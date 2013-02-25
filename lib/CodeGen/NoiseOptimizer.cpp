//===--- NoiseOptimizer.cpp - Noise Optimizations --------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// The optimizer for noise functions
//
//===----------------------------------------------------------------------===//

#include "NoiseOptimizer.h"
#include "CGNoise.h"

#ifdef COMPILE_NOISE_WFV_WRAPPER
#include "NoiseWFVWrapper.h"
#endif

#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/PassRegistry.h"
#include "llvm/PassManagers.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Assembly/PrintModulePass.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/CodeGen/RegAllocRegistry.h"
#include "llvm/CodeGen/SchedulerRegistry.h"
#include "llvm/MC/SubtargetFeature.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/Timer.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/Transforms/Utils/Cloning.h" // CloneFunction()
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h" // FunctionType
#include "llvm/IR/Constants.h" // UndefValue
#include "llvm/IR/Instructions.h" // CallInst

#include <iostream>

using namespace llvm;

namespace {

Function* GetNoiseFunction(const MDNode* mdNode)
{
    assert (mdNode->getNumOperands() == 2);
    // First operand is the function.
    assert (isa<Function>(mdNode->getOperand(0)));
    return cast<Function>(mdNode->getOperand(0));
}

MDString* GetNoiseString(const MDNode* mdNode)
{
    assert (mdNode->getNumOperands() == 2);
    // Second operand is a string with the noise optimizations.
    assert (isa<MDString>(mdNode->getOperand(1)));
    return cast<MDString>(mdNode->getOperand(1));
}

} // unnamed namespace

namespace llvm {

// Collects all blocks between the block "block" and the end block "endBB"
// TODO: There's functionality inside LLVM for this: llvm::Region
template<unsigned SetSize>
void collectBlocks(BasicBlock* block,
                   BasicBlock* endBB,
                   SmallPtrSet<BasicBlock*, SetSize>& region)
{
  if (region.count(block)) return;
  region.insert(block);

  if (block == endBB) return;

  TerminatorInst* terminator = block->getTerminator();
  for (unsigned i=0, e=terminator->getNumSuccessors(); i<e; ++i)
  {
    collectBlocks<SetSize>(terminator->getSuccessor(i), endBB, region);
  }
}

void initializeNoiseExtractorPass(PassRegistry&);
void initializeNoiseInlinerPass(PassRegistry&);
void initializeNoiseSpecializerPass(PassRegistry&);

struct NoiseExtractor : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid

  noise::NoiseFnInfoVecType* noiseFnInfoVec;
  NamedMDNode*               MD;
  SmallSet<Function*, 64>    createdFunctions;
  Module*                    Mod;
  LLVMContext*               Context;

  NoiseExtractor(noise::NoiseFnInfoVecType* noiseFuncInfoVec=0,
                 NamedMDNode*               mdNode=0)
  : FunctionPass(ID), noiseFnInfoVec(noiseFuncInfoVec), MD(mdNode) {
    initializeNoiseExtractorPass(*PassRegistry::getPassRegistry());
  }

  virtual ~NoiseExtractor()
  { }

  MDNode* getCompoundStmtNoiseMD(const BasicBlock& block)
  {
      return block.getTerminator()->getMetadata("noise_compound_stmt");
  }

  bool hasNoiseFunctionAttribute(const Function& function) const {
    for (unsigned i=0, e=MD->getNumOperands(); i<e; ++i) {
      MDNode* functionMDN = MD->getOperand(i);
      Function* noiseFn = GetNoiseFunction(functionMDN);
      if (noiseFn == &function) return true;
    }

    return false;
  }

  template<unsigned SetSize>
  bool resolveMarkers(BasicBlock*                        block,
                      SmallPtrSet<BasicBlock*, SetSize>& visitedBlocks,
                      const bool                         isTopLevel)
  {
    if (visitedBlocks.count(block)) return false;
    visitedBlocks.insert(block);

    MDNode* noiseMD = getCompoundStmtNoiseMD(*block);
    if (!noiseMD) return false;

    // Handle compound statement attributes.
    assert (isa<BasicBlock>(noiseMD->getOperand(0)));
    assert (isa<BasicBlock>(noiseMD->getOperand(1)));
    assert (isa<MDString>(noiseMD->getOperand(2)));

    // Recurse into nested noise regions (if any).
    // To do so properly, we need to reconstruct the region after we
    // extracted a noise region and then start iterating again.
    BasicBlock* entryBB = cast<BasicBlock>(noiseMD->getOperand(0));
    BasicBlock* exitBB  = cast<BasicBlock>(noiseMD->getOperand(1));

    SmallPtrSet<BasicBlock*, SetSize> region;
    bool iterate = true;
    while (iterate)
    {
        iterate = false;
        region.clear();
        collectBlocks<SetSize>(entryBB, exitBB, region);

        for (typename SmallPtrSet<BasicBlock*, SetSize>::iterator it=region.begin(),
            E=region.end(); it!=E; ++it)
        {
            if (resolveMarkers<SetSize>(*it, visitedBlocks, false))
            {
                iterate = true;
                break;
            }
        }
    }

    // Create new function from the marked range.
    SmallVector<BasicBlock*, SetSize> regionVec(region.begin(), region.end());
    CodeExtractor extractor(regionVec);
    Function* extractedFn = extractor.extractCodeRegion();
    extractedFn->setName(extractedFn->getName()+".extracted");

    // Create new NoiseFnInfo object.
    assert (extractedFn->getNumUses() == 1 &&
            "There should be only one call to an extracted function");
    assert (isa<CallInst>(*extractedFn->use_begin()));
    CallInst* call = cast<CallInst>(*extractedFn->use_begin());
    noise::NoiseFnInfo* nfi = new noise::NoiseFnInfo(extractedFn, call, !isTopLevel);
    noiseFnInfoVec->push_back(nfi);

    //outs() << "extracted function: " << *extractedFn << "\n";
    //outs() << "source function: " << *call->getParent()->getParent() << "\n";

    // Create global (function) metadata for the new function from the statement attribute.
    assert(Mod);
    MDString* noiseMDS = cast<MDString>(noiseMD->getOperand(2));
    llvm::StringRef noiseStr = noiseMDS->getString();

    llvm::Value* params[] = { extractedFn, llvm::MDString::get(*Context, noiseStr) };
    MD->addOperand(llvm::MDNode::get(*Context, llvm::ArrayRef<llvm::Value*>(params)));

    createdFunctions.insert(extractedFn);

    return true;
  }

  virtual bool runOnFunction(Function &F)
  {
    // If this was an extracted function, skip the extraction operation.
    if(createdFunctions.count(&F))
      return false;

    Mod = F.getParent();
    Context = &F.getContext();

    // Test each block of the function for a noise marker and extract
    // the corresponding region.
    // We extract nested regions exactly in the order that we apply
    // the optimizations and re-inlining later. Thus, we have to recurse
    // *before* extracting a region.
    // To do this properly, we need to reconstruct the region after we
    // extracted a noise region and then start iterating again.
    SmallPtrSet<BasicBlock*, 32> visitedBlocks;
    bool iterate = true;
    while (iterate)
    {
      iterate = false;
      for (Function::iterator BB = F.begin(), BBE=F.end(); BB!=BBE; ++BB)
      {
        const bool isTopLevel = !hasNoiseFunctionAttribute(*BB->getParent());
        if (resolveMarkers(BB, visitedBlocks, isTopLevel))
        {
          iterate = true;
          break;
        }
      }
    }

    return true;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
  }
};

// This custom inlining pass is required since the built-in functionality
// cannot inline functions which are in different modules
// TODO: This should not be necessary anymore.
struct NoiseInliner : public FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid

  explicit NoiseInliner()
  : FunctionPass(ID) {
    initializeNoiseInlinerPass(*PassRegistry::getPassRegistry());
  }

  virtual ~NoiseInliner()
  { }

  virtual bool runOnFunction(Function &F)
  {
    // Collect all blocks which belong to the function.
    SmallPtrSet<BasicBlock*, 32> functionRegion;
    collectBlocks<32>(&F.front(), &F.back(), functionRegion);
    // Loop over the collected blocks and find all interesting call instructions
    SmallVector<CallInst*, 32> calls;
    for (SmallPtrSet<BasicBlock*, 32>::iterator it = functionRegion.begin(),
         e = functionRegion.end(); it != e; ++it)
    {
      for(BasicBlock::iterator bit = (*it)->begin(), e = (*it)->end(); bit != e; ++bit)
      {
        if(!isa<CallInst>(*bit))
          continue;
        calls.push_back(&cast<CallInst>(*bit));
      }
    }
    // inline each call
    for(SmallVector<CallInst*, 32>::iterator it = calls.begin(),
        e = calls.end(); it != e; ++it)
    {
      InlineFunctionInfo IFI;
      InlineFunction(*it, IFI);
    }

    return true;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
  }
};

struct NoiseSpecializer : public FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid

  const StringRef            mVariable;
  const SmallVector<int, 4>* mValues;

  explicit NoiseSpecializer() : FunctionPass(ID), mVariable(""), mValues(0)
  {
    assert (false && "empty constructor must never be called!");
    initializeNoiseSpecializerPass(*PassRegistry::getPassRegistry());
  }

  NoiseSpecializer(StringRef&                 variable,
                   const SmallVector<int, 4>& values)
  : FunctionPass(ID), mVariable(variable), mValues(&values)
  {
    initializeNoiseSpecializerPass(*PassRegistry::getPassRegistry());
  }

  virtual ~NoiseSpecializer()
  { }

  virtual bool runOnFunction(Function &F)
  {
    return false;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
  }
};

char NoiseExtractor::ID = 0;
char NoiseInliner::ID = 0;
char NoiseSpecializer::ID = 0;
}

// Pass declarations

INITIALIZE_PASS_BEGIN(NoiseExtractor, "noise-extract",
                      "Extract code blocks into noise functions", false, false)
INITIALIZE_PASS_END(NoiseExtractor, "noise-extract",
                    "Extract code blocks into noise functions", false, false)

INITIALIZE_PASS_BEGIN(NoiseInliner, "noise-inline",
                      "Forces inlining of calls", false, false)
INITIALIZE_PASS_END(NoiseInliner, "noise-inline",
                    "Forces inlining of calls", false, false)

INITIALIZE_PASS_BEGIN(NoiseSpecializer, "noise-specialize",
                      "Specializes code for specific values of a variable", false, false)
INITIALIZE_PASS_END(NoiseSpecializer, "noise-specialize",
                    "Specializes code for specific values of a variable", false, false)

namespace llvm {
namespace noise {

// Noise Optimizer

NoiseOptimizer::NoiseOptimizer(llvm::Module *M)
  : Mod(M)
  , NoiseMod(new Module("noiseMod", Mod->getContext()))
  , Registry(PassRegistry::getPassRegistry())
  , MD(Mod->getOrInsertNamedMetadata("noise"))
{ }

NoiseOptimizer::~NoiseOptimizer()
{
  for (NoiseFnInfoVecType::iterator it=noiseFnInfoVec.begin(),
       E=noiseFnInfoVec.end(); it!=E; ++it)
  {
    delete *it;
  }
  delete NoiseMod;
}

struct NoisePassListener : public PassRegistrationListener {

  NoisePassListener() {}

  virtual ~NoisePassListener() {}

  virtual void passRegistered(const PassInfo *) {}

  void enumeratePasses();

  virtual void passEnumerate(const PassInfo * p)
  {
    outs() << p->getPassArgument() << " (" << p->getPassName() << ")\n";
  }
};

// TODO: Support "negative" noise attributes (e.g. "subtraction" of specified
//       passes from O3).
void NoiseOptimizer::PerformOptimization()
{
  PrettyStackTraceString CrashInfo("NOISE: Optimizing functions");

  //outs() << "Module before noise: " << *Mod;

  // Initialize all passes linked into all libraries (see InitializePasses.h).
  // This way, they are registerd so we can add them via getPassInfo().
  initializeCore(*PassRegistry::getPassRegistry());
  initializeTransformUtils(*PassRegistry::getPassRegistry());
  initializeScalarOpts(*PassRegistry::getPassRegistry());
  initializeVectorization(*PassRegistry::getPassRegistry());
  initializeInstCombine(*PassRegistry::getPassRegistry());
  initializeIPO(*PassRegistry::getPassRegistry());
  initializeInstrumentation(*PassRegistry::getPassRegistry());
  initializeAnalysis(*PassRegistry::getPassRegistry());
  initializeIPA(*PassRegistry::getPassRegistry());
  initializeCodeGen(*PassRegistry::getPassRegistry());
  initializeTarget(*PassRegistry::getPassRegistry());

  {
    // Perform some standard optimizations upfront.
    // NOTE: This should not interfere with the user-defined optimizations.
    //       If we don't do this transformation to SSA here (before
    //       extraction), later phases are unable to optimize the extracted
    //       function because of aliasing problems (the generated function
    //       will usually have lots of pointer parameters).
    PassManager PM;
    PM.add(new DataLayout(Mod));
    PM.add(createTypeBasedAliasAnalysisPass());
    PM.add(createBasicAliasAnalysisPass());
    PM.add(createScalarReplAggregatesPass());
    PM.run(*Mod);
  }

  // Extract noise code regions from compound statements into separate functions.
  // These functions look exactly like functions with noise function attribute.
  {
    PassManager PM;
    PM.add(new NoiseExtractor(&noiseFnInfoVec, MD));
    PM.run(*Mod);
  }

  //outs() << "Module after compound noise extraction: " << *Mod;

  // Get the corresponding noise attribute.
  // We cannot just iterate over the metadata since the order of the
  // functions is important (for nested attributes). We have to be able
  // to iterate the extracted functions in that same order.
  for (unsigned i=0, e=MD->getNumOperands(); i<e; ++i) {
    MDNode* functionMDN = MD->getOperand(i);
    Function* noiseFn = GetNoiseFunction(functionMDN);

    NoiseFnInfo* nfi = 0;
    for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i)
    {
      if (noiseFnInfoVec[i]->mOrigFn != noiseFn) continue;
      nfi = noiseFnInfoVec[i];
      break;
    }

    // If the function is not inside noiseFnInfoVec, it was not extracted from code
    // but corresponds to a noise function attribute. In this case, there
    // is no NoiseFnInfo object yet.
    if (!nfi)
    {
      nfi = new NoiseFnInfo(noiseFn);
      noiseFnInfoVec.push_back(nfi);
    }

    nfi->mOptString = GetNoiseString(functionMDN);
    assert (nfi->mOptString);

    // Make sure that no other optimizations than the requested ones are
    // executed on that function.
    // To this end, we clone "top level" functions (all others are inlined
    // after noise optimizations anyway) and delete the body of the original
    // function.
    // This way, there is no connection between the original code and the
    // noise function, so the rest of the original code can still be optimized
    // normally without affecting the noise part.
    if (nfi->mReinline) continue;

    ValueToValueMapTy valueMap;
    Function* movedNoiseFn = CloneFunction(noiseFn, valueMap, false);
    movedNoiseFn->setName(noiseFn->getName()+".noise");
    nfi->mMovedFn = movedNoiseFn;
    Mod->getFunctionList().push_back(movedNoiseFn);

    // Update NoiseFnInfo objects that have their mCall member point into
    // the moved function, and thus, have to be updated to the new function.
    // Otherwise, we can not inline the functions back in order.
    for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i)
    {
      NoiseFnInfo* nfi = noiseFnInfoVec[i];
      if (!nfi->mCall) continue;
      if (nfi->mCall->getParent()->getParent() != noiseFn) continue;
      nfi->mCall = cast<CallInst>(valueMap[nfi->mCall]);
    }

    // Make the old function an external declaration so the rest of the
    // code is still valid and can be optimized.
    noiseFn->deleteBody();
  }

  // Now optimize each function separately (execute the requested passes) and
  // inline functions from nested noise attributes again.
  // NOTE: We must not inline functions that were created from "top-level"
  //       noise attributes, since this code then would be optimized with all
  //       other optimizations again.
  // NOTE: The module vector obeys the correct nesting order, so we first
  //       optimize the innermost code blocks, inline them, and then continue
  //       with the parents.
  for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i)
  {
    NoiseFnInfo* nfi   = noiseFnInfoVec[i];
    Function* noiseFn  = nfi->mReinline ? nfi->mOrigFn : nfi->mMovedFn;
    StringRef str      = nfi->mOptString->getString();

    assert (!nfi->mReinline || !nfi->mMovedFn);

    // Display all available passes.
    //NoisePassListener list;
    //Registry->enumerateWith(&list);
    outs() << "Running noise optimizations on function '"
      << noiseFn->getName() << "': " << str << "\n";

    // Run requested noise passes.
    FunctionPassManager NoisePasses(Mod);
    NoisePasses.add(new DataLayout(Mod));

    // Run CFG simplification upfront to remove the blocks we introduced
    // ourselves.
    // TODO: Replace this by some simple code that only removes *exactly* the
    //       blocks and instructions we introduced so the user is not confused.
    NoisePasses.add(createCFGSimplificationPass());

    // Parse attributes.
    for(std::pair<StringRef, StringRef> opts = str.split(' ');
        opts.first.size() > 0;
        opts = opts.second.split(' '))
    {
      // resolve current pass description
      const StringRef& pass = opts.first;

      // check for a custom noise "pass description"
      if(pass.startswith("wfv"))
      {
#ifdef COMPILE_NOISE_WFV_WRAPPER
        outs() << "Running pass: loop-simplify\n";
        outs() << "Running pass: lowerswitch\n";
        outs() << "Running pass: indvars\n";
        outs() << "Running pass: lcssa\n";

        // Add preparatory passes for WFV.
        NoisePasses.add(createLoopSimplifyPass());
        NoisePasses.add(createLowerSwitchPass());
        // Add induction variable simplification pass.
        NoisePasses.add(createIndVarSimplifyPass());
        // Convert to loop-closed SSA form to simplify applicability analysis.
        NoisePasses.add(createLCSSAPass());

        // WFV may receive argument to specify vectorization width, whether to
        // use AVX and whether to use the divergence analysis.
        // TODO: If arguments are given, there must not be a space between them!
        // "wfv-vectorize"          -> width 4, do not use avx, use divergence analysis (default)
        // "wfv-vectorize (4,0,1)"  -> width 4, do not use avx, use divergence analysis (default)
        // "wfv-vectorize (8,1,1)"  -> width 8, use avx, use divergence analysis
        // "wfv-vectorize (8,1)"    -> width 8, use avx, use divergence analysis
        // "wfv-vectorize (16,0,0)" -> width 16, do not use avx, do not use divergence analysis
        unsigned   vectorizationWidth = 4;
        bool       useAVX = false;
        bool       useDivergenceAnalysis = true;
        const bool verbose = false;

        const size_t openParen = pass.find('(', 0);
        const size_t closeParen = pass.find(')', 0);
        if (closeParen > openParen)
        {
          StringRef args = pass.substr(openParen + 1, (closeParen - openParen) - 1);

          unsigned numArgs = 0;
          for(std::pair<StringRef, StringRef> split = args.split(',');
              split.first.size() > 0;
              split = split.second.split(','), ++numArgs)
          {
            if (numArgs == 3)
            {
              errs() << "WARNING: WFV may only receive up to three parameters, "
                << "ignoring additional ones!\n";
              break;
            }

            // Get the current argument.
            StringRef arg = split.first;
            const size_t comma = arg.find(',', 0);
            if (comma != arg.npos) arg = arg.substr(arg.find(',', 0));

            unsigned val;
            const bool error = arg.getAsInteger(10, val);
            if (error)
            {
              errs() << "WARNING: only unsigned integer arguments allowed as "
                << "WFV parameter "
                << (numArgs == 0 ? "'vectorizationWidth'" :
                    numArgs == 1 ? "'useAVX'" : "'useDivergenceAnalysis'")
                << ", found: '" << arg << "'. Falling back "
                << "to default ("
                << (numArgs == 0 ? "4" : numArgs == 1 ? "false" : "true")
                << ").\n";
              continue;
            }
            if (numArgs == 0) vectorizationWidth = val;
            else if (numArgs == 1) useAVX = val;
            else if (numArgs == 2) useDivergenceAnalysis = val;
          }
        }

        // Add WFV pass wrapper.
        NoisePasses.add(new NoiseWFVWrapper(vectorizationWidth,
                                            useAVX,
                                            useDivergenceAnalysis,
                                            verbose));
#else
        outs() << "No support for WFV is available\n";
        continue;
#endif
      }
      else if(pass.startswith("inline"))
      {
        // force inlining of function calls
        NoisePasses.add(new NoiseInliner());
      }
      else if(pass.startswith("unroll"))
      {
        // loop unrolling requested
        int count = -1;
        // => check for additional arguments
        const size_t openParen = pass.find('(', 0);
        const size_t closeParen = pass.find(')', 0);
        if (closeParen > openParen)
        {
          // get the number of arguments
          StringRef args = pass.substr(openParen + 1, (closeParen - openParen) - 1);
          count = atoi(args.str().c_str()); // TODO: Use getAsInteger() (see below).
        }

        outs() << "Running pass: indvars\n";
        outs() << "Running pass: loop-rotate\n";

        NoisePasses.add(createIndVarSimplifyPass()); // TODO: Shouldn't this be left to the user?
        NoisePasses.add(createLoopRotatePass()); // TODO: Shouldn't this be left to the user?
        NoisePasses.add(createLoopUnrollPass(-1, count, false));
      }
      else if (pass.startswith("specialize"))
      {
        // pass = "specialize(x=1,2,3)"
        // TODO: If arguments are given, there must not be a space between them!

        // Check for additional arguments.
        const size_t openParen = pass.find('(', 0);
        const size_t closeParen = pass.find(')', 0);
        if (openParen >= closeParen ||
            openParen == pass.npos ||
            closeParen == pass.npos)
        {
          errs() << "ERROR: 'specialize' requires additional parameters!\n";
          continue;
        }

        // args = "x=1,2,3"
        StringRef args = pass.substr(openParen + 1, (closeParen - openParen) - 1);
        assert (!args.empty());

        // Get the variable to specialize.
        std::pair<StringRef, StringRef> splitPair = args.split("=");
        if (splitPair.second.empty())
        {
          errs() << "ERROR: expected at least two arguments separated by a blank.\n";
          continue;
        }
        // variable = "x", args = "1,2,3"
        StringRef variable = splitPair.first;
        args = splitPair.second;

        // Get the values to specialize for.
        SmallVector<int, 4> values;
        for(std::pair<StringRef, StringRef> split = args.split(',');
                split.first.size() > 0;
                split = split.second.split(','))
        {
          StringRef& arg = split.first;
          const size_t comma = arg.find(',', 0);
          if (comma != arg.npos) arg = arg.substr(arg.find(',', 0));

          int val;
          const bool error = arg.getAsInteger(10, val);
          if (error)
          {
            errs() << "\nERROR: only integer arguments allowed after variable,"
              << " found: " << arg << "\n";
            continue;
          }
          values.push_back(val);
        }

        if (values.empty()) continue;

        NoisePasses.add(new NoiseSpecializer(variable, values));
      }
      else
      {
        // Use the pass registry to resolve the pass.
        const PassInfo* info = Registry->getPassInfo(pass);
        if(!info)
        {
          errs() << "ERROR: Pass not found: " << pass << "\n";
          continue;
        }
        // use the resolved LLVM pass
        NoisePasses.add(info->createPass());
      }

      outs() << "Running pass: " << pass << "\n";
    }

    // TODO: Remove this when reaching "production" state or so.
    NoisePasses.add(createVerifierPass());

    // Run the required passes
    NoisePasses.run(*noiseFn);

    // If this is a function that was created from a top-level noise attribute,
    // we are done.
    if (!nfi->mReinline) continue;

    // If mCall is not set, this was a noise function attribute.
    // Thus, we must not inline/remove anything.
    if (!nfi->mCall) continue;

    // We want to run some optimizations on the function after inlining,
    // so we have to fetch it from the call before it is gone.
    Function* parentFn = nfi->mCall->getParent()->getParent();

    // Otherwise, inline the only call to this function.
    InlineFunctionInfo IFI;
    InlineFunction(nfi->mCall, IFI);

    // Remove the now inlined noise function again.
    assert (noiseFn->use_empty());
    noiseFn->eraseFromParent();
    nfi->mMovedFn = 0;

    {
      // Perform some standard optimizations after inlining.
      // TODO: This may disturb user experience.
      FunctionPassManager PM(Mod);
      PM.add(new DataLayout(Mod));
      PM.add(createTypeBasedAliasAnalysisPass());
      PM.add(createBasicAliasAnalysisPass());
      PM.add(createCFGSimplificationPass());
      PM.add(createScalarReplAggregatesPass());
      PM.add(createEarlyCSEPass());
      PM.run(*parentFn);
    }

    //outs() << "module after reinlining: " << *Mod << "\n";
  }

  // At this point, all noise functions that were not "top level" are
  // inlined and erased.
  //outs() << "module after passes: " << *Mod << "\n";

  // Finally, move all "top-level" noise functions into a different
  // module and set calls to them to an external declaration. This is to
  // prevent the standard optimizations etc. to run on noise functions.
  // They are reassembled later.
  for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i)
  {
    NoiseFnInfo* nfi      = noiseFnInfoVec[i];
    Function*    noiseFn  = nfi->mMovedFn;

    // If this is no top level function, continue.
    if (!noiseFn) continue;

    assert (!nfi->mReinline && "there should be no non-top level function left!");

    // Move function to noise module.
    noiseFn->removeFromParent();
    assert (!Mod->getFunction(noiseFn->getName()));
    NoiseMod->getFunctionList().push_back(noiseFn);

    // If this is a "function noise" function without use, the original
    // function can be removed by the module optimizations.
    // To ensure that we catch such cases, we have to do two things:
    // - Set the original function to NULL.
    // - Set the name of the moved noise function to the original name
    //   so we don't lose track of it.
    CallInst* call = nfi->mCall;
    if (!call && nfi->mOrigFn->use_empty())
    {
      noiseFn->takeName(nfi->mOrigFn);
      nfi->mOrigFn = 0;
    }

    // Update call to temporarily point to original function again
    // (the external declaration that has not been moved).
    // This is only valid for non-function noise.
    if (call) call->setCalledFunction(nfi->mOrigFn);
  }

  // If we have moved top-level functions that include calls to "compound
  // noise" functions, we also have to move the declarations of those callees.
  // The declarations in question are those that have a use in the NoiseMod.
  for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i)
  {
    NoiseFnInfo* nfi      = noiseFnInfoVec[i];
    Function*    noiseFn  = nfi->mMovedFn;

    // If this is no top level function, continue.
    if (!noiseFn) continue;

    // TODO: What is this?!
  }

  //outs() << "module after outsourcing: " << *Mod << "\n";
  //outs() << "noise module after outsourcing: " << *NoiseMod << "\n";
}

void NoiseOptimizer::Reassemble()
{
  PrettyStackTraceString CrashInfo("NOISE: reassemble module after optimizations");

  for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i) {
    NoiseFnInfo* nfi = noiseFnInfoVec[i];

    if (nfi->mReinline) continue; // Has already been reassembled/inlined.

    Function* movedNoiseFn = nfi->mMovedFn;
    assert (movedNoiseFn);
    assert (movedNoiseFn->getParent() == NoiseMod);

    Function* decl = nfi->mOrigFn;

    if (!decl)
    {
      // This is a "function noise" function without use, so it is likely that
      // it got deleted during the "normal" optimization phase.
      // NOTE: We have to make this query *before* moving the function!
      decl = Mod->getFunction(movedNoiseFn->getName());
    }

    // Move function back to Mod.
    movedNoiseFn->removeFromParent();
    Mod->getFunctionList().push_back(movedNoiseFn);
    assert (movedNoiseFn->getParent() == Mod);

    // If the original function was indeed removed, skip everything else.
    if (!decl) continue;

    assert (Mod == nfi->mOrigFn->getParent());

    // Replace uses of declaration by function.
    decl->replaceAllUsesWith(movedNoiseFn);

    // Make sure the function has the same name again.
    movedNoiseFn->takeName(decl);

    // Remove declaration from TheModule.
    decl->eraseFromParent();

    // If mCall is not set, this was a noise function attribute.
    // Thus, we must not inline/remove anything.
    if (!nfi->mCall) return;

    // Otherwise, inline the only call to this function.
    InlineFunctionInfo IFI;
    InlineFunction(nfi->mCall, IFI);

    // Remove the now inlined noise function again.
    assert (movedNoiseFn->use_empty());
    movedNoiseFn->eraseFromParent();

    //outs() << "module after reinlining: " << *Mod << "\n";

    {
      // Perform some standard optimizations after inlining.
      // TODO: This may disturb user experience.
      PassManager PM;
      PM.add(new DataLayout(Mod));
      PM.add(createTypeBasedAliasAnalysisPass());
      PM.add(createBasicAliasAnalysisPass());
      PM.add(createCFGSimplificationPass());
      PM.add(createScalarReplAggregatesPass());
      PM.add(createEarlyCSEPass());
      PM.run(*Mod);
    }

    //outs() << "module after post inlining std opts: " << *Mod << "\n";
  }
}

void NoiseOptimizer::Finalize()
{
  // Remove noise metadata from TheModule.
  // TODO: Only if we know that there is only noise metadata inside.
  // TODO: If we don't do this, CodeGenPasses->run() fails with an assertion.
  MD->eraseFromParent();
  outs() << "module after noise: " << *Mod;
}

}
}
