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
#include "NoiseOptimization.h"

#ifdef COMPILE_NOISE_WFV_WRAPPER
#include "NoiseWFVWrapper.h"
#endif
#include "NoiseFusion.h"
#include "NoiseSpecializer.h"

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
#include <sstream>

using namespace llvm;

namespace {

Function* GetNoiseFunction(const MDNode* mdNode)
{
    assert (mdNode->getNumOperands() == 2);
    // First operand is the function.
    assert (isa<Function>(mdNode->getOperand(0)));
    return cast<Function>(mdNode->getOperand(0));
}

llvm::MDNode* GetNoiseOptDesc(const MDNode* mdNode)
{
    assert (mdNode->getNumOperands() == 2);
    // Second operand is the noise-optimization metadata.
    assert (isa<llvm::MDNode>(mdNode->getOperand(1)));
    return cast<llvm::MDNode>(mdNode->getOperand(1));
}

MDNode* getCompoundStmtNoiseMD(const BasicBlock& block)
{
  return block.getTerminator()->getMetadata("noise_compound_stmt");
}

const MDNode* getNoiseFunctionAttributeMDN(const Function&    function,
                                           const NamedMDNode& MD)
{
  for (unsigned i=0, e=MD.getNumOperands(); i<e; ++i) {
    const MDNode* functionMDN = MD.getOperand(i);
    const Function* noiseFn = GetNoiseFunction(functionMDN);
    if (noiseFn == &function) return functionMDN;
  }

  return 0;
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
    assert (isa<MDNode>(noiseMD->getOperand(2)));

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

    // Things currently break if there is a return statement inside the region,
    // so we forbid this.
    for (typename SmallPtrSet<BasicBlock*, SetSize>::iterator it=region.begin(),
         E=region.end(); it!=E; ++it)
    {
      if (!isa<ReturnInst>((*it)->getTerminator())) continue;

      errs() << "ERROR: Marked region must not contain a 'return' statement!\n";
      abort();
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

    llvm::Value* params[] = { extractedFn, noiseMD->getOperand(2) };
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
      const bool isTopLevel = !getNoiseFunctionAttributeMDN(F, *MD);
      for (Function::iterator BB = F.begin(), BBE=F.end(); BB!=BBE; ++BB)
      {
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

  SmallVector<std::string, 2> functionNames;
  SmallPtrSet<Function*, 2>   functions;

  explicit NoiseInliner(SmallVector<std::string, 2>* fnNames=0)
  : FunctionPass(ID) {
    initializeNoiseInlinerPass(*PassRegistry::getPassRegistry());
    if (fnNames) functionNames.insert(functionNames.begin(), fnNames->begin(), fnNames->end());
  }

  virtual ~NoiseInliner()
  { }

  virtual bool runOnFunction(Function &F)
  {
    const bool inlineAll = functionNames.empty();

    // Get Functions from input strings (if any).
    Module* mod = F.getParent();
    for (SmallVector<std::string, 2>::iterator it=functionNames.begin(),
         E=functionNames.end(); it!=E; ++it)
    {
      Function* fn = mod->getFunction(*it);
      if (!fn)
      {
        errs() << "ERROR: Function requested for inlining does not exist in module: '"
          << *it << "'!\n";
        abort();
      }

      functions.insert(fn);
    }

    // Collect blocks that belong to the marked region.
    SmallPtrSet<BasicBlock*, 32> functionRegion;
    collectBlocks<32>(&F.front(), &F.back(), functionRegion);

    // For all specified functions, collect all calls within the marked code segment.
    // If no function names were given, collect all calls to any function.
    SmallVector<CallInst*, 32> calls;
    for (SmallPtrSet<BasicBlock*, 32>::iterator it = functionRegion.begin(),
         e = functionRegion.end(); it != e; ++it)
    {
      for(BasicBlock::iterator I=(*it)->begin(), IE=(*it)->end(); I!=IE; ++I)
      {
        if (!isa<CallInst>(I)) continue;
        CallInst* call = cast<CallInst>(I);
        if (!inlineAll && !functions.count(call->getCalledFunction())) continue;
        calls.push_back(call);
      }
    }

    // Inline each of the collected calls.
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

char NoiseExtractor::ID = 0;
char NoiseInliner::ID = 0;
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


namespace llvm {
namespace noise {

// NoiseFnInfo

void NoiseFnInfo::UpdateOptDesc(MDNode* OptDesc)
{
  // according to the description from NoiseOptimization.h
  size_t numOps = OptDesc->getNumOperands();
  for(size_t i = 0; i < numOps; ++i)
    assert( isa<NoiseOptimization>(OptDesc->getOperand(i)) && "invalid noise opt" );

  mOptDesc = OptDesc;
}

NoiseOptimization* NoiseFnInfo::GetOptimization(size_t i) {
  assert( isa<NoiseOptimization>(mOptDesc->getOperand(i)) );
  return cast<NoiseOptimization>(mOptDesc->getOperand(i));
}

size_t NoiseFnInfo::GetNumOptimizations() const {
  return mOptDesc->getNumOperands();
}

void NoiseOptimizations::Instantiate(NoiseOptimization* Opt, PassRegistry* Registry,
                                     FunctionPassManager& Passes)
{
  const StringRef pass = GetPassName(Opt);
  if(pass == "inline") {
    SmallVector<std::string, 2> fnNames;
    for (unsigned i=0, e=NoiseOptimizations::GetNumPassArgs(Opt); i<e; ++i) {
      std::string fnName = NoiseOptimizations::GetPassArgAsString(Opt, i);
      fnNames.push_back(fnName);
    }
    Passes.add(new NoiseInliner(&fnNames));
  } else if(pass == "unroll") {
    const int count = NoiseOptimizations::HasPassArg(Opt, 0U) ?
      NoiseOptimizations::GetPassArgAsInt(Opt, 0U) : -1;

    outs() << "Running pass: indvars\n";
    outs() << "Running pass: loop-rotate\n";

    Passes.add(createIndVarSimplifyPass()); // TODO: Shouldn't this be left to the user?
    Passes.add(createLoopRotatePass()); // TODO: Shouldn't this be left to the user?
    Passes.add(createLoopUnrollPass(-1, count, false));
  } else if(pass == "opt") {
    PassManagerBuilder builder;
    // use 2 instead of 3 in order to avoid the creation of passes which
    // are incompatible with our pass setup
    // during (the invocation of the populateModulePassManager method)
    builder.OptLevel = 2U;
    builder.SizeLevel = 0U;
    builder.DisableUnitAtATime = true;
    builder.populateFunctionPassManager(Passes);
    builder.populateModulePassManager(Passes);
  } else if(pass == "specialize") {
    // pass = "specialize(x,0,1,13)"

    assert (NoiseOptimizations::GetNumPassArgs(Opt) > 1 &&
            "expected at least two arguments for specialized dispatching!");
    const std::string variable = NoiseOptimizations::GetPassArgAsString(Opt, 0U);
    SmallVector<int, 4>* values = new SmallVector<int, 4>();
    for (unsigned i=1, e=NoiseOptimizations::GetNumPassArgs(Opt); i<e; ++i) {
      values->push_back(NoiseOptimizations::GetPassArgAsInt(Opt, i));
    }

    Passes.add(new NoiseSpecializer(variable, values));
  } else if(pass == "wfv" || pass == "wfv-vectorize") {
#ifndef COMPILE_NOISE_WFV_WRAPPER
    errs() << "ERROR: No support for WFV is available!\n";
    abort();
#else
    outs() << "Running pass: loop-simplify\n";
    outs() << "Running pass: lowerswitch\n";
    outs() << "Running pass: indvars\n";
    outs() << "Running pass: lcssa\n";

    // Add preparatory passes for WFV.
    Passes.add(createLoopSimplifyPass());
    Passes.add(createLowerSwitchPass());
    // Add induction variable simplification pass.
    Passes.add(createIndVarSimplifyPass());
    // Convert to loop-closed SSA form to simplify applicability analysis.
    Passes.add(createLCSSAPass());

    // WFV may receive argument to specify vectorization width, whether to
    // use AVX and whether to use the divergence analysis.
    // "wfv-vectorize"          -> width 4, do not use avx, use divergence analysis (default)
    // "wfv-vectorize (4,0,1)"  -> width 4, do not use avx, use divergence analysis (default)
    // "wfv-vectorize (8,1,1)"  -> width 8, use avx, use divergence analysis
    // "wfv-vectorize (8,1)"    -> width 8, use avx, use divergence analysis
    // "wfv-vectorize (16,0,0)" -> width 16, do not use avx, do not use divergence analysis
    unsigned   vectorizationWidth = NoiseOptimizations::HasPassArg(Opt, 0U) ?
        (unsigned)NoiseOptimizations::GetPassArgAsInt(Opt, 0U) : 4U;
    bool       useAVX = NoiseOptimizations::HasPassArg(Opt, 1U) &&
        NoiseOptimizations::GetPassArgAsInt(Opt, 1U);
    bool       useDivergenceAnalysis = NoiseOptimizations::HasPassArg(Opt, 2U) ?
        NoiseOptimizations::GetPassArgAsInt(Opt, 2U) : true;
    const bool verbose = false;

    // Add WFV pass wrapper.
    Passes.add(new NoiseWFVWrapper(vectorizationWidth,
                                   useAVX,
                                   useDivergenceAnalysis,
                                   verbose));
#endif
  } else if(pass == "loop-fusion") {
    Passes.add(createLoopSimplifyPass());
    Passes.add(new NoiseFusion());
  } else {
    const PassInfo* info = Registry->getPassInfo(pass);
    if(!info) {
      errs() << "ERROR: Pass not found: " << pass << "\n";
      abort();
    }
    Pass* pass = info->createPass();
    if(info->isAnalysis())
      Passes.add(pass);
    else
    {
      switch(pass->getPassKind()) {
        case PT_BasicBlock:
        case PT_Function:
        case PT_Loop:
        case PT_Region:
          Passes.add(pass);
          break;
        default:
          errs() << "ERROR: \"" << pass->getPassName() << "\" (" << GetPassName(Opt) << ") is not a function pass\n";
          abort();
      }
    }
  }
  outs() << "Running pass: " << GetPassName(Opt) << "\n";
}

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

namespace {

Function* createDummyFunction(Function* noiseFn)
{
    assert (noiseFn);
    Module* mod = noiseFn->getParent();
    LLVMContext& context = mod->getContext();

    // Create dummy block.
    BasicBlock* entryBB = BasicBlock::Create(context, "");

    SmallVector<Value*, 4> values;
    for (Function::iterator BB=noiseFn->begin(), BBE=noiseFn->end(); BB!=BBE; ++BB)
    {
      for (BasicBlock::iterator I=BB->begin(), IE=BB->end(); I!=IE; ++I)
      {
        // Handle global values.
        for (Instruction::op_iterator O=I->op_begin(), OE=I->op_end(); O!=OE; ++O)
        {
          Value* opVal = cast<Value>(*O);
          if (isa<Function>(opVal)) continue;
          if (isa<BasicBlock>(opVal)) continue;

          if (isa<GlobalValue>(opVal))
          {
            values.push_back(opVal);
          }

          if (!isa<ConstantExpr>(opVal)) continue;
          ConstantExpr* ce = cast<ConstantExpr>(opVal);

          for (ConstantExpr::op_iterator O2=ce->op_begin(), OE2=ce->op_end(); O2!=OE2; ++O2)
          {
            Value* opVal2 = cast<Value>(*O2);
            if (!isa<GlobalValue>(opVal2)) continue;
            values.push_back(opVal2);
          }
        }

        // Handle calls to other functions.
        if (!isa<CallInst>(I)) continue;

        CallInst* call = cast<CallInst>(I);

        Function* callee = call->getCalledFunction();
        if (!callee) continue;

        // Create dummy arguments.
        SmallVector<Value*, 2> args;
        for (unsigned i=0, e=call->getNumArgOperands(); i<e; ++i)
        {
          Value* oldArg = call->getArgOperand(i);
          args.push_back(UndefValue::get(oldArg->getType()));
        }

        // Create dummy call.
        CallInst* dummyCall = CallInst::Create(callee, args, "", entryBB);
        if (!dummyCall->getType()->isVoidTy()) values.push_back(dummyCall);
      }
    }

    if (entryBB->empty()) return NULL;

    // Create dummy function with one parameter per dummy value.
    SmallVector<Type*, 4> argTypes;
    for (SmallVector<Value*, 4>::iterator it=values.begin(), E=values.end(); it!=E; ++it)
    {
        Type* argType = (*it)->getType();
        assert (!argType->isVoidTy());
        argTypes.push_back(PointerType::getUnqual(argType));
    }

    FunctionType* type = FunctionType::get(Type::getVoidTy(context), argTypes, false);

    Function* dummyFn = Function::Create(type, GlobalValue::ExternalLinkage, "dummy", mod);

    // Add the entry block to the function.
    dummyFn->getBasicBlockList().push_back(entryBB);

    // Create a store operation for each value to prevent deletion of the load.
    Function::arg_iterator A = dummyFn->arg_begin();
    for (SmallVector<Value*, 4>::iterator it=values.begin(), E=values.end(); it!=E; ++it, ++A)
    {
        Value* value = *it;
        Value* ptr   = A;
        assert (!value->getType()->isVoidTy());
        new StoreInst(value, ptr, false, entryBB);
    }

    // Finally, create a return instruction to finish the block and function.
    ReturnInst::Create(context, entryBB);

    return dummyFn;
}


void createDummyVarNameCalls(Module*            module,
                             const NamedMDNode& MD)
{
  // Handle noise specialize attributes.
  for (Module::iterator F=module->begin(), FE=module->end(); F!=FE; ++F)
  {
    // First, find out for which variables per function we have to generate
    // dummy function calls.
    SmallSet<std::string, 2> specializeVarNames;

    // Check noise strings from function metadata for passes that need a variable name.
    const MDNode* noiseFnAttrMDN = getNoiseFunctionAttributeMDN(*F, MD);
    if (noiseFnAttrMDN)
    {
      MDNode* noiseDescStrs = cast<MDNode>(noiseFnAttrMDN->getOperand(1)); // 0 = function, 1 = desc strings
      for (unsigned i=0, e=noiseDescStrs->getNumOperands(); i<e; ++i)
      {
        NoiseOptimization* noiseOpt = cast<MDNode>(noiseDescStrs->getOperand(i));
        if (NoiseOptimizations::GetPassName(noiseOpt) != "specialize") continue;
        StringRef passArg = NoiseOptimizations::GetPassArgAsString(noiseOpt, 0);
        specializeVarNames.insert(passArg.str());
      }
    }

    // Check noise strings from compound metadata for passes that need a variable name.
    bool hasNoiseCmp = false;
    for (Function::const_iterator BB = F->begin(), BBE=F->end(); BB!=BBE; ++BB)
    {
      MDNode* noiseMD = getCompoundStmtNoiseMD(*BB);
      if (!noiseMD) continue;
      hasNoiseCmp = true;
      MDNode* noiseDescStrs = cast<MDNode>(noiseMD->getOperand(2)); // 0 = entry, 1 = exit, 2 = desc strings
      for (unsigned i=0, e=noiseDescStrs->getNumOperands(); i<e; ++i)
      {
        NoiseOptimization* noiseOpt = cast<MDNode>(noiseDescStrs->getOperand(i));
        if (NoiseOptimizations::GetPassName(noiseOpt) != "specialize") continue;
        StringRef passArg = NoiseOptimizations::GetPassArgAsString(noiseOpt, 0);
        specializeVarNames.insert(passArg.str());
      }
    }

    // If there was no noise metadata, skip this function.
    if (!noiseFnAttrMDN && !hasNoiseCmp) continue;

    // Generate dummy calls to retain variable name mapping after SROA.
    for (Function::iterator BB=F->begin(), BBE=F->end(); BB!=BBE; ++BB)
    {
      for (BasicBlock::iterator I=BB->begin(), IE=BB->end(); I!=IE; ++I)
      {
        if (!isa<AllocaInst>(I)) continue;
        if (!I->hasMetadata()) continue;

        MDNode* noiseVarNameMD = I->getMetadata("noise_varname");
        if (!noiseVarNameMD) continue;

        assert (noiseVarNameMD->getNumOperands() == 1);
        assert (isa<MDString>(noiseVarNameMD->getOperand(0)));
        MDString* varNameMDS = cast<MDString>(noiseVarNameMD->getOperand(0));
        std::string varName = varNameMDS->getString().str();

        if (!specializeVarNames.count(varName)) continue;

        std::stringstream sstr;
        sstr << "__noise_specialize_" << varName;
        const std::string& specializeFnName = sstr.str();

        assert (!module->getFunction(specializeFnName) &&
                "specialization of multiple variables of same name not implemented!");

        Type* type = I->getType();
        FunctionType* fType = FunctionType::get(type->getPointerElementType(),
                                                type->getPointerElementType(),
                                                false);

        Function* dummyFn = Function::Create(fType,
                                             Function::ExternalLinkage,
                                             specializeFnName,
                                             module);
        dummyFn->setDoesNotAccessMemory();
        dummyFn->setDoesNotThrow();

        DominatorTree domTree;
        domTree.runOnFunction(*F);
        StoreInst* firstStore = 0;
        Value* specializedVal = 0;
        BasicBlock* curBlock = 0;
        for(Value::use_iterator it = I->use_begin(), e = I->use_end(); it != e; ++it)
        {
          if(!isa<StoreInst>(*it)) continue;
          StoreInst* storeI = cast<StoreInst>(*it);
          BasicBlock* instBlock = storeI->getParent();
          if(curBlock == 0 || domTree.dominates(instBlock, curBlock))
            curBlock = instBlock;
          else if(domTree.dominates(curBlock, instBlock))
            continue;
          else
          {
            // reset block as this block cannot contain the first store
            curBlock = 0;
          }

          // remember store values
          assert (storeI->getPointerOperand() == I);
          firstStore = storeI;
          specializedVal = storeI->getValueOperand();
        }
        assert (curBlock && "cannot find unique use of specialized variable");
        assert (specializedVal);

        CallInst* call = CallInst::Create(dummyFn,
                                          ArrayRef<Value*>(specializedVal),
                                          "specializeCall", I);
        I->moveBefore(call);
        call->setDoesNotAccessMemory();
        call->setDoesNotThrow();

        // In the first reachable use of I that is a store,
        // replace the operand by our call.
        firstStore->setOperand(0, call);

        // TODO: check for related code that has to be moved out of the noise region
      }
    }
  }
}

} // unnamed namespace

// TODO: Support "negative" noise attributes (e.g. "subtraction" of specified
//       passes from O3).
void NoiseOptimizer::PerformOptimization()
{
  // Initialize all passes linked into all libraries (see InitializePasses.h).
  // This way, they are registered so we can add them via getPassInfo().
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

  PrettyStackTraceString CrashInfo("NOISE: Optimizing functions");

  // Before transforming to SROA, create dummy calls for phases like
  // specialize that need to have a mapping of variable names to SSA
  // values.
  createDummyVarNameCalls(Mod, *MD);

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

    nfi->UpdateOptDesc(GetNoiseOptDesc(functionMDN));
    assert (nfi->mOptDesc);

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
    NoiseFnInfo* nfi     = noiseFnInfoVec[i];
    Function*    noiseFn = nfi->mReinline ? nfi->mOrigFn : nfi->mMovedFn;

    assert (!nfi->mReinline || !nfi->mMovedFn);

    // Remove exactly the blocks and instructions that we introduced in CGNoise.cpp.
    // NOTE: Using CFG simplification instead makes problems with WFV (or any other loop optimization).
    //       Bug #1377 shows an example where this results in an if-statement at
    //       the end of the loop body getting converted into 2 back edges. The
    //       following loop simplification then creates two nested loops, resulting
    //       in WFV not being able to find a canonical induction variable anymore.
    SmallVector<BasicBlock*, 2> eraseVec;
    for (Function::iterator BB=noiseFn->begin(), BBE=noiseFn->end(); BB!=BBE; ++BB)
    {
      TerminatorInst* ti = BB->getTerminator();
      if (!getCompoundStmtNoiseMD(*BB) && !ti->getMetadata("noise_tmp_block")) continue;
      if (BB->getInstList().size() != 1) continue;
      assert (ti->getNumSuccessors() == 1 && "expected noise tmp block to have exactly one successor!");

      for (pred_iterator P=pred_begin(BB), PE=pred_end(BB); P!=PE; ++P)
      {
        BasicBlock* predBB = *P;
        BasicBlock* succBB = ti->getSuccessor(0);
        TerminatorInst* predTI = predBB->getTerminator();

        for (unsigned i=0, e=predTI->getNumSuccessors(); i<e; ++i)
        {
          if (predTI->getSuccessor(i) != BB) continue;
          predTI->setSuccessor(i, succBB);
        }
      }

      eraseVec.push_back(BB);
    }
    for (SmallVector<BasicBlock*, 2>::iterator it=eraseVec.begin(),
         E=eraseVec.end(); it!=E; ++it)
    {
      (*it)->eraseFromParent();
    }

    // Display all available passes.
    //NoisePassListener list;
    //Registry->enumerateWith(&list);
    outs() << "Running noise optimizations on function '"
      << noiseFn->getName() << "': \n";

    // Run requested noise passes.
    FunctionPassManager NoisePasses(Mod);
    NoisePasses.add(new DataLayout(Mod));

    for(size_t i = 0, e = nfi->GetNumOptimizations(); i < e; ++i) {
      NoiseOptimization* noiseOpt = nfi->GetOptimization(i);
      NoiseOptimizations::Instantiate(noiseOpt, Registry, NoisePasses);
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

    // Before we move the function, we have to create a dummy that calls
    // all functions that are also called in the current noise function.
    // This is to prevent their deletion during the standard optimizations.
    Function* dummyFn = createDummyFunction(noiseFn);
    if (dummyFn) dummyFnVec.push_back(dummyFn);

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
  assert (MD->getNumOperands() != 0);

  PrettyStackTraceString CrashInfo("NOISE: reassemble module after optimizations");

  for (SmallVector<Function*, 4>::iterator it=dummyFnVec.begin(),
       E=dummyFnVec.end(); it!=E; ++it)
  {
    (*it)->eraseFromParent();
  }

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
    if (!nfi->mCall) continue;

    // We have multiple options here.
    // 1) We mark the parent function as "noinline" after the noise function
    // was extracted to NoiseMod. This way, the standard optimizer would not
    // inline it, preventing cases where we have more than one call.
    // 2) If we don't mark it as "noinline", the parent function will often be
    // inlined because most of the code was extracted. Thus, we could inline
    // *all* calls to the function here, which could possibly result in too much
    // code being inlined. Thus, we should let the inliner decide whether to
    // inline or not, and possibly leave the new function in the module.
    // This in turn could be confusing to the user, because the originally
    // written function was inlined, but a new one is called.
    // 3) Mark as "noinline", inline the (then only) call back into the original
    // function, then run the standard inliner again on that one.

    // If mCall is set, inline the call to this function.
    // Caution: as the original call might be inlined, we have to check all uses
    // and NOT the stored one (as it might be invalid right now).
    // Furthermore, there may be additional calls (see comment above).
    // For now, we don't care and simply attempt to inline all calls (option 2).
    SmallVector<CallInst*, 2> callVec;
    for (Function::use_iterator U=movedNoiseFn->use_begin(),
         UE=movedNoiseFn->use_end(); U!=UE; ++U)
    {
      if (!isa<CallInst>(*U)) continue;
      callVec.push_back(cast<CallInst>(*U));
    }
    for (SmallVector<CallInst*, 2>::iterator it=callVec.begin(),
         E=callVec.end(); it!=E; ++it)
    {
      InlineFunctionInfo IFI;
      InlineFunction(*it, IFI);
    }

    // Remove the now inlined noise function again.
    if (movedNoiseFn->use_empty())
    {
      movedNoiseFn->eraseFromParent();
    }

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
  outs() << "\nmodule after noise: " << *Mod;
}

}
}
