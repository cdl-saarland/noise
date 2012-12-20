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

#include "llvm/Module.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/PassRegistry.h"
#include "llvm/PassManagers.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/Dominators.h"
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
#include "llvm/DataLayout.h"
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
#include "llvm/DerivedTypes.h" // FunctionType
#include "llvm/Constants.h" // UndefValue
#include "llvm/Instructions.h" // CallInst

#include <iostream>

using namespace llvm;

namespace llvm {

// Collects all blocks between the block "block" and the end block "endBB"
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
void initializeNoiseUnrollerPass(PassRegistry&);

struct NoiseExtractor : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid

  noise::NoiseFnInfoVecType* noiseFnInfoVec;
  SmallSet<Function*, 64> createdFunctions;
  Module* Mod;
  LLVMContext* Context;
  DominatorTree* DT;

  explicit NoiseExtractor(noise::NoiseFnInfoVecType* noiseFuncInfoVec=0)
  : FunctionPass(ID), noiseFnInfoVec(noiseFuncInfoVec) {
    initializeNoiseExtractorPass(*PassRegistry::getPassRegistry());
  }

  virtual ~NoiseExtractor()
  { }

  MDNode* getCompoundStmtNoiseMD(const BasicBlock& block)
  {
      return block.getTerminator()->getMetadata("noise_compound_stmt");
  }

  template<unsigned SetSize>
  void resolveMarkers(BasicBlock*                        block,
                      SmallPtrSet<BasicBlock*, SetSize>& visitedBlocks,
                      const bool                         isTopLevel)
  {
    if (visitedBlocks.count(block)) return;
    visitedBlocks.insert(block);

    MDNode* noiseMD = getCompoundStmtNoiseMD(*block);
    if (!noiseMD) return;

    // Handle compound statement attributes.
    assert (isa<BasicBlock>(noiseMD->getOperand(0)));
    assert (isa<BasicBlock>(noiseMD->getOperand(1)));
    assert (isa<MDString>(noiseMD->getOperand(2)));

    // Create new function from the marked range.
    BasicBlock* entryBB = cast<BasicBlock>(noiseMD->getOperand(0));
    BasicBlock* exitBB  = cast<BasicBlock>(noiseMD->getOperand(1));

    SmallPtrSet<BasicBlock*, SetSize> region;
    collectBlocks<SetSize>(entryBB, exitBB, region);

    for (typename SmallPtrSet<BasicBlock*, SetSize>::iterator it=region.begin(),
         E=region.end(); it!=E; ++it)
    {
      resolveMarkers<SetSize>(*it, visitedBlocks, false);
    }

    SmallVector<BasicBlock*, SetSize> regionVec(region.begin(), region.end());
    CodeExtractor extractor(regionVec, DT, false);
    Function* extractedFn = extractor.extractCodeRegion();

    // uncomment to see the extracted function
    // outs() << "extracted function: " << *extractedFn << "\n";

    // Create new NoiseFnInfo object.
    assert (extractedFn->getNumUses() == 1 &&
            "There should be only one call to an extracted function");
    assert (isa<CallInst>(*extractedFn->use_begin()));
    CallInst* call = cast<CallInst>(*extractedFn->use_begin());
    noise::NoiseFnInfo* nfi = new noise::NoiseFnInfo(extractedFn, call, !isTopLevel);
    noiseFnInfoVec->push_back(nfi);

    // Create global (function) metadata for the new function from the statement attribute.
    assert(Mod);
    MDString* noiseMDS = cast<MDString>(noiseMD->getOperand(2));
    llvm::StringRef noiseStr = noiseMDS->getString();
    llvm::Value* params[] = { extractedFn,
                              llvm::MDString::get(*Context, "noise"),
                              llvm::MDString::get(*Context, noiseStr) };
    llvm::NamedMDNode* MDN = Mod->getOrInsertModuleFlagsMetadata();
    MDN->addOperand(llvm::MDNode::get(*Context, llvm::ArrayRef<llvm::Value*>(params)));

    createdFunctions.insert(extractedFn);
  }

  virtual bool runOnFunction(Function &F)
  {
    // If this was an extracted function, skip the extraction operation.
    if(createdFunctions.count(&F))
      return false;

    Mod = F.getParent();
    Context = &F.getContext();
    DT = &getAnalysis<DominatorTree>();

    // Collect all blocks which belong to the function.
    SmallPtrSet<BasicBlock*, 32> functionRegion;
    collectBlocks<32>(&F.front(), &F.back(), functionRegion);

    // Iterate over the blocks of the function and resolve all markers.
    // We must not iterate over the function's blocks directly since we are
    // modifying it on the fly.
    SmallPtrSet<BasicBlock*, 32> visitedBlocks;
    for (SmallPtrSet<BasicBlock*, 32>::iterator it = functionRegion.begin(),
         e = functionRegion.end(); it != e; ++it)
    {
      resolveMarkers(*it, visitedBlocks, true);
    }

    return true;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<DominatorTree>();
  }
};

// This custom inlining pass is required since the built-in functionality
// cannot inline functions which are in different modules
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

char NoiseExtractor::ID = 0;
char NoiseInliner::ID = 0;
}

// Pass declarations

INITIALIZE_PASS_BEGIN(NoiseExtractor, "noise-extract",
                      "Extract code blocks into noise functions", false, false)
INITIALIZE_PASS_DEPENDENCY(DominatorTree)
INITIALIZE_PASS_END(NoiseExtractor, "noise-extract",
                    "Extract code blocks into noise functions", false, false)

INITIALIZE_PASS_BEGIN(NoiseInliner, "noise-inline",
                      "Forces inlining of calls", false, false)
INITIALIZE_PASS_END(NoiseInliner, "noise-inline",
                    "Forces inlining of calls", false, false)

namespace llvm {
namespace noise {

// Noise Optimizer

NoiseOptimizer::NoiseOptimizer(llvm::Module *M)
  : Mod(M)
  , Registry(PassRegistry::getPassRegistry())
  , MD(Mod->getOrInsertModuleFlagsMetadata())
{ }

NoiseOptimizer::~NoiseOptimizer()
{
  for (NoiseFnInfoVecType::iterator it=noiseFnInfoVec.begin(),
       E=noiseFnInfoVec.end(); it!=E; ++it)
  {
    delete *it;
  }
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
  LLVMContext& context = Mod->getContext();

  //outs() << "Module before std opts: " << *Mod;

  {
    // Perform some standard optimizations upfront.
    // This is to prevent pointer aliasing in the extracted functions.
    PassManager PM;
    PM.add(new DataLayout(Mod));
    PM.add(createTypeBasedAliasAnalysisPass());
    PM.add(createBasicAliasAnalysisPass());
    //PM.add(createCFGSimplificationPass()); // Removes noise attribute.
    PM.add(createScalarReplAggregatesPass());
    PM.add(createEarlyCSEPass());
    PM.run(*Mod);
  }

  //outs() << "Module before noise: " << *Mod;

  // Extract noise code regions from compound statements into separate functions.
  // These functions look exactly like functions with noise function attribute.
  {
    PassManager PM;
    PM.add(new NoiseExtractor(&noiseFnInfoVec));
    PM.run(*Mod);
  }

  //outs() << "Module after noise extraction: " << *Mod;

  // Move each function with noise attribute into its own module and
  // store the requested passes string.

  // Get the corresponding noise attribute.
  // We cannot just iterate over the metadata since the order of the
  // functions is important (for nested attributes). We have to be able
  // to iterate the modules in that same order.
  for (unsigned i=0, e=MD->getNumOperands(); i<e; ++i) {
    MDNode* functionMDN = MD->getOperand(i);

    // First operand is the function.
    // Second operand is a special 'noise' string.
    // Third operand is a string with the noise optimizations.
    // TODO: Transform these into assertions if we know that all MDNodes
    //       in the NamedMDNode are noise nodes.
    if (functionMDN->getNumOperands() != 3) continue;
    if (!isa<Function>(functionMDN->getOperand(0))) continue;
    if (!isa<MDString>(functionMDN->getOperand(1))) continue;
    if (!isa<MDString>(functionMDN->getOperand(2))) continue;

    MDString* noiseString = cast<MDString>(functionMDN->getOperand(1));
    if (!noiseString->getString().equals("noise")) continue;

    Function* noiseFn = cast<Function>(functionMDN->getOperand(0));

    NoiseFnInfo* nfi = 0;
    for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i)
    {
      if (noiseFnInfoVec[i]->mOrigFn != noiseFn) continue;
      nfi = noiseFnInfoVec[i];
      break;
    }

    // If the function is inside noiseFnInfoVec, it was not extracted from code
    // but corresponds to a noise function attribute. In this case, there
    // is no NoiseFnInfo object yet.
    if (!nfi)
    {
      nfi = new NoiseFnInfo(noiseFn);
      noiseFnInfoVec.push_back(nfi);
    }

    nfi->mOptString = cast<MDString>(functionMDN->getOperand(2));
    assert (nfi->mOptString);

    // Move the function to its own module so no optimization at
    // all is done.
    ValueToValueMapTy valueMap;
    Function* movedNoiseFn = CloneFunction(noiseFn, valueMap, false);

    Module* noiseFnMod = new Module(noiseFn->getName(), context);

    noiseFnMod->getFunctionList().push_back(movedNoiseFn);
    assert (movedNoiseFn->getParent() == noiseFnMod);

    // Update NoiseFnInfo objects that have their mCall member point into
    // the moved function, and thus, have to be updated to the new function.
    // Otherwise, we can not inline the functions back in order.
    SmallVector<NoiseFnInfo*, 4> toBeUpdatedNFIs;
    for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i)
    {
      NoiseFnInfo* nfi = noiseFnInfoVec[i];
      if (!nfi->mCall) continue;
      if (nfi->mCall->getParent()->getParent() != noiseFn) continue;
      toBeUpdatedNFIs.push_back(nfi);
      nfi->mCall = cast<CallInst>(valueMap[nfi->mCall]);
    }

    // Make the old function an external declaration so the rest of the
    // code is still valid and can be optimized.
    noiseFn->deleteBody();

    // We have to create a dummy use to prevent deletion of the function
    // during module pass optimization if it has no use in this module.
    {
      Function* dummyFn = Mod->getFunction("noise_dummy");
      assert (!dummyFn);
      FunctionType* fnTy = FunctionType::get(Type::getVoidTy(context), false);
      dummyFn = Function::Create(fnTy,
                                 GlobalValue::ExternalLinkage,
                                 "dummy",
                                 Mod);

      BasicBlock* dummyBB = BasicBlock::Create(context,
                                               "dummyBB",
                                               dummyFn,
                                               0);

      SmallVector<Value*, 4> params;
      for (Function::arg_iterator A=noiseFn->arg_begin(),
           AE=noiseFn->arg_end(); A!=AE; ++A) {
        Value* param = UndefValue::get(A->getType());
        params.push_back(param);
      }
      CallInst::Create(noiseFn,
                       ArrayRef<Value*>(params),
                       noiseFn->getReturnType()->isVoidTy() ? "" : "dummyCall",
                       dummyBB);

      ReturnInst::Create(context, dummyBB);

      nfi->mDummy = dummyFn;
    }

    nfi->mMovedFn = movedNoiseFn;

    //outs() << "after deletion of body:" << *noiseFn << "\n";
    //outs() << "cloned noise fn: " << *movedNoiseFn << "\n";
    //outs() << "tmp module: " << *noiseFnMod << "\n";
    //outs() << "old module: " << *TheModule << "\n";
  }

  // Now optimize each function in its own module separately (execute the
  // requested passes) and inline functions from nested noise attributes again.
  // NOTE: We must not inline functions that were created from "top-level"
  //       noise attributes, since this code then would be optimized with all
  //       other optimizations again.
  // NOTE: The module vector obeys the correct nesting order, so we first
  //       optimize the innermost code blocks, inline them, and then continue
  //       with the parents.
  for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i)
  {
    NoiseFnInfo* nfi   = noiseFnInfoVec[i];
    Function* noiseFn  = nfi->mMovedFn;
    Module*   noiseMod = noiseFn->getParent();
    StringRef str      = nfi->mOptString->getString();

    // Display all available passes.
    //NoisePassListener list;
    //Registry->enumerateWith(&list);
    outs() << "Running noise optimizations on function '"
      << noiseMod->getModuleIdentifier() << "': " << str << "\n";

    // Run requested noise passes.
    PassManager NoisePasses;
    NoisePasses.add(new DataLayout(noiseMod));

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
        // Add preparatory passes for WFV.
        NoisePasses.add(createLoopSimplifyPass());
        NoisePasses.add(createLowerSwitchPass());
        // Add induction variable simplification pass.
        NoisePasses.add(createIndVarSimplifyPass());
        // Add WFV pass wrapper.
        //NoisePasses.add(createWFVRunnerPass());
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
        int openParen = pass.find('(', 0);
        int closeParen = pass.find(')', 0);
        if(openParen < closeParen) {
          // get the number of arguments
          StringRef args = pass.substr(openParen + 1, closeParen - openParen);
          count = atoi(args.str().c_str());
        }

        NoisePasses.add(createIndVarSimplifyPass());
        NoisePasses.add(createLoopRotatePass());
        NoisePasses.add(createLoopUnrollPass(-1, count, false));
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

    // Run the required passes
    NoisePasses.run(*noiseMod);

    // If this is a function that was created from a top-level noise attribute,
    // we are done.
    if (!nfi->mReinline) continue;

    // Otherwise, reassemble and inline.
    ReassembleExtractedFunction(nfi);
  }
}

// Copy back 'noise' functions into TheModule.
void NoiseOptimizer::ReassembleExtractedFunction(NoiseFnInfo* nfi)
{
  Function* movedNoiseFn  = nfi->mMovedFn;
  Module*   movedNoiseMod = nfi->mMovedFn->getParent();
  assert (movedNoiseFn);

  Function* decl = nfi->mOrigFn;
  assert (decl);

  assert (Mod == nfi->mOrigFn->getParent());

  // Move function back to TheModule.
  movedNoiseFn->removeFromParent();
  Mod->getFunctionList().push_back(movedNoiseFn);
  assert (movedNoiseFn->getParent() == Mod);

  // Replace uses of declaration by function.
  decl->replaceAllUsesWith(movedNoiseFn);

  // Remove dummy function from TheModule.
  assert (nfi->mDummy);
  nfi->mDummy->eraseFromParent();
  nfi->mDummy = 0;

  // Make sure the function has the same name again.
  movedNoiseFn->takeName(decl);

  // Remove declaration from TheModule.
  decl->eraseFromParent();

  // We don't need the temporary module anymore.
  delete movedNoiseMod;
  nfi->mMovedFn = 0;

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
    // Perform some standard optimizations upfront.
    // This is to prevent pointer aliasing in the extracted functions.
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

void NoiseOptimizer::Reassemble()
{
  PrettyStackTraceString CrashInfo("NOISE: reassemble module after optimizations");

  for (unsigned i=0, e=noiseFnInfoVec.size(); i<e; ++i) {
    NoiseFnInfo* nfi = noiseFnInfoVec[i];

    if (nfi->mReinline) continue; // Has already been reassembled/inlined.
    ReassembleExtractedFunction(nfi);
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
