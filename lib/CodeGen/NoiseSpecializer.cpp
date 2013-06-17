//===--- NoiseSpecializer.cpp - Noise Specialized Loop Dispatch -----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// The specialized loop dispatch transformation for noise functions
//
//===----------------------------------------------------------------------===//

#include "NoiseSpecializer.h"

#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/PassRegistry.h"
#include "llvm/PassManagers.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"   // extractCodeRegion()
#include "llvm/Transforms/Utils/BasicBlockUtils.h" // SplitBlock()
#include "llvm/Transforms/Utils/Cloning.h" // CloneFunction()
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h" // FunctionType
#include "llvm/IR/Constants.h" // UndefValue
#include "llvm/IR/Instructions.h" // CallInst

#include <sstream>

using namespace llvm;

namespace llvm {

#if 0
Pass*
createNoiseSpecializerPass()
{
    return new NoiseSpecializer();
}
#endif


NoiseSpecializer::NoiseSpecializer()
: FunctionPass(ID), mVariable(""), mValues(0)
{
    assert (false && "empty constructor must never be called!");
    initializeNoiseSpecializerPass(*PassRegistry::getPassRegistry());
}

NoiseSpecializer::NoiseSpecializer(StringRef&                 variable,
                                   const SmallVector<int, 4>& values)
: FunctionPass(ID), mVariable(variable), mValues(&values)
{
    initializeNoiseSpecializerPass(*PassRegistry::getPassRegistry());
}

NoiseSpecializer::~NoiseSpecializer()
{
}

bool
NoiseSpecializer::runOnFunction(Function &F)
{
  mModule   = F.getParent();
  mContext  = &F.getContext();
  mLoopInfo = &getAnalysis<LoopInfo>();

  const bool success = runSLD(&F);

  if (!success)
  {
    errs() << "ERROR: Specialized loop dispatching failed!\n";
  }

  // If not successful, nothing changed.
  // TODO: Make sure this is correct, e.g. by re-inlining the extracted
  //       loop body.
  return success;
}

void
NoiseSpecializer::getAnalysisUsage(AnalysisUsage &AU) const
{
  AU.addRequired<LoopInfo>();
}


// TODO: Implement generation of fixup code for cases where we either
//       don't know the exact iteration count or where it is not an exact
//       multiple of the vectorization width.
// TODO: Make assertions return gracefully instead.
bool
NoiseSpecializer::runSLD(Function* noiseFn)
{
  assert (noiseFn);

  // Get the only outermost loop of this function.
  assert (std::distance(mLoopInfo->begin(), mLoopInfo->end()) == 1 &&
          "expected exactly one top level loop in noise function!");
  Loop* loop = *mLoopInfo->begin();
  assert (loop);

  BasicBlock* preheaderBB = loop->getLoopPreheader();
  BasicBlock* headerBB    = loop->getHeader();
  BasicBlock* latchBB     = loop->getLoopLatch();
  BasicBlock* exitBB      = loop->getUniqueExitBlock();
  BasicBlock* exitingBB   = loop->getExitingBlock();
  assert (preheaderBB && headerBB && latchBB &&
          "specialized loop dispatching of non-simplified loop not supported!");
  assert (loop->isLoopSimplifyForm() &&
          "specialized loop dispatching of non-simplified loop not supported!");

  //-------------------------------------------------------------------------//

  return true;
}



char NoiseSpecializer::ID = 0;
} // namespace llvm

INITIALIZE_PASS_BEGIN(NoiseSpecializer, "noise-specialized-loop-dispatch",
                      "Specialized loop dispatching for noise functions", false, false)
INITIALIZE_PASS_DEPENDENCY(DominatorTree)
INITIALIZE_PASS_DEPENDENCY(LoopInfo)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolution)
INITIALIZE_PASS_END(NoiseSpecializer, "noise-specialized-loop-dispatch",
                    "Specialized loop dispatching for noise functions", false, false)
