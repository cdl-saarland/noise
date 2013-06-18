//===--- NoiseFusion.cpp - Noise Fusion Loop Dispatch ---------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Loop fusion for noise attributed loops
//
//===----------------------------------------------------------------------===//

#include "NoiseFusion.h"

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
createNoiseFusionPass()
{
    return new NoiseFusion();
}
#endif


NoiseFusion::NoiseFusion()
: FunctionPass(ID), mVariable(""), mValues(0)
{
    initializeNoiseFusionPass(*PassRegistry::getPassRegistry());
}

bool
NoiseFusion::runOnFunction(Function &F)
{
  mModule   = F.getParent();
  mContext  = &F.getContext();
  mLoopInfo = &getAnalysis<LoopInfo>();

  typedef LoopInfoBase<BasicBlock, Loop> LIB;
  LIB& Base = mLoopInfo->getBase();
  const Loop *Loop2 = *Base.begin();
  const Loop *Loop1 = *(Base.begin() + 1);
  PHINode *Phi1 = Loop1->getCanonicalInductionVariable();
  PHINode *Phi2 = Loop2->getCanonicalInductionVariable();
  BasicBlock *Header1 = Loop1->getHeader(); 
  BasicBlock *Header2 = Loop2->getHeader(); 
  BasicBlock *Latch1 = Loop1->getLoopLatch(); 
  BasicBlock *Latch2 = Loop2->getLoopLatch();

  Value *Induction1 = Phi1->getIncomingValueForBlock(Latch1);
  Value *Induction2 = Phi2->getIncomingValueForBlock(Latch2);

  assert(Induction1->getNumUses() == 1);
  assert(Induction2->getNumUses() == 1);

  BranchInst *HeaderBranch2 = cast<BranchInst>(Header2->getTerminator());
  assert(HeaderBranch2->isConditional() && HeaderBranch2->getNumSuccessors() == 2);

  BasicBlock *BodyStart2 = Loop2->contains(HeaderBranch2->getSuccessor(0)) 
                         ? HeaderBranch2->getSuccessor(0) 
                         : HeaderBranch2->getSuccessor(1);

  BranchInst *LatchBranch1 = cast<BranchInst>(Latch1->getTerminator());
  assert(LatchBranch1->isUnconditional() && LatchBranch1->getNumSuccessors() == 1);
  LatchBranch1->eraseFromParent();
  BranchInst::Create(BodyStart2, Latch1);

  BranchInst *LatchBranch2 = cast<BranchInst>(Latch2->getTerminator());
  assert(LatchBranch2->isUnconditional() && LatchBranch2->getNumSuccessors() == 1);
  LatchBranch2->eraseFromParent();
  BranchInst::Create(Header1, Latch2);

  if (Phi1->getIncomingBlock(0) == Latch1)
    Phi1->setIncomingBlock(0, Latch2);
  else
    Phi1->setIncomingBlock(1, Latch2);

  BranchInst *HeaderBranch1 = cast<BranchInst>(Header1->getTerminator());
  assert(HeaderBranch1->isConditional() && HeaderBranch1->getNumSuccessors() == 2);
  Value *Cond = HeaderBranch1->getCondition();
  BasicBlock *Targets[2] = { HeaderBranch1->getSuccessor(0), HeaderBranch1->getSuccessor(1) };
  BasicBlock* Exit = Loop2->contains(HeaderBranch2->getSuccessor(0)) 
                   ? HeaderBranch2->getSuccessor(1) 
                   : HeaderBranch2->getSuccessor(0);
  if (Loop1->contains(Targets[0]))
    Targets[1] = Exit;
  else
    Targets[0] = Exit;
  HeaderBranch1->eraseFromParent();
  BranchInst::Create(Targets[0], Targets[1], Cond, Header1);

  Phi2->replaceAllUsesWith(Phi1);
  Header2->eraseFromParent();

  return true;
}

void
NoiseFusion::getAnalysisUsage(AnalysisUsage &AU) const
{
  AU.addRequired<LoopInfo>();
}

char NoiseFusion::ID = 0;

} // namespace llvm

INITIALIZE_PASS_BEGIN(NoiseFusion, "noise-loop-fusion",
                      "Loop fusion for noise attributed loops", false, false)
INITIALIZE_PASS_DEPENDENCY(DominatorTree)
INITIALIZE_PASS_DEPENDENCY(LoopInfo)
INITIALIZE_PASS_END(NoiseFusion, "noise-loop-fusion",
                      "Loop fusion for noise attributed loops", false, false)
