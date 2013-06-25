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

NoiseFusion::NoiseFusion()
: FunctionPass(ID)
{
    initializeNoiseFusionPass(*PassRegistry::getPassRegistry());
}

class Sorter {
public:

  Sorter(DominatorTree* DomTree) : mDomTree(DomTree) {}

  bool operator () (const Loop *Loop1, const Loop *Loop2) { 
    return mDomTree->dominates(Loop1->getHeader(), Loop2->getHeader());
  }

  DominatorTree *mDomTree;
};

bool
NoiseFusion::runOnFunction(Function &F) {
  mModule   = F.getParent();
  mContext  = &F.getContext();
  mLoopInfo = &getAnalysis<LoopInfo>();
  mDomTree  = &getAnalysis<DominatorTree>();

  typedef LoopInfoBase<BasicBlock, Loop> LIB;
  LIB& Base = mLoopInfo->getBase();

  size_t NumLoops = std::distance(Base.begin(), Base.end());
  if (NumLoops <= 1)
    return true;

  std::vector<const Loop*> Loops(NumLoops);
  std::copy(Base.begin(), Base.end(), Loops.begin());
  std::sort(Loops.begin(), Loops.end(), Sorter(mDomTree));

  const Loop *Loop1 = Loops.front();
  PreHeader1 = Loop1->getLoopPreheader();
  Header1 = Loop1->getHeader(); 
  Latch1 = Loop1->getLoopLatch(); 
  HeaderBranch1 = cast<BranchInst>(Header1->getTerminator());
  int ExitIndex = Loop1->contains(HeaderBranch1->getSuccessor(0)) ? 1 : 0;

  for (std::vector<const Loop*>::const_iterator Loop2 = Loops.begin() + 1, e = Loops.end(); Loop2 != e; ++Loop2)
    fuse(ExitIndex, *Loop2);

  return true;
}

template<bool early>
static void moveTo(BasicBlock *From, BasicBlock *To) {
  // move everything except terminator from Header2 to BodyStart2
  std::vector<Instruction*> Is;
  for (BasicBlock::iterator i = From->begin(); dyn_cast<TerminatorInst>(i) == 0; ++i) {
    assert(dyn_cast<PHINode>(i) == 0);
    Is.push_back(i);
  }

  for (size_t i = 0, e = Is.size(); i != e; ++i)
    Is[i]->moveBefore(early ? To->getFirstNonPHI() : To->getTerminator());
}

void NoiseFusion::fuse(int ExitIndex, const Loop *Loop2) {
  BasicBlock *PreHeader2 = Loop2->getLoopPreheader();
  BasicBlock *Header2 = Loop2->getHeader(); 
  BasicBlock *Latch2 = Loop2->getLoopLatch();

  BranchInst *HeaderBranch2 = cast<BranchInst>(Header2->getTerminator());
  assert(HeaderBranch2->isConditional() && HeaderBranch2->getNumSuccessors() == 2);

  BasicBlock *BodyStart2 = Loop2->contains(HeaderBranch2->getSuccessor(0)) 
                         ? HeaderBranch2->getSuccessor(0) 
                         : HeaderBranch2->getSuccessor(1);

  // fix phi functions first
  Latch1->replaceSuccessorsPhiUsesWith(Latch2);
  Header2->replaceSuccessorsPhiUsesWith(Header1);
  PreHeader2->replaceSuccessorsPhiUsesWith(PreHeader1);

  // jump: Latch1 -> BodyStart2
  BranchInst *LatchBranch1 = cast<BranchInst>(Latch1->getTerminator());
  assert(LatchBranch1->isUnconditional() && LatchBranch1->getNumSuccessors() == 1);
  LatchBranch1->eraseFromParent();
  BranchInst::Create(BodyStart2, Latch1);

  // jump: Latch2 -> Header1
  BranchInst *LatchBranch2 = cast<BranchInst>(Latch2->getTerminator());
  assert(LatchBranch2->isUnconditional() && LatchBranch2->getNumSuccessors() == 1);
  LatchBranch2->eraseFromParent();
  BranchInst::Create(Header1, Latch2);

  BranchInst *HeaderBranch1 = cast<BranchInst>(Header1->getTerminator());
  assert(HeaderBranch1->isConditional() && HeaderBranch1->getNumSuccessors() == 2);
  Value *Cond = HeaderBranch1->getCondition();
  BasicBlock *Targets[2] = { HeaderBranch1->getSuccessor(0), HeaderBranch1->getSuccessor(1) };
  BasicBlock* Exit = Loop2->contains(HeaderBranch2->getSuccessor(0)) 
                   ? HeaderBranch2->getSuccessor(1) 
                   : HeaderBranch2->getSuccessor(0);
  Targets[ExitIndex] = Exit;
  HeaderBranch1->eraseFromParent();
  HeaderBranch1 = BranchInst::Create(Targets[0], Targets[1], Cond, Header1);

  // move all phis in Header2 to Header1
  PHINode *Phi;
  std::vector<PHINode*> Phis;
  for (BasicBlock::iterator i = Header2->begin(); (Phi = dyn_cast<PHINode>(i)); ++i)
    Phis.push_back(Phi);

  for (size_t i = 0, e = Phis.size(); i != e; ++i)
    Phis[i]->moveBefore(&Header1->front());

  // move everything except terminator from Header2 and PreHeader2 to BodyStart2
  moveTo<true>(Header2, BodyStart2);
  moveTo<false>(PreHeader2, PreHeader1);

  // erase now unreachable (pre-)headers
  PreHeader2->eraseFromParent();
  Header2->eraseFromParent();

  // make new big loop's latch current latch
  Latch1 = Latch2;
}

void
NoiseFusion::getAnalysisUsage(AnalysisUsage &AU) const
{
  AU.addRequired<DominatorTree>();
  AU.addRequired<LoopInfo>();
}

char NoiseFusion::ID = 0;

} // namespace llvm

INITIALIZE_PASS_BEGIN(NoiseFusion, "noise-loop-fusion",
                      "Loop fusion for noise attributed loops", false, false)
INITIALIZE_PASS_DEPENDENCY(DominatorTree)
INITIALIZE_PASS_DEPENDENCY(LoopInfo)
INITIALIZE_PASS_DEPENDENCY(LoopSimplify)
INITIALIZE_PASS_END(NoiseFusion, "noise-loop-fusion",
                      "Loop fusion for noise attributed loops", false, false)
