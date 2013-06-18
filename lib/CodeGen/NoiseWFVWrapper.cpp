//===--- NoiseWFVWrapper.cpp - Noise Optimizations ------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Noise vectorizer interface
//
//===----------------------------------------------------------------------===//

#ifdef COMPILE_NOISE_WFV_WRAPPER

#include "NoiseWFVWrapper.h"

#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/PassRegistry.h"
#include "llvm/PassManagers.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopInfo.h"
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
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"   // extractCodeRegion()
#include "llvm/Transforms/Utils/BasicBlockUtils.h" // SplitBlock()
#include "llvm/Transforms/Utils/Cloning.h" // CloneFunction()
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h" // FunctionType
#include "llvm/IR/Constants.h" // UndefValue
#include "llvm/IR/Instructions.h" // CallInst
#include "llvm/Analysis/Verifier.h" // VerifyFunction
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpander.h"

#include <sstream>

#include <wfvInterface.h>

//#define DEBUG_NOISE_WFV(x) do { x } while (0)
#define DEBUG_NOISE_WFV(x) ((void)0)

using namespace llvm;

namespace llvm {

NoiseWFVWrapper::ReductionUpdate::~ReductionUpdate()
{
  mOtherOperands->clear();
  mResultUsers->clear();
  delete mOtherOperands;
  delete mResultUsers;
}

NoiseWFVWrapper::ReductionVariable::~ReductionVariable()
{
  for (RedUpMapType::iterator it=mUpdates->begin(),
       E=mUpdates->end(); it!=E; ++it)
  {
    delete it->second;
  }
  delete mUpdates;
}

#if 0
Pass*
createNoiseWFVWrapperPass()
{
  return new NoiseWFVWrapper();
}
#endif


NoiseWFVWrapper::NoiseWFVWrapper(const unsigned vectorizationWidth,
                                 const bool     useAVX,
                                 const bool     useDivergenceAnalysis,
                                 const bool     verbose)
: FunctionPass(ID),
  mFinished(false),
  mVectorizationFactor(vectorizationWidth),
  mUseAVX(useAVX),
  mUseDivergenceAnalysis(useDivergenceAnalysis),
  mVerbose(verbose)
{
  initializeNoiseWFVWrapperPass(*PassRegistry::getPassRegistry());
}

NoiseWFVWrapper::~NoiseWFVWrapper()
{
}

bool
NoiseWFVWrapper::runOnFunction(Function &F)
{
  // Make sure we only vectorize the function that we want to vectorize.
  if (mFinished) return false;
  mFinished = true;

  mModule   = F.getParent();
  mContext  = &F.getContext();
  mLoopInfo = &getAnalysis<LoopInfo>();
  mDomTree  = &getAnalysis<DominatorTree>();
  mSCEV     = &getAnalysis<ScalarEvolution>();

  const bool success = runWFV(&F);

  if (!success)
  {
    errs() << "ERROR: WFV failed!\n";
  }

  // If not successful, nothing changed.
  // TODO: Make sure this is correct, e.g. by re-inlining the extracted
  //       loop body.
  return success;
}

void
NoiseWFVWrapper::getAnalysisUsage(AnalysisUsage &AU) const
{
  AU.addRequired<DominatorTree>();
  AU.addRequired<LoopInfo>();
  AU.addRequired<ScalarEvolution>();
}


// Helper functions for runWFV().
namespace {

Loop*
createNewLoop(Loop* loop, Loop* parentLoop, ValueToValueMapTy& valueMap, LoopInfo* loopInfo)
{
  Loop* newLoop = new Loop();

  // Add all of the blocks in loop to the new loop.
  for (Loop::block_iterator BB=loop->block_begin(), BBE=loop->block_end(); BB!=BBE; ++BB)
  {
    if (loopInfo->getLoopFor(*BB) != loop) continue;
    newLoop->addBasicBlockToLoop(cast<BasicBlock>(valueMap[*BB]), loopInfo->getBase());
  }

  // Add all of the subloops to the new loop.
  for (Loop::iterator SL=loop->begin(), SLE=loop->end(); SL!=SLE; ++SL)
  {
    createNewLoop(*SL, newLoop, valueMap, loopInfo);
  }

  return newLoop;
}

Loop*
cloneLoop(Loop*              loop,
          ValueToValueMapTy& valueMap,
          LoopInfo*          loopInfo)
{
  assert (loop && loopInfo);
  Function* f = loop->getHeader()->getParent();
  assert (f);

  // Get all info we need about the loop before we start cloning.
  BasicBlock* preheaderBB = loop->getLoopPreheader();
  SmallVector<Loop::Edge, 2> exitEdges;
  loop->getExitEdges(exitEdges);

  // Clone blocks and store mappings of blocks and instructions.
  SmallVector<BasicBlock*, 4> loopBlocks;
  SmallVector<BasicBlock*, 4> newBlocks;
  loopBlocks.insert(loopBlocks.end(), loop->block_begin(), loop->block_end());
  newBlocks.reserve(loopBlocks.size()+2);

  for (unsigned i=0, e=loopBlocks.size(); i!=e; ++i)
  {
    BasicBlock* newBB = CloneBasicBlock(loopBlocks[i], valueMap, ".", f);
    newBlocks.push_back(newBB);
    valueMap[loopBlocks[i]] = newBB;
  }

  // Create new preheader block.
  BasicBlock* headerBB = loop->getHeader();
  BasicBlock* newHeaderBB = cast<BasicBlock>(valueMap[headerBB]);
  BasicBlock* newPreheaderBB = BasicBlock::Create(preheaderBB->getContext(),
                                                  preheaderBB->getName()+".",
                                                  f,
                                                  newHeaderBB);
  BranchInst::Create(headerBB, newPreheaderBB); // This is just for consistency, all edges are updated below.
  newPreheaderBB->moveBefore(newHeaderBB);
  newBlocks.push_back(newPreheaderBB);
  valueMap[preheaderBB] = newPreheaderBB;

  // Create new exit blocks with exit value phis and store mappings of blocks and phis.
  for (unsigned i=0, e=exitEdges.size(); i!=e; ++i)
  {
    const BasicBlock* exitingBB = exitEdges[i].first;
    const BasicBlock* exitBB    = exitEdges[i].second;
    BasicBlock* newExitingBB = cast<BasicBlock>(valueMap[exitingBB]);

    BasicBlock* newExitBB = BasicBlock::Create(exitBB->getContext(),
                                               exitBB->getName()+".",
                                               f,
                                               newExitingBB);
    newExitingBB->moveBefore(newExitBB);
    // Add a dummy terminator (no branch, since below we update all branches).
    Type* fnRetTy = f->getFunctionType()->getReturnType();
    ReturnInst* dummyRet = fnRetTy->isVoidTy() ?
        ReturnInst::Create(f->getContext(), newExitBB) :
        ReturnInst::Create(f->getContext(), UndefValue::get(fnRetTy), newExitBB);

    newBlocks.push_back(newExitBB);
    valueMap[exitBB] = newExitBB;

    // Clone exit block phis (LCSSA).
    for (BasicBlock::const_iterator I=exitBB->begin(), IE=exitBB->end(); I!=IE; ++I)
    {
      if (!isa<PHINode>(I)) break;
      const PHINode* phi = cast<PHINode>(I);
      PHINode* newPhi = cast<PHINode>(phi->clone());
      newPhi->insertBefore(dummyRet);
      valueMap[phi] = newPhi;
    }
  }

  // Rewire blocks to their cloned successors.
  for (unsigned i=0, e=newBlocks.size(); i!=e; ++i)
  {
    BasicBlock* block = newBlocks[i];
    TerminatorInst* terminator = block->getTerminator();
    if (!terminator) continue; // This is an exit block.
    for (unsigned s=0, se=terminator->getNumSuccessors(); s<se; ++s)
    {
      BasicBlock* succBB = terminator->getSuccessor(s);
      assert (valueMap[succBB]);
      terminator->setSuccessor(s, cast<BasicBlock>(valueMap[succBB]));
    }
  }

  // Update operands coming from other blocks.
  for (unsigned i=0, e=newBlocks.size(); i!=e; ++i)
  {
    BasicBlock* block = newBlocks[i];
    for (BasicBlock::iterator I=block->begin(), IE=block->end(); I!=IE; ++I)
    {
      // Update incoming blocks of phi nodes.
      if (PHINode* phi = dyn_cast<PHINode>(I))
      {
        for (unsigned j=0, je=phi->getNumIncomingValues(); j<je; ++j)
        {
          BasicBlock* incBB = phi->getIncomingBlock(j);
          BasicBlock* newIncBB = cast<BasicBlock>(valueMap[incBB]);
          phi->setIncomingBlock(j, newIncBB);
        }
      }

      // Update operands.
      for (unsigned j=0, je=I->getNumOperands(); j<je; ++j)
      {
        Value* mappedOp = valueMap[I->getOperand(j)];
        if (!mappedOp) continue;
        I->setOperand(j, mappedOp);
      }
    }
  }

  // The only remaining "loose ends" now are the following:
  // - New preheader has no entry edge (incoming values do not dominate their uses)
  // - New exit blocks have no successors.

  // Create new loop, update loop info.
  return createNewLoop(loop, 0, valueMap, loopInfo);
}

template<unsigned S>
Function*
extractLoopBody(Loop*                        loop,
                PHINode*                     indVarPhi,
                Instruction*                 indVarUpdate,
                const unsigned               vectorizationFactor,
                DominatorTree*               domTree,
                SmallVector<BasicBlock*, S>& loopBody)
{
  assert (loop && indVarPhi);
  assert (loopBody.empty());

  BasicBlock* headerBB    = loop->getHeader();
  BasicBlock* latchBB     = loop->getLoopLatch();
  BasicBlock* exitingBB   = loop->getExitingBlock();
  assert (loop->getLoopPreheader() && headerBB && latchBB &&
          "vectorization of non-simplified loop not supported!");
  assert (exitingBB &&
          "vectorization of loop with multiple exits not supported!");
  assert (exitingBB == headerBB &&
          "expected exiting block to be the loop header!");

  // Collect all blocks that are definitely part of the body.
  std::vector<BasicBlock*>& blocks = loop->getBlocksVector();
  for (unsigned i=0, e=blocks.size(); i<e; ++i)
  {
    BasicBlock* block = blocks[i];
    if (block == headerBB) continue;
    if (block == exitingBB) continue; // Redundant.
    if (block == latchBB) continue;
    loopBody.push_back(block);
  }

  // Get loop exit condition.
  assert (isa<BranchInst>(exitingBB->getTerminator()));
  BranchInst* exitBr = cast<BranchInst>(exitingBB->getTerminator());

  assert (isa<ICmpInst>(exitBr->getCondition()));
  assert (cast<Instruction>(exitBr->getCondition())->getParent() == exitingBB &&
          "expected exit condition to be in exiting block!");
  assert (exitBr->getCondition()->getNumUses() == 1 &&
          "expected exit condition to have only one use in the exit branch!");

  // Split latch directly before induction variable increment.
  BasicBlock* newLatchBB = SplitBlock(latchBB, indVarUpdate, domTree);
  newLatchBB->setName(latchBB->getName()+".wfv.latch");

  // latchBB is now the part of the latch that is only the body.
  loopBody.push_back(latchBB);

  CodeExtractor extractor(loopBody, domTree, false);
  assert (extractor.isEligible());
  Function* bodyFn = extractor.extractCodeRegion();
  assert (bodyFn);

  // Now, adjust the original loop.
  // Increment by 'vectorizationFactor' instead of 1.
  Constant* vecFactorConst = ConstantInt::get(indVarUpdate->getType(), vectorizationFactor, false);
  Instruction* newIndVarUpdate = BinaryOperator::Create(Instruction::Add,
                                                        indVarPhi,
                                                        vecFactorConst,
                                                        "wfv.inc",
                                                        indVarUpdate);
  indVarUpdate->moveBefore(newIndVarUpdate);
  indVarUpdate->replaceAllUsesWith(newIndVarUpdate);
  newIndVarUpdate->replaceUsesOfWith(newIndVarUpdate, indVarUpdate);

  return bodyFn;
}

bool
isPredecessor(const BasicBlock*                  bbA,
              const BasicBlock*                  bbB,
              SmallPtrSet<const BasicBlock*, 8>& visitedBlocks)
{
  assert (bbA && bbB);

  if (visitedBlocks.count(bbB)) return false;
  visitedBlocks.insert(bbB);

  if (bbA == bbB) return false;

  for (const_pred_iterator P=pred_begin(bbB), PE=pred_end(bbB); P!=PE; ++P)
  {
    const BasicBlock* predBB = *P;

    if (predBB == bbA) return true;
    if (isPredecessor(bbA, predBB, visitedBlocks)) return true;
  }

  return false;
}

bool
isPredecessor(const Instruction* instA, const Instruction* instB)
{
  assert (instA && instB);

  if (instA == instB) return false;

  const BasicBlock* parentB = instB->getParent();

  // Search B's list for the first occurrence of A or B.
  const BasicBlock::InstListType& instList = parentB->getInstList();
  for (BasicBlock::InstListType::const_iterator it=instList.begin(),
       E=instList.end(); it!=E; ++it)
  {
    const Instruction* curInst = &(*it);

    // Stop as soon as we see B.
    if (curInst == instB) break;

    // If we see A, it comes before B, so A is predecessor of B.
    if (curInst == instA) return true;
  }

  // A was not found, so we now test whether parentA is a predecessor of parentB.
  const BasicBlock* parentA = instA->getParent();
  SmallPtrSet<const BasicBlock*, 8> visitedBlocks;
  return isPredecessor(parentA, parentB, visitedBlocks);
}

typedef NoiseWFVWrapper::RedUpMapType RedUpMapType;
typedef NoiseWFVWrapper::RedVarVecType RedVarVecType;
typedef NoiseWFVWrapper::ReductionUpdate ReductionUpdate;
typedef NoiseWFVWrapper::ReductionVariable ReductionVariable;
typedef NoiseWFVWrapper::ReductionUpdate::OtherOperandsVec OtherOperandsVec;
typedef NoiseWFVWrapper::ReductionUpdate::ResultUsersVec ResultUsersVec;

// Determine a valid position for the call (if any):
// - *After* the last "update operation" that is a phi or select.
// - *After* the last "other operand" of any "update operation".
// - *Before* the first "result user" of any "update operation".
// - If that is not possible, we may try to move instructions.
//   Otherwise, we can't do anything, so WFV fails due to a "bad" reduction.
// NOTE: If operations require masks, this position may not be correct.
//       However, this can only be fixed after WFV is done and masks are available.
// TODO: We have to make sure we don't place the call in a branch that is retained
//       during WFV!
Instruction*
getCallInsertPosition(const ReductionVariable& redVar,
                      Instruction*             earliestPos,
                      Instruction*             latestPos)
{
  assert (earliestPos->getParent()->getParent() == redVar.mPhiArg->getParent());
  assert (latestPos->getParent()->getParent() == redVar.mPhiArg->getParent());

  const RedUpMapType& updates = *redVar.mUpdates;
#if 0
  // - *After* the last "update operation" that is a phi or select.
  // TODO: Not sure if this is required.
  for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
  {
    const ReductionUpdate& redUp = *it->second;
    Instruction* updateOperation = redUp.mOperation;
    assert (updateOperation->getParent()->getParent() == f);
    if (!isa<PHINode>(updateOperation) && !isa<SelectInst>(updateOperation)) continue;
    if (isPredecessor(updateOperation, earliestPos)) continue;
    earliestPos = updateOperation;
  }
#endif

  // - *After* the last "other operand" of any "update operation".
  for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
  {
    const ReductionUpdate& redUp = *it->second;
    const OtherOperandsVec& otherOperands = *redUp.mOtherOperands;
    for (OtherOperandsVec::const_iterator it2=otherOperands.begin(),
         E2=otherOperands.end(); it2!=E2; ++it2)
    {
      if (!isa<Instruction>(*it2)) continue;
      Instruction* otherOperand = cast<Instruction>(*it2);
      assert (otherOperand->getParent()->getParent() == redVar.mPhiArg->getParent());
      if (isPredecessor(otherOperand, earliestPos)) continue;
      earliestPos = otherOperand;
    }
  }

  // - *Before* the first "result user" of any "update operation".
  for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
  {
    const ReductionUpdate& redUp = *it->second;
    const ResultUsersVec& resultUsers = *redUp.mResultUsers;
    if (resultUsers.empty()) continue;
    for (ResultUsersVec::const_iterator it2=resultUsers.begin(),
         E2=resultUsers.end(); it2!=E2; ++it2)
    {
      Instruction* resultUser = *it2;
      assert (resultUser->getParent()->getParent() == redVar.mPhiArg->getParent());
      if (isPredecessor(latestPos, resultUser)) continue;
      latestPos = resultUser;
    }
  }

  if (!isPredecessor(earliestPos, latestPos))
  {
    errs() << "ERROR: Bad reduction found: There is no valid single position"
        << " to perform all operations connected to reduction variable:\n"
        << *redVar.mPhi << "\n";
    assert (false && "Bad reduction found!");
    return 0;
  }

  return latestPos;
}

// Generate a reduction function F_R:
// - Return type is the type of the reduction (if there is a result user).
// - One input parameter for P.
// - One input parameter per "other operand" per "update operation".
// - One input parameter per "update operation" that requires a mask.
// - One output parameter per "update operation" that has at least one "result user".
void
generateScalarReductionFunction(ReductionVariable& redVar)
{
  assert (!redVar.mReductionFn);
  Type* type = redVar.mPhi->getType();
  LLVMContext& context = type->getContext();

  SmallVector<Type*, 4> params;

  // Add input parameter for P.
  params.push_back(type);

  // Add input parameters for "other operands".
  const RedUpMapType& updates = *redVar.mUpdates;
  for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
  {
    const ReductionUpdate& redUp = *it->second;
    const OtherOperandsVec& otherOperands = *redUp.mOtherOperands;
    for (OtherOperandsVec::const_iterator it2=otherOperands.begin(),
         E2=otherOperands.end(); it2!=E2; ++it2)
    {
      Value* operand = *it2;
      params.push_back(operand->getType());
    }
  }

  // Add output parameter for final result (that goes back to phi).
  params.push_back(PointerType::getUnqual(type));

  // Add output parameters for "result users".
  for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
  {
    const ReductionUpdate& redUp = *it->second;
    if (redUp.mResultUsers->empty()) continue;
    Type* updateType = redUp.mOperation->getType();
    params.push_back(PointerType::getUnqual(updateType));
  }

  FunctionType* fType = FunctionType::get(Type::getVoidTy(context), params, false);

  Module* mod = redVar.mPhi->getParent()->getParent()->getParent();
  redVar.mReductionFn = Function::Create(fType, Function::ExternalLinkage, "red_fn", mod);
}

// This works analogously to parameter generation in generateDummyReductionFunction().
void
getCallArgs(ReductionVariable&      redVar,
            SmallVector<Value*, 4>& args)
{
  assert (redVar.mReductionPos);

  // Add P.
  args.push_back(redVar.mPhiArg);

  // Add "other operands".
  Function* f = redVar.mPhiArg->getParent();
  const RedUpMapType& updates = *redVar.mUpdates;
  for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
  {
    const ReductionUpdate& redUp = *it->second;
    const OtherOperandsVec& otherOperands = *redUp.mOtherOperands;
    for (OtherOperandsVec::const_iterator it2=otherOperands.begin(),
         E2=otherOperands.end(); it2!=E2; ++it2)
    {
      Value* otherOp = *it2;

      if (!isa<Instruction>(otherOp) && !isa<Argument>(otherOp))
      {
        args.push_back(otherOp);
        continue;
      }

      // Generate alloca/store/load and add load (rely on later SROA phase).
      Type* otherOpType = otherOp->getType();
      // Create alloca.
      Instruction* allocaInsertPos = f->getEntryBlock().getFirstNonPHI();
      AllocaInst* alloca = new AllocaInst(otherOpType,
                                          "red.otherop.storage",
                                          allocaInsertPos);
      // Store value after def.
      if (Instruction* otherOpI = dyn_cast<Instruction>(otherOp))
      {
        StoreInst* store = new StoreInst(otherOpI, alloca, otherOpI);
        otherOpI->moveBefore(store);
      }
      else
      {
        assert (isa<Argument>(otherOp));
        assert (cast<Argument>(otherOp)->getParent() == f);
        new StoreInst(otherOp, alloca, allocaInsertPos);
      }
      // Reload value at reduction position.
      LoadInst* reload = new LoadInst(alloca, "red.otherop.reload", redVar.mReductionPos);

      args.push_back(reload);
    }
  }

  // Generate and add alloca for final result.
  Type* redType = redVar.mPhi->getType();
  AllocaInst* alloca = new AllocaInst(redType,
                                      "red.result.storage",
                                      f->getEntryBlock().getFirstNonPHI());
  redVar.mResultPtr = alloca;
  args.push_back(alloca);

  // Generate and add alloca for "result users", if any.
  // These allocas should be inside the body, otherwise they are treated as uniform by WFV,
  // which will discard the intermediate results of all but one lane.
  // Unfortunately, CodeExtractor refuses to extract blocks with local allocas.
  // -> Thus, we add special calls here that will later be replaced by allocas.
  // TODO: The position is not a good idea if we later move the call again...
  for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
  {
    ReductionUpdate& redUp = *it->second;
    if (redUp.mResultUsers->empty()) continue;

    Type* updateType = redUp.mOperation->getType();
    AllocaInst* alloca = new AllocaInst(updateType,
                                        "red.user.storage",
                                        f->getEntryBlock().getFirstNonPHI());

    assert (!redUp.mIntermediateResultPtr);
    redUp.mIntermediateResultPtr = alloca;
    args.push_back(alloca);
  }
}

// Create SIMD type from scalar type.
// -> only 32bit-float, integers <= 32bit, pointers, arrays and structs allowed
// -> no scalar datatypes allowed
// -> no pointers to pointers allowed
// TODO: i8* should not be transformed to <4 x i8>* !
Type*
vectorizeSIMDType(Type* oldType, const unsigned vectorizationFactor)
{
  if (oldType->isFloatingPointTy() || oldType->isIntegerTy())
  {
    return VectorType::get(oldType, vectorizationFactor);
  }

  switch (oldType->getTypeID())
  {
  case Type::PointerTyID:
    {
      PointerType* pType = cast<PointerType>(oldType);
      return PointerType::get(vectorizeSIMDType(pType->getElementType(), vectorizationFactor),
                              pType->getAddressSpace());
    }
  case Type::ArrayTyID:
    {
      ArrayType* aType = cast<ArrayType>(oldType);
      return ArrayType::get(vectorizeSIMDType(aType->getElementType(), vectorizationFactor),
                            aType->getNumElements());
    }
  case Type::StructTyID:
    {
      StructType* sType = cast<StructType>(oldType);
      std::vector<Type*> newParams;
      for (unsigned i=0; i<sType->getNumContainedTypes(); ++i)
      {
        newParams.push_back(vectorizeSIMDType(sType->getElementType(i), vectorizationFactor));
      }
      return StructType::get(oldType->getContext(), newParams, sType->isPacked());
    }

  default:
    {
      errs() << "\nERROR: only arguments of type float, int, pointer, "
        << "array or struct can be vectorized, not '"
        << *oldType << "'!\n";
      return 0;
    }
  }
}

void
deleteTree(Instruction* inst, SetVector<Instruction*>& deleteVec)
{
  assert (inst);

  for (Instruction::use_iterator U=inst->use_begin(), UE=inst->use_end(); U!=UE; ++U)
  {
    deleteTree(cast<Instruction>(*U), deleteVec);
  }

  // TODO: Handle branch/switch/return.
  if (isa<BranchInst>(inst) ||
      isa<SwitchInst>(inst) ||
      isa<ReturnInst>(inst))
  {
    assert (false && "deleteTree for branch/switch/return not implemented!");
  }

  deleteVec.insert(inst);
}

bool
isInfluencingControlFlow(Instruction* inst)
{
  assert (inst);

  for (Instruction::use_iterator U=inst->use_begin(), UE=inst->use_end(); U!=UE; ++U)
  {
    Instruction* useI = cast<Instruction>(*U);
    if (isInfluencingControlFlow(useI)) return true;
  }

  return isa<BranchInst>(inst) ||
      isa<SwitchInst>(inst) ||
      isa<ReturnInst>(inst);
}

void
replaceUpdateOpUses(Value*              mappedOp,
                    Value*              replaceOp,
                    Instruction*        currentUpdateOp,
                    ValueToValueMapTy&  valueMap,
                    const RedUpMapType& updates)
{
  assert (mappedOp && replaceOp && currentUpdateOp);
  DEBUG_NOISE_WFV( outs() << "begin replaceUpdateOpUses()\n"; );
  DEBUG_NOISE_WFV( outs() << "  mappedOp : " << *mappedOp << "\n"; );
  DEBUG_NOISE_WFV( outs() << "  replaceOp: " << *replaceOp << "\n"; );
  SmallVector<Instruction*, 2> replaceVec;
  for (Value::use_iterator U=mappedOp->use_begin(), UE=mappedOp->use_end(); U!=UE; ++U)
  {
    Instruction* useI = cast<Instruction>(*U);
    DEBUG_NOISE_WFV( outs() << "    useI: " << *useI << "\n"; );
    // If the use is a different update operation, we must not replace it.
    bool isOtherUpdateOp = false;
    for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
    {
      const ReductionUpdate& redUp = *it->second;
      Instruction* mappedUp2 = cast<Instruction>(valueMap[redUp.mOperation]);
      if (useI == currentUpdateOp) continue;  // The current update op has to be modified.
      if (useI != mappedUp2) continue;        // Others should remain untouched.
      isOtherUpdateOp = true;
      break;
    }
    DEBUG_NOISE_WFV( if (isOtherUpdateOp) outs() << "    is other opdate op!\n"; );
    if (isOtherUpdateOp) continue;

    // If the use is not in the valueMap, it belongs to a different iteration of i,
    // so we must not replace it.
    ValueToValueMapTy::iterator it=valueMap.begin();
    for (ValueToValueMapTy::iterator E=valueMap.end(); it!=E; ++it)
    {
      Value* mappedVal = it->second;
      if (mappedVal != useI) continue;
      break;
    }
    DEBUG_NOISE_WFV( if (it == valueMap.end()) outs() << "    has no value mapping!\n"; );
    if (it == valueMap.end()) continue;

    // Otherwise, it has to be replaced.
    replaceVec.push_back(useI);
  }

  for (SmallVector<Instruction*, 2>::iterator it=replaceVec.begin(),
       E=replaceVec.end(); it!=E; ++it)
  {
    (*it)->replaceUsesOfWith(mappedOp, replaceOp);
  }
  DEBUG_NOISE_WFV( outs() << "end replaceUpdateOpUses()\n"; );
}

// - Generate function F_R_SIMD that performs all updates in a vector context:
//   - Return type is the scalar return type of P.
//   - One input parameter for P.
//   - One input parameter per "other operand" per "update operation".
//   - One output parameter per "update operation" that has at least one "result user".
// TODO: It would be beneficial to have WFV vectorization analysis info here.
void
generateSIMDReductionFunction(ReductionVariable&   redVar,
                              const unsigned       vectorizationFactor,
                              Function*            loopBodyFn,
                              const RedVarVecType& redVars)
{
  Type* type = redVar.mPhi->getType();
  LLVMContext& context = type->getContext();

  SmallVector<Type*, 4>  params;
  SmallVector<Twine, 4>  names;
  SmallVector<Value*, 4> values;

  // Add input parameter for P.
  params.push_back(type);
  names.push_back(redVar.mPhiArg->hasName() ? redVar.mPhiArg->getName() : "phi");
  values.push_back(redVar.mPhiArg);

  // Add input parameters for "other operands".
  const RedUpMapType& updates = *redVar.mUpdates;
  for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
  {
    const ReductionUpdate& redUp = *it->second;
    const OtherOperandsVec& otherOperands = *redUp.mOtherOperands;
    for (OtherOperandsVec::const_iterator it2=otherOperands.begin(),
         E2=otherOperands.end(); it2!=E2; ++it2)
    {
      Value* operand = *it2;
      Type* simdType = vectorizeSIMDType(operand->getType(), vectorizationFactor);
      params.push_back(simdType);
      names.push_back(operand->hasName() ? operand->getName() : "otherOp");
      values.push_back(operand);
    }
  }

  // Add output parameter for final result.
  params.push_back(PointerType::getUnqual(type));
  names.push_back("result.ptr");
  values.push_back(redVar.mOutArg);

  // Add output parameters for "result users".
  const unsigned firstResultUserPtrIndex = params.size();
  for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
  {
    const ReductionUpdate& redUp = *it->second;
    if (redUp.mResultUsers->empty()) continue;
    Type* updateType = redUp.mOperation->getType();
    Type* simdType = vectorizeSIMDType(updateType, vectorizationFactor);
    params.push_back(PointerType::getUnqual(simdType));
    names.push_back("update.result.ptr");
    values.push_back(NULL);
  }

  // Add dummy mask parameter (unused, only required for WFV to prevent splitting).
  Type* maskTy = vectorizeSIMDType(Type::getInt1Ty(context), vectorizationFactor);
  params.push_back(maskTy);
  names.push_back("");
  values.push_back(NULL); // No value required.

  FunctionType* fType = FunctionType::get(Type::getVoidTy(context), params, false);

  Module* mod = redVar.mPhi->getParent()->getParent()->getParent();
  Function* simdRedFn = Function::Create(fType, Function::ExternalLinkage, "red_fn_SIMD", mod);
  redVar.mReductionFnSIMD = simdRedFn;

  SmallVector<Twine, 4>::const_iterator N = names.begin();
  for (Function::arg_iterator A = simdRedFn->arg_begin(),
      AE = simdRedFn->arg_end(); A != AE; ++A, ++N)
  {
      A->setName(*N);
  }

  DEBUG_NOISE_WFV( outs() << "SIMD reduction function signature: " << *simdRedFn << "\n"; );

  //-------------------------------------------------------------------------//
  // Generate code for the SIMD reduction from the original function.
  //-------------------------------------------------------------------------//

  // First, specify which arguments of the old function map to arguments
  // of the new one. By leaving all others unspecified, the corresponding
  // code is dead and should be removed automatically.
  // To this end, we iterate over the call to the scalar reduction function.
  // NOTE: Since we put all "other operands" into local memory, these
  //       arguments (if any) never map directly. Thus, the only remaining
  //       argument is the phi arg.
  ValueToValueMapTy valueMap;
  ValueToValueMapTy replaceMap;

  // Initialize all parameters with "undef" first.
  // Otherwise, all arguments of loopBodyFn that are not part of
  // any reduction will not have any mapping.
  for (Function::const_arg_iterator A = loopBodyFn->arg_begin(),
      AE = loopBodyFn->arg_end(); A != AE; ++A)
  {
    valueMap[A] = UndefValue::get(A->getType());
  }

  // Map the collected values (operands of the reduction) to
  // the arguments of simdRedFn.
  // This covers the mapping of the phi and all otherOps that are defined
  // outside the loop (so they were arguments after extraction already).
  // OtherOps that are defined in the body are handled below.
  // Non-uniform otherOps are also handled below.
  // NOTE: This essentially only fills valueMap/replaceMap for use in the loop.
  SmallVector<Value*, 4>::iterator V = values.begin();
  for (Function::arg_iterator AR = simdRedFn->arg_begin(),
      ARE = simdRedFn->arg_end(); AR != ARE; ++AR, ++V)
  {
    Value* value = *V;
    if (!value) continue;
    assert (!value ||
            AR->getType() == value->getType() ||
            (AR->getType()->isVectorTy() &&
             AR->getType()->getVectorElementType() == value->getType()));
    // We only add mappings for arguments of the original function.
    // (This is not strictly necessary since CloneFunctionInto overwrites the information anyway).
    if (isa<Argument>(value))
    {
      DEBUG_NOISE_WFV( outs() << "original arg: " << *value << "\n"; );
      DEBUG_NOISE_WFV( outs() << "mapped arg  : " << *AR << "\n"; );
      valueMap[value] = AR;
    }
    replaceMap[value] = AR;
  }

  //-------------------------------------------------------------------------//
  // Now, clone the function W times, connect the reduction outputs to the
  // inputs of the next iteration, and remove all code that is not required
  // for the reduction.
  //-------------------------------------------------------------------------//
  Value* lastIterOut = NULL;
  BasicBlock* lastExitBB = NULL;
  SmallVector<AllocaInst*, 2> intermediateResults;

  for (unsigned i=0; i<vectorizationFactor; ++i)
  {
    ConstantInt* c = ConstantInt::get(context, APInt(32, i));

    // Set this iteration's "input" (the reference to the phi arg) to the
    // "output" of the last iteration.
    // First iteration: already done by mapping phi to argument.
    if (i != 0)
    {
      valueMap[redVar.mPhiArg] = lastIterOut;
    }

    //------------------------------------------------------------------------//
    // Clone the function.
    // It is desired that some operations afterwards still have references to "undef":
    // These are operations that are not required anymore since their result - if
    // used at all in the SCC - is replaced by one of the "inputs" of the last iteration.
    SmallVector<ReturnInst*, 2> returns;
    ClonedCodeInfo              clonedFInfo;
    const char*                 nameSuffix = ".";
    CloneFunctionInto(simdRedFn,
                      loopBodyFn,
                      valueMap,
                      false,
                      returns,
                      nameSuffix,
                      &clonedFInfo);

    //------------------------------------------------------------------------//
    // Replace other operands that are defined in the loop body by the respective arguments.
    // This kills the corresponding code in the reduction function.
    SmallPtrSet<Instruction*, 2> deleteSet;
    for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
    {
      const ReductionUpdate& redUp = *it->second;
      Instruction* mappedUp = cast<Instruction>(valueMap[redUp.mOperation]);
      DEBUG_NOISE_WFV( outs() << "mappedUp: " << *mappedUp << "\n"; );
      const OtherOperandsVec& otherOperands = *redUp.mOtherOperands;
      for (OtherOperandsVec::const_iterator it2=otherOperands.begin(),
           E2=otherOperands.end(); it2!=E2; ++it2)
      {
        Value* operand = *it2;
        Value* mappedOp = valueMap[operand];
        Value* replaceOp = replaceMap[operand];
        DEBUG_NOISE_WFV( outs() << "  operand  : " << *operand << "\n"; );
        DEBUG_NOISE_WFV( outs() << "  mappedOp : " << *mappedOp << "\n"; );
        DEBUG_NOISE_WFV( outs() << "  replaceOp: " << *replaceOp << "\n"; );

        if (isa<Argument>(mappedOp))
        {
          // Fix other operands that are vectorized function arguments.
          if (!replaceOp->getType()->isVectorTy()) continue;

          // TODO: For more complex types, we have to use generic extract function (-> WFV).
          Instruction* insertBefore = simdRedFn->getEntryBlock().getFirstNonPHI();
          replaceOp = ExtractElementInst::Create(replaceOp, c, "", insertBefore);
          // We must not replace all uses of mappedOp, since this would replace
          // uses of previous iterations of i and other uses of this "other operand" as well.
          // We have to replace all uses in the code of this iteration of i that are
          // not other update operations.
          replaceUpdateOpUses(mappedOp, replaceOp, mappedUp, valueMap, updates);
        }
        else
        {
          // If the operand is a vector, we have to extract the element that
          // corresponds to the current iteration.
          if (replaceOp->getType()->isVectorTy())
          {
            // TODO: For more complex types, we have to use generic extract function (-> WFV).
            Instruction* insertBefore;
            if (Instruction* mappedOpI = dyn_cast<Instruction>(mappedOp))
            {
              insertBefore = mappedOpI;
            }
            else
            {
              insertBefore = simdRedFn->getEntryBlock().getFirstNonPHI();
            }
            Instruction* ext = ExtractElementInst::Create(replaceOp, c, "", insertBefore);
            insertBefore->moveBefore(ext);
            replaceOp = ext;
          }
          // We must not replace all uses of mappedOp, since this would replace
          // other uses of this "other operand" as well.
          // We have to replace all uses in the code of this iteration of i that are
          // not other update operations.
          replaceUpdateOpUses(mappedOp, replaceOp, mappedUp, valueMap, updates);
          if (Instruction* inst = dyn_cast<Instruction>(mappedOp))
          {
            deleteSet.insert(inst);
          }
        }
      }
    }

    bool changed = true;
    while (!changed)
    {
      changed = false;
      for (SmallPtrSet<Instruction*, 2>::iterator it=deleteSet.begin(),
           E=deleteSet.end(); it!=E; ++it)
      {
        Instruction* inst = *it;
        if (!inst->use_empty()) continue;
        inst->eraseFromParent();
        changed = true;
      }
    }

    //------------------------------------------------------------------------//
    // Replace return by a branch to the latest entry block.
    // First iteration: do nothing :p.
    if (i != 0)
    {
      assert (isa<ReturnInst>(lastExitBB->getTerminator()));
      BasicBlock* entryBB = cast<BasicBlock>(valueMap[&loopBodyFn->getEntryBlock()]);
      BranchInst::Create(entryBB, lastExitBB->getTerminator());
      lastExitBB->getTerminator()->eraseFromParent();
    }

    //------------------------------------------------------------------------//
    // This iteration's "output" is the "input" of the next clone.
    assert (valueMap[redVar.mStoreBack]);
    StoreInst* storeBack = cast<StoreInst>(valueMap[redVar.mStoreBack]);
    lastIterOut = storeBack->getValueOperand();
    lastExitBB = storeBack->getParent();

    //------------------------------------------------------------------------//
    // Remove the store operation (unless this is the last iteration).
    if (i+1 != vectorizationFactor)
    {
      storeBack->eraseFromParent();
    }

    //------------------------------------------------------------------------//
    // Delete all call and store operations that are not part of this reduction.
    // This should kill all code that is not required.
    DEBUG_NOISE_WFV( outs() << "\nErasing unnecessary code from SIMD reduction function...\n"; );
    SetVector<Instruction*> deleteVec2;
    for (Function::iterator BB=simdRedFn->begin(), BBE=simdRedFn->end(); BB!=BBE; ++BB)
    {
      for (BasicBlock::iterator I=BB->begin(), IE=BB->end(); I!=IE; ++I)
      {
        if (!isa<StoreInst>(I) && !isa<CallInst>(I)) continue;
        deleteTree(I, deleteVec2);
      }
    }

    DEBUG_NOISE_WFV( outs() << "  deleting unrelated calls/stores...\n"; );
    for (unsigned j=0, je=deleteVec2.size(); j<je; ++j)
    {
      // Don't delete instructions that also belong to the current SCC.
      bool isSCCUse = false;
      for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
      {
        const ReductionUpdate& redUp = *it->second;
        if (deleteVec2[j] != valueMap[redUp.mOperation]) continue;
        isSCCUse = true;
      }
      if (isSCCUse) continue;

      // Don't delete the storeback operation.
      if (StoreInst* store = dyn_cast<StoreInst>(deleteVec2[j]))
      {
        if (store->getPointerOperand() == valueMap[redVar.mOutArg]) continue;
      }

      // Don't delete instructions whose parent was not deleted (due to the continues above).
      if (!deleteVec2[j]->use_empty()) continue;

      DEBUG_NOISE_WFV( outs() << "    deleting instruction: " << *deleteVec2[j] << "\n"; );
      deleteVec2[j]->eraseFromParent();
    }

    DEBUG_NOISE_WFV( outs() << "Erasing of unnecessary code done.\n\n"; );

    //------------------------------------------------------------------------//
    //------------------------------------------------------------------------//
    // Finally, we need to update the vectors of all intermediate results that are used
    // outside of the SCC.
    if (i == 0)
    {
      // Generate alloca/store/load for intermediate results (rely on later SROA
      // phase to circumvent control-flow related issues).
      // We can only do this after the first code has been cloned, otherwise there
      // is no insertion point for the allocas :).
      for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
      {
        const ReductionUpdate& redUp = *it->second;
        if (redUp.mResultUsers->empty()) continue;
        Type* updateType = redUp.mOperation->getType();
        Type* vecType = vectorizeSIMDType(updateType, vectorizationFactor);
        // Create alloca.
        Instruction* allocaInsertPos = simdRedFn->getEntryBlock().getFirstNonPHI();
        AllocaInst* alloca = new AllocaInst(vecType,
                                            "red.intermediate.storage",
                                            allocaInsertPos);
        intermediateResults.push_back(alloca);
      }
    }

    unsigned intermIdx = 0;
    for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
    {
      const ReductionUpdate& redUp = *it->second;
      if (redUp.mResultUsers->empty()) continue;

      Instruction* mappedUp = cast<Instruction>(valueMap[redUp.mOperation]);
      AllocaInst* intermResPtr = intermediateResults[intermIdx];

      // First, if this is not the first iteration, load the last value.
      Value* intermRes = UndefValue::get(intermResPtr->getType()->getPointerElementType());
      if (i != 0)
      {
        intermRes = new LoadInst(intermResPtr, "red.intermediate.reload", mappedUp);
        mappedUp->moveBefore(cast<Instruction>(intermRes)); // Not necessary.
      }

      // TODO: For more complex types, we have to use generic insert function (-> WFV).
      InsertElementInst* newIntermRes = InsertElementInst::Create(intermRes,
                                                                  mappedUp,
                                                                  c,
                                                                  "",
                                                                  mappedUp);
      mappedUp->moveBefore(newIntermRes);
      if (Instruction* intermResI = dyn_cast<Instruction>(intermRes))
      {
        intermResI->moveBefore(newIntermRes);
      }

      // Store updated value.
      StoreInst* store = new StoreInst(newIntermRes, intermResPtr, newIntermRes);
      newIntermRes->moveBefore(store);

      // In the last iteration, the intermediate results have to be stored
      // to their corresponding output arguments.
      // We generate an additional store here to make sure SROA replaces the
      // others by SSA values.
      if (i+1 == vectorizationFactor)
      {
        LoadInst* finalRes = new LoadInst(intermResPtr, "red.intermediate.reload", store);
        store->moveBefore(finalRes);
        Function::arg_iterator A = simdRedFn->arg_begin();
        std::advance(A, firstResultUserPtrIndex+intermIdx);
        StoreInst* store2 = new StoreInst(finalRes, A, finalRes);
        finalRes->moveBefore(store2);
      }

      ++intermIdx;
    }
  } // Iterate W times.
}

} // unnamed namespace

// TODO: Make assertions return gracefully instead.
bool
NoiseWFVWrapper::runWFV(Function* noiseFn)
{
  assert (noiseFn);

  //-------------------------------------------------------------------------//
  // We must not vectorize the entire function but only the loop body.
  // Thus, we first have to extract the body into a new function.
  //-------------------------------------------------------------------------//
  // NOTE: We want to allow arbitrary optimizations before wfv, but at the
  //       same time rely on being able to extract those parts of the block
  //       that were the body (without induction variable increment, loop
  //       condition test, etc.).
  //       If one of the previous optimizations does not allow us to extract
  //       the loop body, we have to live with it for now.
  //-------------------------------------------------------------------------//

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
          "vectorization of non-simplified loop not supported!");
  assert (loop->isLoopSimplifyForm() &&
          "vectorization of non-simplified loop not supported!");
  assert (loop->isLCSSAForm(*mDomTree) &&
          "vectorization of loops not in LCSSA form not supported!");

  assert (loop->getNumBackEdges() == 1 &&
          "vectorization of loops with multiple back edges not supported!");
  assert (exitBB && exitingBB &&
          "vectorization of loops with multiple exits not supported!");

  //-------------------------------------------------------------------------//

  // Get loop induction variable phi.
  PHINode* indVarPhi = loop->getCanonicalInductionVariable();
  if (!indVarPhi)
  {
    for (BasicBlock::iterator I=headerBB->begin(), IE=headerBB->end(); I!=IE; ++I)
    {
      if (!isa<PHINode>(I)) continue;
      PHINode* phi = cast<PHINode>(I);
      Type* type = phi->getType();

      if (!type->isIntegerTy() &&
          //!type->isFloatingPointTy() && // can't use getSCEV.
          !type->isPointerTy())
      {
        continue;
      }

      const SCEV* scevPhi = mSCEV->getSCEV(phi);
      if (!isa<SCEVAddRecExpr>(scevPhi)) continue;

      const SCEVAddRecExpr* addExpr = cast<SCEVAddRecExpr>(scevPhi);
      const SCEV* stepRec = addExpr->getStepRecurrence(*mSCEV);

      if (type->isIntegerTy() && stepRec->isAllOnesValue())
      {
        errs() << "WARNING: vectorization of loop with reverse induction not implemented!\n";
        continue;
      }

      if (!stepRec->isOne()) continue;

      if (type->isPointerTy())
      {
        errs() << "WARNING: vectorization of loop with pointer induction not implemented!\n";
        continue;
      }

      if (indVarPhi)
      {
        errs() << "WARNING: vectorization of loop with multiple "
            << "induction variables not implemented!\n";
        continue;
      }

      indVarPhi = phi;
    }
  }

  assert (indVarPhi &&
          "vectorization of loops without canonical induction variable not supported!");
  assert (isa<Instruction>(indVarPhi->getIncomingValueForBlock(latchBB)) &&
          "expected induction variable update value to be an instruction!");
  Instruction* indVarUpdate = cast<Instruction>(indVarPhi->getIncomingValueForBlock(latchBB));
  assert (indVarUpdate->getParent() == latchBB &&
          "expected induction variable update operation in latch block!");

  // TODO: These should return gracefully.
  // TODO: These should eventually be replaced by generation of fixup code.
  assert (indVarUpdate->getOpcode() == Instruction::Add &&
          "vectorization of loop with induction variable update operation that is no integer addition not supported!");
  assert ((indVarUpdate->getOperand(0) == indVarPhi ||
           indVarUpdate->getOperand(1) == indVarPhi) &&
          "vectorization of loop with induction variable update operation that is no simple increment not supported!");
  assert ((indVarUpdate->getOperand(0) == ConstantInt::get(indVarUpdate->getType(), 1U) ||
           indVarUpdate->getOperand(1) == ConstantInt::get(indVarUpdate->getType(), 1U)) &&
          "vectorization of loop with induction variable update operation that is no simple increment not supported!");

  // Do some sanity checks to test assumptions about our construction.
  assert (preheaderBB == &noiseFn->getEntryBlock());
  assert (preheaderBB->getTerminator()->getNumSuccessors() == 1);
  assert (headerBB == preheaderBB->getTerminator()->getSuccessor(0));
  assert (isa<PHINode>(headerBB->begin()));
  assert (cast<PHINode>(headerBB->begin())->getNumIncomingValues() == 2);

  //-------------------------------------------------------------------------//

  // Identify reduction variables and their operations.
  // TODO: Make sure there is no interference between reduction variables.
  // TODO: There's a problem with store-load chains that we don't detect
  //       to be part of the SCC! Make sure we are conservative with that.
  RedVarVecType redVars;
  collectReductionVariables(redVars, indVarPhi, *loop, *mDomTree);

  // Print info & check sanity.
  assert (redVars.empty() || noiseFn == (*redVars.begin())->mPhi->getParent()->getParent());
  DEBUG_NOISE_WFV( DEBUG_NOISE_WFV( outs() << "\nfunction:" << *noiseFn << "\n"; ); );
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    assert (redVar.mPhi && redVar.mStartVal && redVar.mUpdates);
    assert (!redVar.mResultUser ||
            redVar.mPhi == redVar.mResultUser->getIncomingValueForBlock(loop->getExitingBlock()));

    DEBUG_NOISE_WFV( outs() << "reduction var phi  P: " << *redVar.mPhi << "\n"; );
    DEBUG_NOISE_WFV( if (redVar.mCanOptimizeWithVector) outs() << "  can be vectorized!\n";);
    DEBUG_NOISE_WFV( outs() << "  start value      S: " << *redVar.mStartVal << "\n"; );
    DEBUG_NOISE_WFV(
      if (redVar.mResultUser) outs() << "  reduction result R: " << *redVar.mResultUser << "\n";
      else outs() << "  reduction result R: not available\n";
    );

    assert (redVar.mPhi->getType() == redVar.mStartVal->getType());
    assert (!redVar.mResultUser || redVar.mPhi->getType() == redVar.mResultUser->getType());

    DEBUG_NOISE_WFV(
      const RedUpMapType& updates = *redVar.mUpdates;
      for (RedUpMapType::const_iterator it2=updates.begin(), E2=updates.end(); it2!=E2; ++it2)
      {
        ReductionUpdate& redUp = *it2->second;
        outs() << "  update operation O: " << *redUp.mOperation << "\n";
        if (!redUp.mResultUsers->empty()) outs() << "    has result user(s).\n";
      }
    );
  }

  // TODO: Make sure we stop here already if there are reductions we can't handle.

  //-------------------------------------------------------------------------//

  assert (mSCEV->hasLoopInvariantBackedgeTakenCount(loop) &&
          "vectorization of loops without loop-invariant backedge count not supported!");

  const SCEV* scevLoopCountMinus1 = mSCEV->getExitCount(loop, exitingBB);
  assert (scevLoopCountMinus1 != mSCEV->getCouldNotCompute() && "invalid loop count found!");
#if 0
  const SCEV* scevConst1 = mSCEV->getConstant(scevLoopCountMinus1->getType(), 1);
  const SCEV* scevLoopCount = mSCEV->getAddExpr(scevLoopCountMinus1, scevConst1);
#else
  const SCEV* scevLoopCount = scevLoopCountMinus1;
#endif
  DEBUG_NOISE_WFV( outs() << "loop count expr: " << *scevLoopCount << "\n"; );
  SCEVExpander expander(*mSCEV, "");
  Value* loopCount = expander.expandCodeFor(scevLoopCount,
                                            scevLoopCount->getType(),
                                            preheaderBB->getTerminator());
  DEBUG_NOISE_WFV( outs() << "loop count     : " << *loopCount << "\n"; );

  loopCount = ZExtInst::CreateZExtOrBitCast(loopCount,
                                            indVarPhi->getType(),
                                            "",
                                            preheaderBB->getTerminator());

  Value* startVal = indVarPhi->getIncomingValueForBlock(preheaderBB);
  DEBUG_NOISE_WFV( outs() << "start val      : " << *startVal << "\n"; );

  // Get the end value.
  // Optimize for the case where the end value is a constant.
  assert (isa<BranchInst>(exitingBB->getTerminator()));
  BranchInst* exitBr = cast<BranchInst>(exitingBB->getTerminator());
  assert (exitBr->isConditional());
  assert (isa<CmpInst>(exitBr->getCondition()) &&
          "vectorization of loop with non-compare-inst exit condition not supported!");
  CmpInst* exitCond = cast<CmpInst>(exitBr->getCondition());
  Value* endVal = exitCond->getOperand(1);
  if (!isa<Constant>(endVal))
  {
    const SCEV* scevLoopCountZExt = mSCEV->getSCEV(loopCount);
    const SCEV* scevLoopStartVal = mSCEV->getSCEV(startVal);
    const SCEV* scevLoopEndVal = mSCEV->getAddExpr(scevLoopStartVal, scevLoopCountZExt);
    endVal = expander.expandCodeFor(scevLoopEndVal,
                                    scevLoopEndVal->getType(),
                                    preheaderBB->getTerminator());
  }
  DEBUG_NOISE_WFV( outs() << "end val        : " << *endVal << "\n"; );

  Constant* constW = ConstantInt::get(indVarPhi->getType(), mVectorizationFactor, false);

  //-------------------------------------------------------------------------//

  // If the loop induction variable does not start at a constant that is
  // a multiple of W, we have to create a first loop that iterates until
  // the induction variable is aligned.
  // NOTE: This is only required if we have loads/stores that are consecutive
  //       and aligned. We only know this after vectorization analysis, though.
  bool needScalarStartLoop = true;
  if (ConstantInt* c = dyn_cast<ConstantInt>(startVal))
  {
    uint64_t val = c->getLimitedValue();
    if (val % mVectorizationFactor == 0) needScalarStartLoop = false;
  }
  else if (ConstantFP* c = dyn_cast<ConstantFP>(startVal))
  {
    double val = c->getValueAPF().convertToDouble();
    if (fmod(val, (double)mVectorizationFactor) == 0.0) needScalarStartLoop = false;
  }

  // If the loop end value is not a multiple of W, we have to create an end
  // loop that iterates until the end value is hit.
  bool needScalarEndLoop = true;
  if (ConstantInt* c = dyn_cast<ConstantInt>(endVal))
  {
    uint64_t val = c->getLimitedValue();
    if (val % mVectorizationFactor == 0) needScalarEndLoop = false;
  }
  else if (ConstantFP* c = dyn_cast<ConstantFP>(endVal))
  {
    double val = c->getValueAPF().convertToDouble();
    if (fmod(val, (double)mVectorizationFactor) == 0.0) needScalarEndLoop = false;
  }

  //-------------------------------------------------------------------------//

  // Clone the loop to create start/end loops if necessary.
  // We have to clone before we start adjusting values etc. for the SIMD loop.
  ValueToValueMapTy startLoopValueMap;
  ValueToValueMapTy endLoopValueMap;
  Loop* scalarStartLoop = needScalarStartLoop ?
      cloneLoop(loop, startLoopValueMap, mLoopInfo) : 0;
  Loop* scalarEndLoop = needScalarEndLoop ?
      cloneLoop(loop, endLoopValueMap, mLoopInfo) : 0;

  //-------------------------------------------------------------------------//

  Value* startLoopIndVar = startVal;
  if (needScalarStartLoop)
  {
    DEBUG_NOISE_WFV( outs() << "scalarStartLoop: " << *scalarStartLoop << "\n"; );

    // Get start/end for scalar start loop:
    // - start = startVal (no change to cloned loop required)
    // - end   = startVal + (W - (startVal % W)
    //           13       + (4 - (13       % 4) = 16
    Value* firstEndVal = BinaryOperator::Create(Instruction::URem,
                                                startVal,
                                                constW,
                                                "",
                                                preheaderBB->getTerminator());
    firstEndVal = BinaryOperator::Create(Instruction::Sub,
                                         constW,
                                         firstEndVal,
                                         "",
                                         preheaderBB->getTerminator());
    firstEndVal = BinaryOperator::Create(Instruction::Add,
                                         startVal,
                                         firstEndVal,
                                         "scalarEndIdx",
                                         preheaderBB->getTerminator());

    // Tie loose ends of cloning.
    BasicBlock* startPreheaderBB = cast<BasicBlock>(startLoopValueMap[preheaderBB]);
    BasicBlock* startExitBB = scalarStartLoop->getUniqueExitBlock();
    TerminatorInst* preheaderTerm = preheaderBB->getTerminator();
    TerminatorInst* startLoopExitTerm = startExitBB->getTerminator();
    // 1. Branch from preheader to start loop preheader.
    BranchInst::Create(startPreheaderBB, preheaderBB);
    // 2. Move terminator of preheader to start loop exit.
    preheaderTerm->moveBefore(startLoopExitTerm);
    // 3. Erase dummy terminator.
    startLoopExitTerm->eraseFromParent();

    // Incoming value of induction phi does not have to be changed.
    // However, we have to store the phi since it will be the input value of the
    // SIMD loop induction variable.
    startLoopIndVar = cast<PHINode>(startLoopValueMap[indVarPhi]);

    // Adjust exit condition.
    BasicBlock* startExitingBB = cast<BasicBlock>(startLoopValueMap[exitingBB]);
    assert (isa<BranchInst>(startExitingBB->getTerminator()));
    BranchInst* exitBr = cast<BranchInst>(startExitingBB->getTerminator());
    assert (exitBr->isConditional());
    assert (isa<CmpInst>(exitBr->getCondition()) &&
            "vectorization of loop with non-compare-inst exit condition not supported!");
    CmpInst* exitCond = cast<CmpInst>(exitBr->getCondition());

    CmpInst* newExitCond = indVarPhi->getType()->isIntegerTy() ?
        ICmpInst::Create(Instruction::ICmp, ICmpInst::ICMP_SLT, startLoopIndVar, firstEndVal, "", exitCond) :
        FCmpInst::Create(Instruction::FCmp, FCmpInst::FCMP_OLT, startLoopIndVar, firstEndVal, "", exitCond);

    exitCond->replaceAllUsesWith(newExitCond);
  }

  //-------------------------------------------------------------------------//

  // Get start/end for vectorized loop:
  // - start = start loop induction phi
  // - end   = endVal - (endVal % W)
  Value* wfvStartVal = startLoopIndVar;
  if (endVal->getType() != indVarPhi->getType())
  {
    endVal = ZExtInst::CreateZExtOrBitCast(endVal,
                                           indVarPhi->getType(),
                                           "",
                                           preheaderBB->getTerminator());
  }
  Value* tmpRem    = BinaryOperator::Create(Instruction::URem,
                                              endVal,
                                              constW,
                                              "",
                                              preheaderBB->getTerminator());
  Value* wfvEndVal = BinaryOperator::Create(Instruction::Sub,
                                            endVal,
                                            tmpRem,
                                            "wfvEndIdx",
                                            preheaderBB->getTerminator());
  Value* wfvLoopIndVar = indVarPhi;

  // Adjust incoming value of induction variable phi (if start loop exists, otherwise no effect).
  const unsigned preIdx = indVarPhi->getBasicBlockIndex(preheaderBB);
  indVarPhi->setIncomingValue(preIdx, wfvStartVal);

  // Adjust incoming blocks of phis in header if there is a scalar start loop.
  if (needScalarStartLoop)
  {
    BasicBlock* mappedExitBB = cast<BasicBlock>(startLoopValueMap[exitBB]);
    for (BasicBlock::iterator I=headerBB->begin(), IE=headerBB->end(); I!=IE; ++I)
    {
      if (!isa<PHINode>(I)) break;
      PHINode* phi = cast<PHINode>(I);
      const unsigned preIdx = phi->getBasicBlockIndex(preheaderBB);
      phi->setIncomingBlock(preIdx, mappedExitBB);
    }
  }

  // Adjust exit condition.
  // TODO: We may have to replace *all* possible uses of the end value!
  CmpInst* newExitCond = indVarPhi->getType()->isIntegerTy() ?
      ICmpInst::Create(Instruction::ICmp, ICmpInst::ICMP_SLT, indVarPhi, wfvEndVal, "", exitCond) :
      FCmpInst::Create(Instruction::FCmp, FCmpInst::FCMP_OLT, indVarPhi, wfvEndVal, "", exitCond);

  exitCond->replaceAllUsesWith(newExitCond);

  // Rewire inputs of SIMD loop from outputs of scalar start loop (if any).
  // These can only be reductions.
  if (needScalarStartLoop)
  {
    // The loop has a new preheader.
    BasicBlock* newPreheaderBB = loop->getLoopPreheader();
    for (BasicBlock::iterator I=exitBB->begin(), IE=exitBB->end(); I!=IE; ++I)
    {
      if (!isa<PHINode>(I)) break;
      PHINode* simdLoopRedRes = cast<PHINode>(I);
      assert (simdLoopRedRes->getNumIncomingValues() == 1 && "not in LCSSA?!");
      // Get the reduction phi (the only operand due to LCSSA).
      assert (isa<PHINode>(simdLoopRedRes->getIncomingValue(0)));
      PHINode* simdLoopRedPhi = cast<PHINode>(simdLoopRedRes->getIncomingValue(0));
      // Get the result of the start loop.
      PHINode* startLoopRedRes = cast<PHINode>(startLoopValueMap[simdLoopRedRes]);
      // Now, modify the phi in the header of the SIMD loop.
      // Replace the incoming value from the preheader of the SIMD loop by the result.
      Value* phIncVal = simdLoopRedPhi->getIncomingValueForBlock(newPreheaderBB);
      simdLoopRedPhi->replaceUsesOfWith(phIncVal, startLoopRedRes);
    }
  }

  //-------------------------------------------------------------------------//

  if (needScalarEndLoop)
  {
    DEBUG_NOISE_WFV( outs() << "scalarEndLoop: " << *scalarEndLoop << "\n"; );

    // Get start/end for scalar end loop:
    // - start = vectorized loop induction phi
    // - end   = endVal (no change to cloned loop required)
    Value* thirdStartVal = wfvLoopIndVar;

    // Tie loose ends of cloning.
    BasicBlock* endPreheaderBB = cast<BasicBlock>(endLoopValueMap[preheaderBB]);
    BasicBlock* endExitBB = scalarEndLoop->getUniqueExitBlock();
    TerminatorInst* simdTerm = exitBB->getTerminator();
    TerminatorInst* endLoopExitTerm = endExitBB->getTerminator();
    // 1. Branch from SIMD loop exit to end loop preheader.
    BranchInst::Create(endPreheaderBB, exitBB);
    // 2. Move terminator of SIMD loop exit to end loop exit.
    simdTerm->moveBefore(endLoopExitTerm);
    // 3. Erase dummy terminator.
    endLoopExitTerm->eraseFromParent();

    // Set incoming value of induction phi to the correct start value.
    PHINode* endIndVarPhi = cast<PHINode>(endLoopValueMap[indVarPhi]);
    const unsigned preIdx = endIndVarPhi->getBasicBlockIndex(endPreheaderBB);
    endIndVarPhi->setIncomingValue(preIdx, thirdStartVal);

    // Exit condition does not have to be changed.

    // Rewire inputs of scalar end loop from outputs of SIMD loop (if any).
    // These can only be reductions.
    for (BasicBlock::iterator I=exitBB->begin(), IE=exitBB->end(); I!=IE; ++I)
    {
      if (!isa<PHINode>(I)) break;
      PHINode* simdLoopRedRes = cast<PHINode>(I);
      assert (simdLoopRedRes->getNumIncomingValues() == 1 && "not in LCSSA?!");
      // Get the result of the start loop.
      PHINode* endLoopRedRes = cast<PHINode>(endLoopValueMap[simdLoopRedRes]);
      // Get the reduction phi (the only operand due to LCSSA).
      assert (isa<PHINode>(endLoopRedRes->getIncomingValue(0)));
      PHINode* endLoopRedPhi = cast<PHINode>(endLoopRedRes->getIncomingValue(0));
      // Now, modify the phi in the header of the SIMD loop.
      // Replace the incoming value from the preheader of the SIMD loop by the result.
      Value* phIncVal = endLoopRedPhi->getIncomingValueForBlock(endPreheaderBB);
      endLoopRedPhi->replaceUsesOfWith(phIncVal, simdLoopRedRes);
    }

    // Rewire outputs of this function to the code behind the loop.
    // Outputs are all those values that have a phi in the exit block (LCSSA).
    // This also requires to move all store operations in the exit block.
    SmallVector<StoreInst*, 2> moveInsts;
    for (BasicBlock::iterator I=exitBB->begin(), IE=exitBB->end(); I!=IE; ++I)
    {
      if (!isa<StoreInst>(I)) continue;
      StoreInst* storeI = cast<StoreInst>(I);
      Value* storedVal = storeI->getValueOperand();
      Value* mappedStoreVal = endLoopValueMap[storedVal];
      storeI->replaceUsesOfWith(storedVal, mappedStoreVal);
      moveInsts.push_back(storeI);
    }

    TerminatorInst* terminator = endExitBB->getTerminator();
    for (SmallVector<StoreInst*, 2>::iterator it=moveInsts.begin(),
         E=moveInsts.end(); it!=E; ++it)
    {
        (*it)->moveBefore(terminator);
    }
  }

  assert (!verifyFunction(*noiseFn) && "verification failed!");

  //-------------------------------------------------------------------------//

  // - Analyze SCCs etc.
  // - Extract loop body into function, map reduction phis to arguments
  //   - As early as possible so we can create SIMD reduction function more easily
  // - Determine position of reduction call (if possible)
  //   - TODO: Make sure the resulting position is valid inside the later extracted code
  //   - TODO: Check if there is a valid position as early as possible
  // - Create scalar reduction function (dummy, no body)
  // - Create SIMD reduction function (clone loop body function W times)
  //   - Remove everything not related to the reduction
  //   - Map inputs/outputs of the W cloned functions
  // - Create call to scalar reduction function
  //   - Create alloca/store/load for every "other operand"
  //   - Pass result of mask functions for mask parameters
  // - Rewire SCC to scalar reduction function.
  // - Remove reduction operations
  // - run WFV
  // - Vectorize "simple" reductions.

  //-------------------------------------------------------------------------//

  // Extract the loop body.
  // This is a non-trivial task, since the code that is not part of the body
  // (induction variable increment etc.) in the C code is part of it in LLVM IR.
  // This function attempts to split out only the relevant parts of the code.
  SmallVector<BasicBlock*, 4> loopBody;
  Function* loopBodyFn = extractLoopBody(loop,
                                         indVarPhi,
                                         indVarUpdate,
                                         mVectorizationFactor,
                                         mDomTree,
                                         loopBody);
  if (!loopBodyFn)
  {
    errs() << "ERROR: Loop body extraction failed!\n";
    return false;
  }

  // Update preheaderBB and latchBB.
  preheaderBB = loop->getLoopPreheader();
  latchBB = loop->getLoopLatch();

  assert (loopBodyFn->getNumUses() == 1);
  CallInst* loopBodyCall = cast<CallInst>(*loopBodyFn->use_begin());
  assert (loopBodyCall->use_empty());

  // Map reduction phis to their respective arguments.
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    Function::arg_iterator A = loopBodyFn->arg_begin();
    for (CallInst::op_iterator O=loopBodyCall->op_begin(),
         OE=loopBodyCall->op_end(); O!=OE; ++O, ++A)
    {
      if (*O == redVar.mPhi) break;
    }
    assert (A != loopBodyFn->arg_end());
    redVar.mPhiArg = A;
  }

  // Map "other operands" to their respective arguments if defined outside the extracted code.
  // NOTE: "Other operands" includes conditions if the update operation depends on control flow.
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    const RedUpMapType& updates = *redVar.mUpdates;
    for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
    {
      const ReductionUpdate& redUp = *it->second;
      OtherOperandsVec& otherOperands = *redUp.mOtherOperands;
      for (unsigned i=0, e=otherOperands.size(); i<e; ++i)
      {
        Value* operand = otherOperands[i];
        if (!isa<Instruction>(operand) && !isa<Argument>(operand)) continue;
        if (isa<Instruction>(operand) &&
            cast<Instruction>(operand)->getParent()->getParent() == loopBodyFn) continue;
        if (isa<Argument>(operand) &&
            cast<Argument>(operand)->getParent() == loopBodyFn) continue;

        Function::arg_iterator A = loopBodyFn->arg_begin();
        for (CallInst::op_iterator O=loopBodyCall->op_begin(),
             OE=loopBodyCall->op_end(); O!=OE; ++O, ++A)
        {
          if (*O == operand) break;
        }
        assert (A != loopBodyFn->arg_end());
        otherOperands[i] = A;
      }
    }
  }

  // Map back edge values.
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    Value* backEdgeVal = redVar.mPhi->getIncomingValueForBlock(loop->getLoopLatch());
    assert (isa<LoadInst>(backEdgeVal));
    redVar.mBackEdgeVal = cast<Instruction>(backEdgeVal);
  }

  // Find write-back operations of results:
  // - Get the load that is the incoming value to the reduction phi from the latch.
  // - Get its pointer operand (alloca).
  // - Get the argument of the extracted function where the alloca is passed.
  // - The desired store operation is the single use of this alloca.
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;

    // Find argument index of the value that goes back to the reduction phi from the latch.
    assert (redVar.mBackEdgeVal);
    assert (isa<LoadInst>(redVar.mBackEdgeVal));
    Value* ptr = cast<LoadInst>(redVar.mBackEdgeVal)->getPointerOperand();
    assert (isa<AllocaInst>(ptr));

    Function::arg_iterator A = loopBodyFn->arg_begin();
    for (CallInst::op_iterator O=loopBodyCall->op_begin(),
         OE=loopBodyCall->op_end(); O!=OE; ++O, ++A)
    {
      if (*O == ptr) break;
    }
    assert (A != loopBodyFn->arg_end());

    Argument* outArg = A;
    assert (outArg->getType()->isPointerTy());
    assert (outArg->getType()->getPointerElementType() == redVar.mPhi->getType());
    assert (outArg->getNumUses() == 1);
    assert (isa<StoreInst>(*outArg->use_begin()));
    redVar.mOutArg = outArg;
    StoreInst* storeBack = cast<StoreInst>(*outArg->use_begin());
    assert (isa<Instruction>(storeBack->getValueOperand()));
    assert (redVar.mUpdates->count(cast<Instruction>(storeBack->getValueOperand())));
    redVar.mStoreBack = storeBack;
  }

  DEBUG_NOISE_WFV( outs() << "\nfunction after extraction:" << *loopBodyFn << "\n"; );
  assert (!verifyFunction(*loopBodyFn));

  //-------------------------------------------------------------------------//

  // - Determine position of reduction call (if possible)
  //   - TODO: Make sure the resulting position is valid inside the later extracted code
  //   - TODO: Check if there is a valid position as early as possible
  Instruction* earliestPos = loopBodyFn->getEntryBlock().getFirstNonPHI();
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    if (redVar.mCanOptimizeWithVector) continue;
    Instruction* latestPos = redVar.mStoreBack;
    redVar.mReductionPos = getCallInsertPosition(redVar, earliestPos, latestPos);
    if (!redVar.mReductionPos)
    {
      errs() << "ERROR: Placing of reduction call is impossible for variable: "
          << *redVar.mPhi << "\n";
      assert (false && "placing of reduction call is impossible!");
      return false;
    }

    DEBUG_NOISE_WFV( outs() << "reduction var phi: " << *redVar.mPhi << "\n"; );
    DEBUG_NOISE_WFV( outs() << "  position for reduction call: " << *redVar.mReductionPos << "\n"; );
  }

  //-------------------------------------------------------------------------//

  // - Create scalar reduction function (dummy, no body)
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    if (redVar.mCanOptimizeWithVector) continue;
    generateScalarReductionFunction(redVar);
    DEBUG_NOISE_WFV( outs() << "reduction var phi: " << *redVar.mPhi << "\n"; );
    DEBUG_NOISE_WFV( outs() << "  scalar reduction function: " << *redVar.mReductionFn << "\n"; );
  }

  //-------------------------------------------------------------------------//

  // - Create SIMD reduction function (clone loop body function W times)
  //   - Remove everything not related to the reduction
  //   - Map inputs/outputs of the W cloned functions
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    if (redVar.mCanOptimizeWithVector) continue;

    generateSIMDReductionFunction(redVar, mVectorizationFactor, loopBodyFn, redVars);
    DEBUG_NOISE_WFV( outs() << "reduction var phi: " << *redVar.mPhi << "\n"; );
    DEBUG_NOISE_WFV( outs() << "  SIMD reduction function: " << *redVar.mReductionFnSIMD << "\n"; );
    assert (!verifyFunction(*redVar.mReductionFnSIMD));
  }

  //-------------------------------------------------------------------------//

  // - Create call to scalar reduction function
  //   - Create alloca/store/load for every "other operand"
  //   - Pass result of mask functions for mask parameters
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    if (redVar.mCanOptimizeWithVector) continue;
    assert (redVar.mPhi && redVar.mStartVal && redVar.mUpdates);
    assert (redVar.mReductionFn && redVar.mReductionPos);
    SmallVector<Value*, 4> args;
    getCallArgs(redVar, args);
    redVar.mReductionFnCall = CallInst::Create(redVar.mReductionFn,
                                               args,
                                               "",
                                               redVar.mReductionPos);
    DEBUG_NOISE_WFV( outs() << "reduction var phi: " << *redVar.mPhi << "\n"; );
    DEBUG_NOISE_WFV( outs() << "  scalar reduction call: " << *redVar.mReductionFnCall << "\n"; );
  }

  DEBUG_NOISE_WFV( outs() << "\nfunction after generation of scalar calls:" << *noiseFn << "\n"; );

  //-------------------------------------------------------------------------//

  // - Rewire SCC to scalar reduction function.
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    if (redVar.mCanOptimizeWithVector) continue;

    // Replace value that is stored back by the final result of the reduction call.
    LoadInst* reload = new LoadInst(redVar.mResultPtr, "red.result.reload", redVar.mStoreBack);
    redVar.mStoreBack->setOperand(0, reload);

    // Replace users of intermediate results by other outputs of reduction call (given
    // by reload of intermediate result pointer).
    const RedUpMapType& updates = *redVar.mUpdates;
    for (RedUpMapType::const_iterator it2=updates.begin(), E2=updates.end(); it2!=E2; ++it2)
    {
      ReductionUpdate& redUp = *it2->second;
      ResultUsersVec& users = *redUp.mResultUsers;
      if (users.empty()) continue;

      for (ResultUsersVec::iterator it3=users.begin(), E3=users.end(); it3!=E3; ++it3)
      {
        Instruction* user = *it3;
        LoadInst* reload = new LoadInst(redUp.mIntermediateResultPtr, "redup.interm.reload", user);
        user->replaceUsesOfWith(redUp.mOperation, reload);
      }
    }
  }

  DEBUG_NOISE_WFV( outs() << "\nfunction after rewiring:" << *loopBodyFn << "\n"; );

  //-------------------------------------------------------------------------//

  // - Remove reduction operations
  // For this, we have to start with the last operation of the SCC and then work
  // our way upwards to prevent deletion of instructions which still have a use.
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    if (redVar.mCanOptimizeWithVector) continue;
    DEBUG_NOISE_WFV( outs() << "erasing SCC: " << *redVar.mPhi << "\n"; );

    const RedUpMapType& updates = *redVar.mUpdates;
    bool done = false;
    while (!done)
    {
      done = true;
      SmallVector<Instruction*, 2> deleteVec;
      for (RedUpMapType::const_iterator it2=updates.begin(), E2=updates.end(); it2!=E2; ++it2)
      {
        ReductionUpdate& redUp = *it2->second;
        if (!redUp.mOperation) continue; // Deleted in previous iteration.
        const bool hasUse = !redUp.mOperation->use_empty();
        done &= !hasUse;
        if (!hasUse)
        {
          DEBUG_NOISE_WFV( outs() << "marking update op for deletion: " << *redUp.mOperation << "\n"; );
          deleteVec.push_back(redUp.mOperation);
          redUp.mOperation = NULL;
        }
      }

      for (SmallVector<Instruction*, 2>::iterator it2=deleteVec.begin(),
           E2=deleteVec.end(); it2!=E2; ++it2)
      {
        DEBUG_NOISE_WFV( outs() << "erasing update op: " << **it2 << "\n"; );
        (*it2)->eraseFromParent();
      }
    }
  }

  DEBUG_NOISE_WFV( outs() << "\nfunction after removal of reductions:" << *loopBodyFn << "\n"; );

  //-------------------------------------------------------------------------//

  // Create new function type.
  // Varying parameters are the one of the loop induction variable and all that
  // are related to reductions that can be vectorized. However, the loop
  // induction variable is no vector value since it also is consecutive.
  // All other incoming values are uniform.
  FunctionType* loopBodyFnType = loopBodyFn->getFunctionType();
  Type*         newReturnType  = loopBodyFnType->getReturnType();
  std::vector<Type*>  newParamTypes;
  Argument*           indVarArg = 0;
  assert (loopBodyFnType->getNumParams() == loopBodyCall->getNumArgOperands());
  Function::arg_iterator A = loopBodyFn->arg_begin();
  for (unsigned i=0, e=loopBodyCall->getNumArgOperands(); i<e; ++i, ++A)
  {
    Value* argOp = loopBodyCall->getArgOperand(i);
    Type*  type  = loopBodyFnType->getParamType(i);
    assert (type == argOp->getType());

    if (argOp == indVarPhi)
    {
      newParamTypes.push_back(type);
      // Map the induction variable to its new argument.
      indVarArg = A;
      continue;
    }

    // Reduction variables that can be vectorized have to have a vector input and a
    // vector-pointer output argument.
    bool requiresVectorType = false;
    for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
    {
      ReductionVariable& redVar = **it;
      if (!redVar.mCanOptimizeWithVector) continue;
      if (redVar.mPhiArg != A && redVar.mOutArg != A) continue;
      requiresVectorType = true;
      break;
    }

    if (requiresVectorType)
    {
      assert (argOp != indVarPhi);
      newParamTypes.push_back(vectorizeSIMDType(type, mVectorizationFactor));
      continue;
    }

    // Otherwise, the type is the same (either uniform or varying/consecutive).
    newParamTypes.push_back(type);

  }
  assert (indVarArg && "loop body independent of induction variable!?");
  FunctionType* simdFnType = FunctionType::get(newReturnType, newParamTypes, false);

  // Create new name.
  std::stringstream sstr;
  sstr << loopBodyFn->getName().str() << "_SIMD";
  const std::string& simdFnName = sstr.str();

  // Create external target function for WFV.
  Function* simdFn = Function::Create(simdFnType,
                                      Function::ExternalLinkage,
                                      simdFnName,
                                      mModule);

  // Set up WFV interface.
  const int maskPosition = -1; // No mask argument.
  WFVInterface::WFVInterface wfvInterface(mModule,
                                          &mModule->getContext(),
                                          loopBodyFn,
                                          simdFn,
                                          mVectorizationFactor,
                                          maskPosition,
                                          mUseDivergenceAnalysis,
                                          mVerbose);

  // Add semantics for SSE/AVX builtins.
  if (mUseAVX) wfvInterface.addCommonMappings(false, false, false, true, false);
  else wfvInterface.addCommonMappings(true, true, true, false, false);

  // Add semantics to the induction variable vector.
  wfvInterface.addSIMDSemantics(*indVarArg, false, true, false, true, false, true);

  // Add mappings for the reduction functions (if any).
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    if (redVar.mCanOptimizeWithVector) continue;

    // The mask is always the last parameter (by construction in generateSIMDReductionFns()).
    const unsigned numParams          = redVar.mReductionFnSIMD->getFunctionType()->getNumParams();
    const int      maskIdx            = numParams-1;
    const bool     mayHaveSideEffects = true;
    wfvInterface.addSIMDMapping(*redVar.mReductionFn,
                                *redVar.mReductionFnSIMD,
                                maskIdx,
                                mayHaveSideEffects);
  }

  // Add semantics to final result alloca to prevent vectorization (otherwise it is
  // marked as OP_VARYING because the reduction call is OP_VARYING).
  // Also mark its reload uses and their store uses.
  for (RedVarVecType::const_iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    const ReductionVariable& redVar = **it;
    if (redVar.mCanOptimizeWithVector) continue;

    const Instruction& resPtr = *redVar.mResultPtr;
    wfvInterface.addSIMDSemantics(resPtr, true, false, false, false,
                                  true, false, false,
                                  true, true, false);
    for (Instruction::const_use_iterator U=resPtr.use_begin(),
         UE=resPtr.use_end(); U!=UE; ++U)
    {
      const Instruction& useI = *cast<Instruction>(*U);
      if (isa<CallInst>(useI)) continue;
      wfvInterface.addSIMDSemantics(useI, true, false, false, false,
                                    true, false, false,
                                    true, true, false);
      for (Instruction::const_use_iterator U2=useI.use_begin(),
           UE2=useI.use_end(); U2!=UE2; ++U2)
      {
        const Instruction& useI2 = *cast<Instruction>(*U2);
        assert (isa<StoreInst>(useI2));
        wfvInterface.addSIMDSemantics(useI2, true, false, false, false,
                                      true, false, false,
                                      true, true, false);
      }
    }
  }

  // Add semantics to "other operand" allocas to enforce vectorization.
  // However, also make sure that their uses are never marked as OP_SEQUENTIAL.
  const BasicBlock* entryBB = &loopBodyFn->getEntryBlock();
  for (BasicBlock::const_iterator I=entryBB->begin(), IE=entryBB->end(); I!=IE; ++I)
  {
    if (!isa<AllocaInst>(I)) continue;
    if (!I->getName().startswith("red.otherop")) continue;
    wfvInterface.addSIMDSemantics(*I, false, true, false, false,
                                  false, true, false,
                                  true, false, true);

    for (Instruction::const_use_iterator U=I->use_begin(),
         UE=I->use_end(); U!=UE; ++U)
    {
      const Instruction& useI = *cast<Instruction>(*U);
      assert (isa<StoreInst>(useI) || isa<LoadInst>(useI));
      wfvInterface.addSIMDSemantics(useI, false, true, false, false,
                                    false, !useI.getType()->isVoidTy(), false,
                                    false, false, false);
    }
  }

  // Run WFV.
  const bool vectorized = wfvInterface.run();

  // TODO: verifyFunction() should not be necessary at some point ;).
  if (!vectorized || verifyFunction(*simdFn, PrintMessageAction))
  {
    // We don't have to rollback anything, just delete the newly generated function.
    simdFn->eraseFromParent();
    return false;
  }

  assert (mModule->getFunction(simdFnName));
  assert (simdFn == mModule->getFunction(simdFnName));

  DEBUG_NOISE_WFV( outs() << "\nfunction after WFV: " << *simdFn << "\n"; );

  //-------------------------------------------------------------------------//
  // Vectorize "simple" reductions.
  // If the reduction only consists of one type of update operations, and that
  // operation is associative and commutative, we can do a "classic" reduction
  // optimization:
  // - Replace the scalar reduction variable R by a vector variable VR.
  // - Initialize VR with <R, S, S, S>, where S is the neutral element of the
  //   operation (0 for add/sub, 1 for mul).
  // - Vectorize VR as part of normal WFV (no reduction function etc.)
  //   - Mark VR as "varying".
  // - Behind the loop, create a horizontal reduction operation that performs
  //   the reduction operation on each element of VR and produces a scalar
  //   result again.
  // - Replace all uses of the original reduction result by this.
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    if (!redVar.mCanOptimizeWithVector) continue;

    assert (redVar.mPhi->getIncomingValueForBlock(latchBB) == redVar.mBackEdgeVal);

    LLVMContext& context = redVar.mPhi->getContext();

    Type* oldType = redVar.mPhi->getType();
    Type* newType = vectorizeSIMDType(oldType, mVectorizationFactor);

    // Mutate type of phi
    redVar.mPhi->mutateType(newType);

    // Vectorize start value.
    Value* oldStartVal = redVar.mPhi->getIncomingValueForBlock(preheaderBB);
    assert (oldStartVal->getType() == oldType);
    Value* newStartVal = UndefValue::get(newType);

    // Get the neutral value of the common update operation as start values
    // for lanes 1 to W-1. The start value of lane 0 is the old start value.
    Value* neutralVal = NULL;
    assert (redVar.mCommonOpcode != 0);
    switch (redVar.mCommonOpcode)
    {
      case Instruction::Add:
      case Instruction::FAdd:
      {
        neutralVal = Constant::getNullValue(oldType);
        break;
      }
      case Instruction::Mul:
      {
        neutralVal = ConstantInt::get(oldType, 1, false);
        break;
      }
      case Instruction::FMul:
      {
        neutralVal = ConstantFP::get(oldType, 1.0);
        break;
      }
      default:
      {
        errs() << "ERROR: Bad common operation for 'simple' reduction found!\n";
        assert (false && "should never happen!");
        return false;
      }
    }

    Instruction* insertBefore = preheaderBB->getTerminator();
    for (unsigned i=0; i<mVectorizationFactor; ++i)
    {
      ConstantInt* idxVal = ConstantInt::get(context, APInt(32, i));
      Value* elem = i == 0 ? oldStartVal : neutralVal;
      newStartVal = InsertElementInst::Create(newStartVal,
                                              elem,
                                              idxVal,
                                              "",
                                              insertBefore);
    }

    // Replace start val.
    const unsigned preheaderIdx = redVar.mPhi->getBasicBlockIndex(preheaderBB);
    redVar.mPhi->setIncomingValue(preheaderIdx, newStartVal);

    // The value from the latch is already a vector due to WFV.
    // However, the reload doesn't know anything about this yet,
    // so we simply mutate its type.
    assert (isa<LoadInst>(redVar.mBackEdgeVal));
    LoadInst* latchVal = cast<LoadInst>(redVar.mBackEdgeVal);
    assert (latchVal->getType() == oldType);
    latchVal->mutateType(newType);

    // Accordingly, we have to mutate the type of the corresponding alloca.
    Value* ptrVal = latchVal->getPointerOperand();
    assert (isa<AllocaInst>(ptrVal));
    ptrVal->mutateType(PointerType::get(newType, ptrVal->getType()->getPointerAddressSpace()));

    // Replace all uses of the result user phi by a dummy.
    assert (redVar.mResultUser->getNumIncomingValues() == 1);
    insertBefore = redVar.mResultUser->getParent()->getFirstNonPHI();
    Instruction* dummy = SelectInst::Create(Constant::getAllOnesValue(Type::getInt1Ty(context)),
                                            UndefValue::get(oldType),
                                            UndefValue::get(oldType),
                                            "dummy",
                                            insertBefore);
    redVar.mResultUser->replaceAllUsesWith(dummy);

    // Mutate the type of the only out-of-loop use of the reduction result
    // (not before replacing the uses).
    redVar.mResultUser->mutateType(newType);

    // Insert horizontal reduction operations.
    // Use log(W) shuffles and operations. LLVM is clever enough to create
    // hadd_ps etc. intrinsics from this.
    // Adapted from LLVM LoopVectorize.cpp.
    Value* result = redVar.mResultUser;
    SmallVector<Constant*, 8> shuffleMask(mVectorizationFactor, 0);
    for (unsigned i=mVectorizationFactor; i!=1; i >>= 1)
    {
      // Move the upper half of the vector to the lower half.
      for (unsigned j=0; j!=i/2; ++j)
      {
        shuffleMask[j] = ConstantInt::get(Type::getInt32Ty(context),
                                          i/2 + j,
                                          false);
      }

      // Fill the rest of the mask with undef.
      std::fill(&shuffleMask[i/2],
                shuffleMask.end(),
                UndefValue::get(Type::getInt32Ty(context)));

      Value* shuf = new ShuffleVectorInst(result,
                                          UndefValue::get(result->getType()),
                                          ConstantVector::get(shuffleMask),
                                          "",
                                          insertBefore);

      result = BinaryOperator::Create((Instruction::BinaryOps)redVar.mCommonOpcode,
                                      result,
                                      shuf,
                                      "",
                                      insertBefore);
    }

    Constant* idx0 = ConstantInt::get(Type::getInt32Ty(context), 0, false);
    result = ExtractElementInst::Create(result,
                                        idx0,
                                        "",
                                        insertBefore);

    // Replace the dummy with the final result.
    dummy->replaceAllUsesWith(result);
    dummy->eraseFromParent();
  }

  //-------------------------------------------------------------------------//

  // Inline reduction functions into the vectorized code.
  // The "scalar" dummy reduction function can't be erased until the temporary
  // function that served as the basis for WFV was erased.
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    if (redVar.mCanOptimizeWithVector) continue;

    Function* fn = redVar.mReductionFnSIMD;
    for (Function::use_iterator U=fn->use_begin(), UE=fn->use_end(); U!=UE; ++U)
    {
      assert (isa<CallInst>(*U));
      CallInst* call = cast<CallInst>(*U);
      InlineFunctionInfo IFI;
      InlineFunction(call, IFI);
    }

    assert (fn->use_empty());
    fn->eraseFromParent();
  }

  // Clean up SIMD function (get rid of local storage).
  {
    FunctionPassManager FPM(mModule);
    FPM.add(new DataLayout(mModule));
    FPM.add(createSROAPass());
    FPM.run(*simdFn);
  }

  //-------------------------------------------------------------------------//

  // To execute the vectorized code, we have to replace the body of the original function.
#if 0
  loopBodyFn->deleteBody();

  ValueToValueMapTy valueMap;
  Function::arg_iterator destI = loopBodyFn->arg_begin();
  for (Function::const_arg_iterator I = simdFn->arg_begin(),
          E = simdFn->arg_end(); I != E; ++I)
  {
      if (valueMap.count(I) == 0)          // Is this argument preserved?
      {
          destI->setName(I->getName()); // Copy the name over...
          valueMap[I] = destI++;           // Add mapping to ValueMap
      }
  }
  SmallVector<ReturnInst*, 10> returns;
  ClonedCodeInfo               clonedFInfo;
  const char*                  nameSuffix = ".";
  CloneFunctionInto(loopBodyFn,
                    simdFn,
                    valueMap,
                    false,
                    returns,
                    nameSuffix,
                    &clonedFInfo);

  // The generated function is not required anymore.
  simdFn->eraseFromParent();

  // Finally, re-inline the loop body function into the noise function.
  assert (loopBodyFn->getNumUses() == 1 &&
          "There should be only one call to the extracted loop body function");
  assert (isa<CallInst>(*loopBodyFn->use_begin()));
  CallInst* call = cast<CallInst>(*loopBodyFn->use_begin());
  assert (call->getParent()->getParent() == noiseFn);
  InlineFunctionInfo IFI;
  InlineFunction(call, IFI);

  // Remove the now inlined loop body function again.
  assert (loopBodyFn->use_empty());
  loopBodyFn->eraseFromParent();
#else
  // To execute the vectorized code, we have to replace the call to loopBodyFn
  // by a call to simdFn.
  assert (loopBodyFn->getNumUses() == 1 &&
          "There should be only one call to the extracted loop body function");
  assert (isa<CallInst>(*loopBodyFn->use_begin()));
  CallInst* loopBodyFnCall = cast<CallInst>(*loopBodyFn->use_begin());
  assert (loopBodyFnCall->getParent()->getParent() == noiseFn);
  assert (loopBodyFnCall->use_empty());

  SmallVector<Value*, 8> args;
  CallInst::op_iterator O = loopBodyCall->op_begin();
  for (Function::arg_iterator A=simdFn->arg_begin(),
       AE=simdFn->arg_end(); A!=AE; ++A, ++O)
  {
    assert ((*O)->getType() == A->getType());
    args.push_back(*O);
  }

  CallInst* newCall = CallInst::Create(simdFn,
                                       args,
                                       loopBodyFnCall->getName(),
                                       loopBodyFnCall);
  loopBodyFnCall->eraseFromParent();

  // Immediately inline the call.
  InlineFunctionInfo IFI;
  InlineFunction(newCall, IFI);

  // Remove the now unused functions again.
  assert (loopBodyFn->use_empty());
  loopBodyFn->eraseFromParent();
  assert (simdFn->use_empty());
  simdFn->eraseFromParent();
#endif

  // Delete reduction variable data structure.
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    delete *it;
  }

  assert (!verifyFunction(*noiseFn) && "verification failed!");

  // Clean up function (get rid of local storage).
  {
    FunctionPassManager FPM(mModule);
    FPM.add(new DataLayout(mModule));
    FPM.add(createSROAPass());
    FPM.run(*noiseFn);
  }

  DEBUG_NOISE_WFV( outs() << "final function after NoiseWFVWrapper:\n" << *noiseFn << "\n"; );

  return true;
}

// Helper functions for collectReductionVariables().
namespace {

// TODO: There's a problem with store-load chains that we don't detect
//       to be part of the SCC!
bool
findReductionSCC(Instruction*                  curInst,
                 PHINode*                      reductionPhi,
                 const Loop&                   loop,
                 RedUpMapType&                 reductionSCC,
                 SmallPtrSet<Instruction*, 8>& visitedInsts)
{
  assert (curInst && reductionPhi);

  if (visitedInsts.count(curInst)) return false;
  visitedInsts.insert(curInst);

  if (reductionSCC.count(curInst)) return true;
  if (curInst == reductionPhi) return true;

  // Recurse into the operands and see if we can find the reduction phi or
  // another instruction that is already part of the SCC.
  bool isInSCC = false;
  for (Instruction::op_iterator O=curInst->op_begin(),
       OE=curInst->op_end(); O!=OE; ++O)
  {
    // Don't recurse into non-instruction operands.
    if (!isa<Instruction>(*O)) continue;
    Instruction* opInst = cast<Instruction>(*O);

    // If this predecessor is already in the SCC, don't recurse into it.
    if (reductionPhi == opInst || reductionSCC.count(opInst))
    {
      isInSCC = true;
      continue;
    }

    // Don't recurse into blocks that are not in the loop.
    BasicBlock* opBB = opInst->getParent();
    if (!loop.contains(opBB)) continue;

    // Recurse.
    isInSCC |= findReductionSCC(opInst, reductionPhi, loop, reductionSCC, visitedInsts);
  }

  if (!isInSCC) return false;

  ReductionUpdate* redUp = new ReductionUpdate();
  redUp->mOperation = curInst;

  reductionSCC[curInst] = redUp;

  return true;
}

void
gatherConditions(BasicBlock*                  block,
                 BasicBlock*                  succBB,
                 const BasicBlock*            latchBB,
                 const DominatorTree&         domTree,
                 OtherOperandsVec&            otherOperands,
                 SmallPtrSet<BasicBlock*, 8>& visitedBlocks)
{
  assert (block && latchBB);

  if (visitedBlocks.count(block)) return;
  visitedBlocks.insert(block);

  // If succBB is not set this is the first block of this path,
  // so we don't want to add any condition.
  TerminatorInst* terminator = block->getTerminator();
  if (succBB && terminator->getNumSuccessors() > 1)
  {
    if (const BranchInst* brI = dyn_cast<BranchInst>(terminator))
    {
      assert (brI->isConditional());
      otherOperands.push_back(brI->getCondition());
    }
    else if (SwitchInst* swI = dyn_cast<SwitchInst>(terminator))
    {
      otherOperands.push_back(swI->getCondition());
      assert (swI->findCaseDest(succBB));
      otherOperands.push_back(swI->findCaseDest(succBB));
    }
    else
    {
      assert (false && "not implemented!");
    }
  }

  // If this block dominates the loop latch block, we are done for this path.
  if (domTree.dominates(block, latchBB)) return;

  // Otherwise, recurse into predecessors.
  for (pred_iterator P=pred_begin(block), PE=pred_end(block); P!=PE; ++P)
  {
    BasicBlock* predBB = *P;
    gatherConditions(predBB, block, latchBB, domTree, otherOperands, visitedBlocks);
  }
}

void
gatherReductionUpdateInfo(RedUpMapType&        reductionSCC,
                          const PHINode*       reductionPhi,
                          const BasicBlock*    latchBB,
                          const DominatorTree& domTree)
{
  for (RedUpMapType::iterator it=reductionSCC.begin(),
       E=reductionSCC.end(); it!=E; ++it)
  {
    ReductionUpdate& redUp = *it->second;
    Instruction* updateOp = redUp.mOperation;

    // Add all operands that are not part of the SCC to the "other operands" set.
    OtherOperandsVec* otherOperands = new OtherOperandsVec();
    for (Instruction::op_iterator O=updateOp->op_begin(),
         OE=updateOp->op_end(); O!=OE; ++O)
    {
      if (isa<BasicBlock>(*O)) continue;
      if (isa<Function>(*O)) continue;

      if (Instruction* opInst = dyn_cast<Instruction>(*O))
      {
        if (reductionPhi == opInst) continue;
        if (reductionSCC.count(opInst)) continue;
      }
      otherOperands->push_back(*O);
    }
    redUp.mOtherOperands = otherOperands;

    // Add all users that are not part of the SCC to the "result users" set.
    ResultUsersVec* resultUsers = new ResultUsersVec();
    for (Instruction::use_iterator U=updateOp->use_begin(),
         UE=updateOp->use_end(); U!=UE; ++U)
    {
      assert (isa<Instruction>(*U));
      Instruction* useI = cast<Instruction>(*U);
      if (reductionPhi == useI) continue;
      if (reductionSCC.count(useI)) continue;

      resultUsers->insert(useI);
    }
    redUp.mResultUsers = resultUsers;

    // More concretely, we collect all conditions that this update depends upon.
    // NOTE: It would be beneficial to have WFV divergence information here.
    BasicBlock* block = updateOp->getParent();
    SmallPtrSet<BasicBlock*, 8> visitedBlocks;
    gatherConditions(block, NULL, latchBB, domTree, *otherOperands, visitedBlocks);

    // The other information is only inserted later.
    redUp.mIntermediateResultPtr = NULL;
  }
}

bool
isCAUpdateOp(const unsigned opcode)
{
  switch (opcode)
  {
    case Instruction::Add:
    case Instruction::FAdd:
    case Instruction::Mul:
    case Instruction::FMul:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Xor:
    case Instruction::Shl:
    case Instruction::LShr:
    case Instruction::AShr:
    case Instruction::PHI:
    case Instruction::Select:
    case Instruction::GetElementPtr:
      return true;
    default:
      return false;
  }
}


} // unnamed namespace

// TODO: Make sure there is no interference between reduction variables.
void
NoiseWFVWrapper::collectReductionVariables(RedVarVecType&       redVars,
                                           PHINode*             indVarPhi,
                                           const Loop&          loop,
                                           const DominatorTree& domTree)
{
  assert (indVarPhi);

  BasicBlock* preheaderBB = loop.getLoopPreheader();
  BasicBlock* headerBB    = loop.getHeader();
  BasicBlock* latchBB     = loop.getLoopLatch();
  BasicBlock* exitBB      = loop.getUniqueExitBlock();

  for (BasicBlock::iterator I=headerBB->begin(),
       IE=headerBB->end(); I!=IE; ++I)
  {
    if (headerBB->getFirstNonPHI() == I) break;
    if (indVarPhi == I) continue;

    PHINode* reductionPhi = cast<PHINode>(I);
    assert (reductionPhi->getNumIncomingValues() == 2);

    ReductionVariable* redVar = new ReductionVariable();
    redVar->mPhi = reductionPhi;

    assert (reductionPhi->getIncomingValueForBlock(preheaderBB));
    redVar->mStartVal = reductionPhi->getIncomingValueForBlock(preheaderBB);

    assert (reductionPhi->getIncomingValueForBlock(latchBB));
    assert (isa<Instruction>(reductionPhi->getIncomingValueForBlock(latchBB)));
    Instruction* backEdgeVal = cast<Instruction>(reductionPhi->getIncomingValueForBlock(latchBB));
    redVar->mBackEdgeVal = backEdgeVal;

    RedUpMapType* reductionSCC = new RedUpMapType();
    SmallPtrSet<Instruction*, 8> visitedInsts;
    findReductionSCC(backEdgeVal, reductionPhi, loop, *reductionSCC, visitedInsts);

    // Weirdly, it can happen that there are two phis for the same loop-carried variable,
    // where the one update operation references the other phi.
    // This results in an empty reductionSCC, which is actually correct since this is
    // no real reduction.
    //if (reductionSCC->empty()) continue;
    assert (!reductionSCC->empty());
    gatherReductionUpdateInfo(*reductionSCC, reductionPhi, latchBB, domTree);

    redVar->mUpdates = reductionSCC;

    // There does not need to be a result user, but there may be one.
    redVar->mResultUser = NULL;
    for (BasicBlock::iterator I2=exitBB->begin(),
         IE2=exitBB->end(); I2!=IE2; ++I2)
    {
      if (exitBB->getFirstNonPHI() == I2) break;
      PHINode* exitPhi = cast<PHINode>(I2);
      assert (exitPhi->getNumIncomingValues() == 1);
      if (exitPhi->getIncomingValue(0) != reductionPhi)
      {
        continue;
      }

      assert (!redVar->mResultUser &&
              "must not have more than one reduction user outside the loop!");
      redVar->mResultUser = exitPhi;
    }

    // Check if this reduction can be optimized, i.e. performed using vector
    // instructions and a post-loop horizontal vector update operation.
    // Do not consider phis when testing for a common opcode.
    bool hasCommonOpcode = true;
    unsigned commonOpcode = 0;
    bool hasIntermediateUses = false;
    for (RedUpMapType::const_iterator it=reductionSCC->begin(),
         E=reductionSCC->end(); it!=E; ++it)
    {
      const ReductionUpdate& redUp = *it->second;

      const unsigned redUpOpcode = redUp.mOperation->getOpcode();
      assert (redUpOpcode != 0 && "expected opcode 0 not to exist!");

      if (!isa<PHINode>(redUp.mOperation) &&
          commonOpcode != redUpOpcode)
      {
        if (commonOpcode == 0)
        {
          commonOpcode = redUpOpcode;
        }
        else
        {
          hasCommonOpcode = false;
        }
      }

      if (!redUp.mResultUsers->empty())
      {
        hasIntermediateUses = true;
      }
    }

    // If all updates are phis, set the opcode accordingly.
    if (hasCommonOpcode && commonOpcode == 0 && !reductionSCC->empty())
    {
      assert (isa<PHINode>(reductionSCC->begin()->second->mOperation));
      commonOpcode = reductionSCC->begin()->second->mOperation->getOpcode();
    }

    if (!hasIntermediateUses &&
        hasCommonOpcode &&
        isCAUpdateOp(commonOpcode))
    {
      redVar->mCanOptimizeWithVector = true;
    }

    redVar->mCommonOpcode = hasCommonOpcode ? commonOpcode : 0;

    // Sanity check.
    for (Instruction::use_iterator U=reductionPhi->use_begin(),
         UE=reductionPhi->use_end(); U!=UE; ++U)
    {
      assert (isa<Instruction>(*U));
      Instruction* useI = cast<Instruction>(*U);
      if (loop.contains(useI->getParent())) continue;
      assert (useI == redVar->mResultUser &&
              "must not have more than one reduction user outside the loop!");
    }

    // The other information is only inserted later.
    redVar->mReductionFn     = NULL;
    redVar->mReductionFnCall = NULL;
    redVar->mReductionFnSIMD = NULL;
    redVar->mResultPtr = NULL;
    redVar->mPhiArg = NULL;
    redVar->mOutArg = NULL;
    redVar->mStoreBack = NULL;

    redVars.push_back(redVar);
  }
}


char NoiseWFVWrapper::ID = 0;
} // namespace llvm

INITIALIZE_PASS_BEGIN(NoiseWFVWrapper, "wfv-wrapper",
                      "wrapper pass around WFV library", false, false)
INITIALIZE_PASS_DEPENDENCY(DominatorTree)
INITIALIZE_PASS_DEPENDENCY(LoopInfo)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolution)
INITIALIZE_PASS_END(NoiseWFVWrapper, "wfv-wrapper",
                    "wrapper pass around WFV library", false, false)

#endif

