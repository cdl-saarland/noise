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

#include "NoiseWFVMaskAnalysis.h"

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

#include <sstream>

#include <wfvInterface.h>

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
}


// Helper functions for runWFV().
namespace {

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

  BasicBlock* preheaderBB = loop->getLoopPreheader();
  BasicBlock* headerBB    = loop->getHeader();
  BasicBlock* latchBB     = loop->getLoopLatch();
  BasicBlock* exitingBB   = loop->getExitingBlock();
  assert (preheaderBB && headerBB && latchBB &&
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
  ICmpInst* exitCond = cast<ICmpInst>(exitBr->getCondition());
  assert (exitCond->getParent() == exitingBB &&
          "expected exit condition to be in exiting block!");
  assert (exitCond->getNumUses() == 1 &&
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
typedef NoiseWFVWrapper::ReductionUpdate::OtherOpAllocaVec OtherOpAllocaVec;
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
#if 0 // deprecated
  // Initialize the earliest position with the first non-phi of the first block
  // after the header (header is excluded from body extraction).
  BasicBlock* headerBB = redVar.mPhi->getParent();
  assert (headerBB == loop.getHeader());
  BasicBlock* firstBodyBB = headerBB->getTerminator()->getSuccessor(0);
  if (!loop.contains(firstBodyBB))
  {
    assert (headerBB->getTerminator()->getNumSuccessors() == 2);
    firstBodyBB = headerBB->getTerminator()->getSuccessor(1);
  }
  Instruction* earliestPos = firstBodyBB->getFirstNonPHI();

  // Initialize the latest position with the induction variable update operation
  // (which is excluded from body extraction).
  Instruction* latestPos = indVarUpdate;
#endif

  Function* f = redVar.mPhiArg->getParent();
  assert (earliestPos->getParent()->getParent() == f);
  assert (latestPos->getParent()->getParent() == f);

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
      assert (otherOperand->getParent()->getParent() == f);
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
      assert (resultUser->getParent()->getParent() == f);
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
    assert (redUp.mOtherOpAllocas->empty());
    const OtherOperandsVec& otherOperands = *redUp.mOtherOperands;
    for (OtherOperandsVec::const_iterator it2=otherOperands.begin(),
         E2=otherOperands.end(); it2!=E2; ++it2)
    {
      Value* otherOp = *it2;

      if (!isa<Instruction>(otherOp) && !isa<Argument>(otherOp))
      {
        redUp.mOtherOpAllocas->insert(NULL);
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

      redUp.mOtherOpAllocas->insert(alloca);
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
#if 1
    Type* updateType = redUp.mOperation->getType();
    AllocaInst* alloca = new AllocaInst(updateType,
                                        "red.user.storage",
                                        f->getEntryBlock().getFirstNonPHI());
#else
    Instruction* userAllocaPos = redVar.mReductionPos;
    Type* updateType = PointerType::getUnqual(redUp.mOperation->getType());
    FunctionType* fType = FunctionType::get(updateType, false);

    Module* mod = redVar.mPhi->getParent()->getParent()->getParent();
    Function* allocaWrapperFn = Function::Create(fType, Function::ExternalLinkage, "allocaWrapper", mod);
    CallInst* alloca = CallInst::Create(allocaWrapperFn, "red.user.storage.tmp", userAllocaPos);
#endif

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
  if (oldType->isFloatTy() ||
      (oldType->isIntegerTy() && oldType->getPrimitiveSizeInBits() <= 32U))
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
deleteTree(Instruction* inst, std::vector<Instruction*>& deleteVec)
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

  deleteVec.push_back(inst);
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

// - Generate function F_R_SIMD that performs all updates in a vector context:
//   - Return type is the scalar return type of P.
//   - One input parameter for P.
//   - One input parameter per "other operand" per "update operation".
//   - One input parameter per "update operation" that requires a mask.
//   - One output parameter per "update operation" that has at least one "result user".
// TODO: It would be beneficial to have WFV vectorization analysis info here.
void
generateSIMDReductionFunction(ReductionVariable& redVar,
                              const unsigned     vectorizationFactor,
                              Function*          loopBodyFn)
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

  outs() << "SIMD reduction function signature: " << *simdRedFn << "\n";

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
  // This does NOT cover otherOps that are defined in the body.
  // This also does NOT correctly handle non-uniform otherOps.
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
      outs() << "original arg: " << *value << "\n";
      outs() << "mapped arg  : " << *AR << "\n";
      valueMap[value] = AR;
    }
    replaceMap[value] = AR;
  }

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

    // Replace other operands that are defined in the loop body by the respective arguments.
    // This kills the corresponding code in the reduction function.
    for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
    {
      const ReductionUpdate& redUp = *it->second;
      Instruction* mappedUp = cast<Instruction>(valueMap[redUp.mOperation]);
      outs() << "mappedUp: " << *mappedUp << "\n";
      OtherOperandsVec& otherOperands = *redUp.mOtherOperands;
      for (OtherOperandsVec::const_iterator it2=otherOperands.begin(),
           E2=otherOperands.end(); it2!=E2; ++it2)
      {
        Value* operand = *it2;
        Value* mappedOp = valueMap[operand];
        Value* replaceOp = replaceMap[operand];
        outs() << "  operand  : " << *operand << "\n";
        outs() << "  mappedOp : " << *mappedOp << "\n";
        outs() << "  replaceOp: " << *replaceOp << "\n";

        // If the operand has a use that is a terminator instruction, it is a
        // condition operand and thus any extraction operations have to be
        // inserted before this terminator.
        Instruction* insertBefore = mappedUp;
        bool terminatorFound = false;
        bool phiFound = isa<PHINode>(mappedUp);
        for (Value::use_iterator U=operand->use_begin(), UE=operand->use_end(); U!=UE; ++U)
        {
          Value* mappedUse = valueMap[*U];
          outs() << "  mappedUse: " << *mappedUse << "\n";

          // If this becomes a problem, we have to implement stuff to find
          // a valid insertion position.
          if (isa<TerminatorInst>(mappedUse))
          {
            assert (!terminatorFound && !phiFound &&
                    "multiple terminator/phi uses not implemented!");
            terminatorFound = true;
            insertBefore = cast<Instruction>(mappedUse);
          }
          else if (isa<PHINode>(mappedUse))
          {
            assert (!terminatorFound && (mappedUp == mappedUse || !phiFound) &&
                    "multiple terminator/phi uses not implemented!");
            phiFound = true;
          }
        }
        assert (!(terminatorFound && phiFound));

        // If the update operation is a phi, the extraction needs to be
        // performed in the corresponding incoming block.
        if (PHINode* phi = dyn_cast<PHINode>(mappedUp))
        {
          bool valFound = false;
          for (unsigned j=0, ej=phi->getNumIncomingValues(); j<ej; ++j)
          {
            Value* val = phi->getIncomingValue(j);
            if (val != mappedOp) continue;
            assert (!valFound && "multiple blocks with same incoming value to phi not implemented!");
            valFound = true;
            BasicBlock* block = phi->getIncomingBlock(j);
            insertBefore = block->getTerminator();
          }
        }

        if (isa<Argument>(operand))
        {
          // Fix other operands that are vectorized function arguments.
          if (!replaceOp->getType()->isVectorTy()) continue;

          // TODO: For more complex types, we have to use generic extract function (-> WFV).
          replaceOp = ExtractElementInst::Create(replaceOp, c, "", insertBefore);
          // We must not replace all uses of mappedArg, since this would replace
          // all uses of previous iterations of i as well.
          mappedUp->replaceUsesOfWith(mappedOp, replaceOp);

          continue;
        }

        // If the operand is a vector, we have to extract the element that
        // corresponds to the current iteration.
        if (replaceOp->getType()->isVectorTy())
        {
          // TODO: For more complex types, we have to use generic extract function (-> WFV).
          replaceOp = ExtractElementInst::Create(replaceOp, c, "", insertBefore);
        }
        // Here, replacing all uses is safe since the mapped operation is unique
        // for this iteration of i.
        mappedOp->replaceAllUsesWith(replaceOp);
        if (Instruction* inst = dyn_cast<Instruction>(mappedOp)) inst->eraseFromParent();
      }
    }

    // Delete all result users and their uses from the reduction function.
    for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
    {
      const ReductionUpdate& redUp = *it->second;
      if (redUp.mResultUsers->empty()) continue;
      ResultUsersVec& resultUsers = *redUp.mResultUsers;
      for (unsigned j=0, ej=resultUsers.size(); j<ej; ++j)
      {
        Instruction* resultUser = resultUsers[j];
        Instruction* mappedUser = cast<Instruction>(valueMap[resultUser]);

        // For now, we don't touch anything that could alter the control flow behavior.
        if (isInfluencingControlFlow(mappedUser)) continue;

        std::vector<Instruction*> deleteVec;
        deleteTree(mappedUser, deleteVec);
        for (unsigned i=0, e=deleteVec.size(); i<e; ++i)
        {
          assert (deleteVec[i]->use_empty());
          deleteVec[i]->eraseFromParent();
        }
      }
    }

    // Replace return by a branch to the latest entry block.
    // First iteration: do nothing :p.
    if (i != 0)
    {
      assert (isa<ReturnInst>(lastExitBB->getTerminator()));
      BasicBlock* entryBB = cast<BasicBlock>(valueMap[&loopBodyFn->getEntryBlock()]);
      BranchInst::Create(entryBB, lastExitBB->getTerminator());
      lastExitBB->getTerminator()->eraseFromParent();
    }

    // This iteration's "output" is the "input" of the next clone.
    assert (valueMap[redVar.mStoreBack]);
    StoreInst* storeBack = cast<StoreInst>(valueMap[redVar.mStoreBack]);
    lastIterOut = storeBack->getValueOperand();
    lastExitBB = storeBack->getParent();

    // Remove the store operation (unless this is the last iteration).
    if (i+1 != vectorizationFactor)
    {
      storeBack->eraseFromParent();
    }

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

    //outs() << "simdRedFn after iteration " << i << "\n";
    //outs() << *simdRedFn << "\n";
  } // Iterate W times.
}

} // unnamed namespace

// TODO: Implement generation of fixup code for cases where we either
//       don't know the exact iteration count or where it is not an exact
//       multiple of the vectorization width.
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
  assert (preheaderBB && headerBB && latchBB &&
          "vectorization of non-simplified loop not supported!");
  assert (loop->isLoopSimplifyForm() &&
          "vectorization of non-simplified loop not supported!");
  assert (loop->isLCSSAForm(*mDomTree) &&
          "vectorization of loops not in LCSSA form not supported!");

  assert (loop->getNumBackEdges() == 1 &&
          "vectorization of loops with multiple back edges not supported!");
  assert (exitBB &&
          "vectorization of loops with multiple exits not supported!");

  // Get loop induction variable phi.
  // TODO: Use Scalar Evolution for that.
  PHINode* indVarPhi = loop->getCanonicalInductionVariable();
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
  assert (noiseFn == (*redVars.begin())->mPhi->getParent()->getParent());
  outs() << "\nfunction:" << *noiseFn << "\n";
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    assert (redVar.mPhi && redVar.mStartVal && redVar.mUpdates);
    assert (!redVar.mResultUser ||
            redVar.mPhi == redVar.mResultUser->getIncomingValueForBlock(loop->getExitingBlock()));

    outs() << "reduction var phi  P: " << *redVar.mPhi << "\n";
    outs() << "  start value      S: " << *redVar.mStartVal << "\n";
    if (redVar.mResultUser) outs() << "  reduction result R: " << *redVar.mResultUser << "\n";
    else outs() << "  reduction result R: not available\n";

    Type* type = redVar.mPhi->getType();

    assert (type == redVar.mStartVal->getType());
    assert (!redVar.mResultUser || type == redVar.mResultUser->getType());

    const RedUpMapType& updates = *redVar.mUpdates;
    for (RedUpMapType::const_iterator it2=updates.begin(), E2=updates.end(); it2!=E2; ++it2)
    {
      ReductionUpdate& redUp = *it2->second;
      outs() << "  update operation O: " << *redUp.mOperation << "\n";
      if (redUp.mRequiresMask) outs() << "    requires mask.\n";
      if (!redUp.mResultUsers->empty()) outs() << "    has result user(s).\n";
    }
  }

  // TODO: Make sure we stop here already if there are reductions we can't handle.
  //assert (!isa<PHINode>(exitBB->begin()) &&
          //"vectorization of loops with loop-carried dependencies not supported!");

  //-------------------------------------------------------------------------//

  // New plan:
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
  // - Create "mask" function for each update operation that requires a mask.
  // - Create call to each mask function at position of update op.
  // - Create call to scalar reduction function
  //   - Create alloca/store/load for every "other operand"
  //   - Pass result of mask functions for mask parameters
  // - Rewire SCC to scalar reduction function.
  // - Remove reduction operations
  // - WFV
  // - Adjust SIMD reduction function call position to incorporate mask operations.
  // - Rewire operands of calls to mask functions to mask parameters of SIMD reduction
  //   function (use alloca/store/load).

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

  outs() << "\nfunction after extraction:" << *loopBodyFn << "\n";
  verifyFunction(*loopBodyFn);

  //-------------------------------------------------------------------------//

  // - Determine position of reduction call (if possible)
  //   - TODO: Make sure the resulting position is valid inside the later extracted code
  //   - TODO: Check if there is a valid position as early as possible
  Instruction* earliestPos = loopBodyFn->getEntryBlock().getFirstNonPHI();
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    Instruction* latestPos = redVar.mStoreBack;
    redVar.mReductionPos = getCallInsertPosition(redVar, earliestPos, latestPos);
    if (!redVar.mReductionPos)
    {
      errs() << "ERROR: Placing of reduction call is impossible for variable: "
          << *redVar.mPhi << "\n";
      assert (false && "placing of reduction call is impossible!");
      return false;
    }

    outs() << "reduction var phi: " << *redVar.mPhi << "\n";
    outs() << "  position for reduction call: " << *redVar.mReductionPos << "\n";
  }

  //-------------------------------------------------------------------------//

  // - Create scalar reduction function (dummy, no body)
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    generateScalarReductionFunction(redVar);
    outs() << "reduction var phi: " << *redVar.mPhi << "\n";
    outs() << "  scalar reduction function: " << *redVar.mReductionFn << "\n";
  }

  //-------------------------------------------------------------------------//

  // - Create SIMD reduction function (clone loop body function W times)
  //   - Remove everything not related to the reduction
  //   - Map inputs/outputs of the W cloned functions
  // NOTE: We have to maintain all arguments while cloning, otherwise
  //       we may destroy computations we need for branches...
  //       The alternative is to use the masks inserted by WFV, but that
  //       requires transforming the code, not just cloning it. I assume
  //       this would result in a lot more complications.
  // NOTE: It seems this was only the case for conditions of branches that
  //       are required for the reduction. This is correctly handled by
  //       adding those as "other operands" as well.
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    generateSIMDReductionFunction(redVar, mVectorizationFactor, loopBodyFn);
    outs() << "reduction var phi: " << *redVar.mPhi << "\n";
    outs() << "  SIMD reduction function: " << *redVar.mReductionFnSIMD << "\n";
    assert (!verifyFunction(*redVar.mReductionFnSIMD));
  }

  //-------------------------------------------------------------------------//

  // - Create call to scalar reduction function
  //   - Create alloca/store/load for every "other operand"
  //   - Pass result of mask functions for mask parameters
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    assert (redVar.mPhi && redVar.mStartVal && redVar.mUpdates);
    assert (redVar.mReductionFn && redVar.mReductionPos);
    SmallVector<Value*, 4> args;
    getCallArgs(redVar, args);
    redVar.mReductionFnCall = CallInst::Create(redVar.mReductionFn,
                                               args,
                                               "",
                                               redVar.mReductionPos);
    outs() << "reduction var phi: " << *redVar.mPhi << "\n";
    outs() << "  scalar reduction call: " << *redVar.mReductionFnCall << "\n";
  }

  outs() << "\nfunction after generation of scalar calls:" << *noiseFn << "\n";

  //-------------------------------------------------------------------------//

#if 0 // deprecated
  // Replace dummy calls introduced for intermediate uses by correct allocas.
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;

    Instruction* allocaInsertPos = loopBodyFn->getEntryBlock().getFirstNonPHI();
    const RedUpMapType& updates = *redVar.mUpdates;
    for (RedUpMapType::const_iterator it2=updates.begin(), E2=updates.end(); it2!=E2; ++it2)
    {
      ReductionUpdate& redUp = *it2->second;
      if (redUp.mResultUsers->empty()) continue;
      Instruction* allocaWrapperCall = redUp.mIntermediateResultPtr;
      assert (isa<CallInst>(allocaWrapperCall));

      Type* updateType = redUp.mOperation->getType();
      AllocaInst* alloca = new AllocaInst(updateType, "red.user.storage", allocaInsertPos);
      allocaWrapperCall->replaceAllUsesWith(alloca);

      Function* allocaWrapperFn = cast<CallInst>(allocaWrapperCall)->getCalledFunction();
      allocaWrapperCall->eraseFromParent();
      allocaWrapperFn->eraseFromParent();
    }
  }
#endif

  //-------------------------------------------------------------------------//

  // - Rewire SCC to scalar reduction function.
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;

#if 0 // deprecated
    // Replace use of mPhi by final reduction result (reload from alloca).
    Instruction* pos = loop->getExitingBlock()->getTerminator();
    LoadInst* reload = new LoadInst(redVar.mResultPtr, "red.result.reload", pos);
    redVar.mResultUser->replaceUsesOfWith(redVar.mPhi, reload);
#endif

#if 0 // deprecated
    // Replace incoming value from latch to mPhi by the final result of the reduction call.
    const unsigned latchIdx = redVar.mPhi->getBasicBlockIndex(loop->getLoopLatch());
    assert (isa<Instruction>(redVar.mPhi->getIncomingValue(latchIdx)));
    assert (redVar.mUpdates->count(cast<Instruction>(redVar.mPhi->getIncomingValue(latchIdx))));
    Instruction* pos = indVarUpdate;
    LoadInst* reload = new LoadInst(redVar.mResultPtr, "red.result.reload", pos);
    redVar.mPhi->setIncomingValue(latchIdx, reload);
#else
    // Replace value that is stored back by the final result of the reduction call.
    LoadInst* reload = new LoadInst(redVar.mResultPtr, "red.result.reload", redVar.mStoreBack);
    redVar.mStoreBack->setOperand(0, reload);
#endif

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

  outs() << "\nfunction after rewiring:" << *loopBodyFn << "\n";

  //-------------------------------------------------------------------------//

  // - Remove reduction operations
  // For this, we have to start with the last operation of the SCC and then work
  // our way upwards to prevent deletion of instructions which still have a use.
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    outs() << "erasing SCC: " << *redVar.mPhi << "\n";

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
          outs() << "marking update op for deletion: " << *redUp.mOperation << "\n";
          deleteVec.push_back(redUp.mOperation);
          redUp.mOperation = NULL;
        }
      }

      for (SmallVector<Instruction*, 2>::iterator it2=deleteVec.begin(),
           E2=deleteVec.end(); it2!=E2; ++it2)
      {
        outs() << "erasing update op: " << **it2 << "\n";
        (*it2)->eraseFromParent();
      }
    }
  }

  outs() << "\nfunction after removal of reductions:" << *loopBodyFn << "\n";

  //-------------------------------------------------------------------------//

  // Create new function type.
  // The only varying parameter is the one of the loop induction variable.
  // All other incoming values are uniform.
  FunctionType* loopBodyFnType = loopBodyFn->getFunctionType();
  Type*         newReturnType  = loopBodyFnType->getReturnType();
  std::vector<Type*>  newParamTypes;
  std::vector<Value*> newCallArgs;
  Argument*           indVarArg = 0;
  assert (loopBodyFnType->getNumParams() == loopBodyCall->getNumArgOperands());
  for (unsigned i=0, e=loopBodyCall->getNumArgOperands(); i<e; ++i)
  {
    Value* argOp   = loopBodyCall->getArgOperand(i);
    Type*  type    = loopBodyFnType->getParamType(i);
    assert (type == argOp->getType());

    newParamTypes.push_back(type);
    newCallArgs.push_back(argOp);
    if (argOp == indVarPhi)
    {
      Function::arg_iterator A = loopBodyFn->arg_begin();
      std::advance(A, i);
      indVarArg = A;
    }
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
                                          true);

  // Add semantics to the induction variable vector.
  wfvInterface.addSIMDSemantics(*indVarArg, false, true, false, true, false, true);

  // Add mappings for the reduction functions (if any).
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;

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
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    wfvInterface.addSIMDSemantics(*redVar.mResultPtr, true, false, false, false,
                                  true, false, false,
                                  true, true, false);
  }

  // Run WFV.
  const bool vectorized = wfvInterface.run();

  // TODO: verifyFunction() should not be necessary at some point ;).
  if (!vectorized || llvm::verifyFunction(*simdFn, PrintMessageAction))
  {
    // We don't have to rollback anything, just delete the newly generated function.
    simdFn->eraseFromParent();
    return false;
  }

  assert (mModule->getFunction(simdFnName));
  assert (simdFn == mModule->getFunction(simdFnName));

  outs() << "\nfunction after WFV: " << *simdFn << "\n";

  //-------------------------------------------------------------------------//

  // - Adjust SIMD reduction function call position to incorporate mask operations.
  // TODO: HERE!
  // -> remove mask calls alltogether.

  //-------------------------------------------------------------------------//

  // Inline reduction functions into the vectorized code.
  // The "scalar" dummy reduction function can't be erased until the temporary
  // function that served as the basis for WFV was erased.
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
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

  // Upon successful vectorization, we have to modify the loop in the original function.
  // Adjust the increment of the induction variable (increment by simd width).
  // Adjust the exit condition (divide by simd width).
  // -> Already done in extractLoopBody.

  // Generate code that packs all input values into vectors to match the signature.
  // -> Should only be the induction variable itself.
  // -> Already done in extractLoopBody.

  // To execute the vectorized code, we have to replace the body of the original function.
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

  outs() << "final function after NoiseWFVWrapper:\n" << *noiseFn << "\n";

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
gatherConditions(BasicBlock*          block,
                 BasicBlock*          succBB,
                 const BasicBlock*    latchBB,
                 const DominatorTree& domTree,
                 OtherOperandsVec&    otherOperands)
{
  assert (block && latchBB);

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
    gatherConditions(predBB, block, latchBB, domTree, otherOperands);
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
    const unsigned otherOps = otherOperands->size();
    BasicBlock* block = updateOp->getParent();
    gatherConditions(block, NULL, latchBB, domTree, *otherOperands);
    const unsigned conditionOps = otherOperands->size() - otherOps;

    // Find out if this operation may require masked reduction.
    redUp.mRequiresMask = conditionOps > 0;

    // The other information is only inserted later.
    redUp.mIntermediateResultPtr = NULL;
    redUp.mOtherOpAllocas = new OtherOpAllocaVec();
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

#if 0 // deprecated
// Helper functions for finishReductions().
namespace {

// State after execution of this function:
// - parent block of inst is split at the position of inst
// - first if-block is former parent block of 'inst' ("upper part")
// - last if-block is new block containing "lower part" of former parent block of 'inst'
// - each if-block holds mask extraction and scalar comparison if mask-instance is true
// - each target-block only holds an unconditional branch to the next if-block
void
generateIfCascade(Instruction*   inst,
                                   Value*         mask,
                                   BasicBlock**   ifBlocks,
                                   BasicBlock**   targetBlocks,
                                   const unsigned vectorizationFactor)
{
  assert (inst && mask && ifBlocks && targetBlocks && inst->getParent());
  assert (mask->getType()->isVectorTy());

  LLVMContext& context = inst->getContext();

  // Split parent block and move all instructions after inst into endBB.
  BasicBlock* parentBB = inst->getParent();
  BasicBlock* endBB    = parentBB->splitBasicBlock(inst, parentBB->getName()+".casc.end");
  Function*   parentF  = parentBB->getParent();

  // Newly generated branch is not needed.
  parentBB->getTerminator()->eraseFromParent();

  // Create blocks.
  for (unsigned i=0, e=vectorizationFactor; i<e; ++i)
  {
    if (i>0)
    {
      std::stringstream sstr;
      sstr << "casc.if" << i;
      ifBlocks[i] = BasicBlock::Create(context, sstr.str(), parentF, endBB);
    }
    std::stringstream sstr;
    sstr << "casc.exec" << i;
    targetBlocks[i] = BasicBlock::Create(context, sstr.str(), parentF, endBB);
  }

  // Those are not really if-blocks but this simplifies iteration.
  // - iterate until i<vectorizationFactor and use i -> first W blocks (includes parent)
  // - iterate until i<vectorizationFactor and use i+1 -> last W blocks (includes end)
  ifBlocks[0] = parentBB;
  ifBlocks[vectorizationFactor] = endBB;

  // Generate unconditional jump from each exec-block to next if-block.
  for (unsigned i=0, e=vectorizationFactor; i<e; ++i)
  {
    BranchInst::Create(ifBlocks[i+1], targetBlocks[i]);
  }

  // Extract scalar values from entry-mask of exec-block.
  Value** masks = new Value*[vectorizationFactor]();
  for (unsigned i=0, e=vectorizationFactor; i<e; ++i)
  {
    ConstantInt* c = ConstantInt::get(context, APInt(32, i));
    masks[i] = ExtractElementInst::Create(mask, c, "", ifBlocks[i]);
  }

  // Generate conditional jump from each if-block to next exec-block/next if-block.
  for (unsigned i=0, e=vectorizationFactor; i<e; ++i)
  {
    BranchInst::Create(targetBlocks[i], ifBlocks[i+1], masks[i], ifBlocks[i]);
  }

  delete [] masks;
}

// - Generate function F_RO_SIMD that performs all updates in a vector context:
//   - Return type is the scalar return type of P.
//   - One input parameter for P.
//   - One input parameter per "other operand" per "update operation".
//   - One input parameter per "update operation" that requires a mask.
//   - One output parameter per "update operation" that has at least one "result user".
//   - Copy the calls to the SCC functions into F_RO.
//   - Wire the new calls to inputs/outputs/other calls.
Function*
generateReductionFunctionSIMD(ReductionVariable& redVar,
                              const unsigned     vectorizationFactor)
{
  assert (false && "not implemented");
  Type* type = redVar.mPhi->getType();
  LLVMContext& context = type->getContext();

  Type* retType = redVar.mResultUser ? type : Type::getVoidTy(context);

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

  // Add input parameters for masks.
  for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
  {
    const ReductionUpdate& redUp = *it->second;
    if (!redUp.mRequiresMask) continue;
    params.push_back(Type::getInt1Ty(context));
  }

  // Add output parameters for "result users".
  for (RedUpMapType::const_iterator it=updates.begin(), E=updates.end(); it!=E; ++it)
  {
    const ReductionUpdate& redUp = *it->second;
    if (redUp.mResultUsers->empty()) continue;
    Type* updateType = redUp.mOperation->getType();
    params.push_back(PointerType::getUnqual(updateType));
  }

  FunctionType* fType = FunctionType::get(retType, params, false);

  Module* mod = redVar.mPhi->getParent()->getParent()->getParent();
  return Function::Create(fType, Function::ExternalLinkage, "red_fn_final", mod);
}

// Transform the reduction SCC:
// - Replace all "in-SCC users" of U with the call's return value.
// - Replace all "result users" of U with the output parameter of the call.
// - Remove U.
void
transformReductionSCCU(ReductionUpdate& redUp)
{
    Instruction* update = redUp.mOperation;

    // We must not use the iterator for the actual "replacement iteration",
    // since this disturbs iteration.
    SmallVector<Instruction*, 2> useVec;
    for (Instruction::use_iterator U=update->use_begin(),
         UE=update->use_end(); U!=UE; ++U)
    {
      assert (isa<Instruction>(*U));
      useVec.push_back(cast<Instruction>(*U));
    }

    for (unsigned i=0, e=useVec.size(); i<e; ++i)
    {
      Instruction* useI = useVec[i];
      Instruction* replaceI;
      if (redUp.mResultUsers->count(useI))
      {
        // This is a "result user".
        // -> Replace with "intermediate result" (return value of call, is a vector after WFV).
        replaceI = redUp.mScalarCall;
      }
      else
      {
        // This is an "in-SCC user".
        // -> Replace with reduction result (output param, still scalar after WFV).

        // Create reload before the use.
        LoadInst* load = new LoadInst(redUp.mIntermediateResultPtr, "redup.interm.reload", useI);
        replaceI = load;
      }

      useI->replaceUsesOfWith(update, replaceI);
    }

    assert (update->use_empty());
    update->eraseFromParent();
    redUp.mOperation = NULL;
}

// Generate vector equivalent F_RO_U_SIMD:
// - Return type remains scalar (same as the return type of F_RO).
// - The input parameters for the "in-SCC operands" remain scalar.
// - The input parameters for the "other operands" are vectorized.
// - The (additional, optional) input parameter for the "update operation mask" is vectorized.
// - The output parameter for the "result users" is vectorized.
Function*
generateReductionFunctionSIMDU(ReductionUpdate& redUp,
                               const unsigned   vectorizationFactor)
{
  Instruction* updateOp = redUp.mOperation;

  assert (updateOp);
  assert (updateOp->getParent());
  assert (updateOp->getParent()->getParent());
  assert (updateOp->getParent()->getParent()->getParent());

  Type* type = updateOp->getType();
  Type* simdType = vectorizeSIMDType(type, vectorizationFactor);
  assert (simdType);
  LLVMContext& context = type->getContext();

  SmallVector<Type*, 2> params;

  for (Instruction::op_iterator O=updateOp->op_begin(),
       OE=updateOp->op_end(); O!=OE; ++O)
  {
    assert (isa<Value>(*O));
    Value* useVal = cast<Value>(*O);
    Type* useType = useVal->getType();
    if (redUp.mOtherOperands->count(useVal))
    {
      // This is an "other operand". -> Input parameter is vectorized.
      params.push_back(vectorizeSIMDType(useType, vectorizationFactor));
    }
    else
    {
      // This is an "in-SCC operand". -> Input parameter remains scalar.
      params.push_back(useType);
    }
  }

  // Add the parameter for the scalar alloca.
  params.push_back(PointerType::getUnqual(type));

  // Set return type if there is at least one "result user".
  Type* retType = redUp.mResultUsers->empty() ?
      Type::getVoidTy(context) :
      simdType;

  // Add parameter for the mask (always, necessary for WFV to always replace the call).
  Type* vecMaskType = vectorizeSIMDType(Type::getInt1Ty(context), vectorizationFactor);
  params.push_back(vecMaskType);
  redUp.mMaskIndex = params.size();

  FunctionType* fType = FunctionType::get(retType, params, false);

  Module* mod = updateOp->getParent()->getParent()->getParent();
  Function* f = Function::Create(fType, Function::ExternalLinkage, "red_fn_SIMD", mod);
  redUp.mAfterWFVFunction = f;

  return f;
}

// Transform the reduction SCC:
// - Replace all "result users" of all "update operations" with the corresponding
//   result of the call.
// - Replace the "update operation" operand of P with the call's return value.
// - Replace the single "result user" behind the loop with the call's return value.
//   - NOTE: I don't think so: That user still refers to P, which should be okay.
// - Remove all "update operations".
void
transformReductionSCC(const ReductionVariable& redVar)
{
  assert (false && "not implemented");
}

} // unnamed namespace

// Create the actual reduction code by moving the mapped update function calls
// to one location and merging their code to produce a correctly reduced result
// and (if required) intermediate values for other users.
//
// For every reduction phi P:
//
//   - Generate function F_RO_SIMD that performs all updates in a vector context:
//     - Return type is the scalar return type of P.
//     - One input parameter for P.
//     - One input parameter per "other operand" per "update operation".
//     - One input parameter per "update operation" that requires a mask.
//     - One output parameter per "update operation" that has at least one "result user".
//     - Copy the calls to the SCC functions into F_RO.
//     - Wire the new calls to inputs/outputs/other calls.
//
//
// - Insert call to F_RO:
//   - *After* the last "update operation" that is a phi or select.
//   - *After* the last "other operand" of any "update operation".
//   - *Before* the first "result user" of any "update operation".
//   - If that is not possible, we may try to move instructions.
//     Otherwise, we can't do anything, so WFV fails due to a "bad" reduction.
//   - Inline the call.
//
// - Transform the reduction SCC (TODO: Update):
//   - Replace all "result users" of all "update operations" with the corresponding
//     result of the call.
//   - Replace the "update operation" operand of P with the call's return value.
//   - Replace the single "result user" behind the loop with the call's return value.
//     - NOTE: I don't think so: That user still refers to P, which should be okay.
//   - Remove all "update operations".
void
NoiseWFVWrapper::finishReductions(RedVarVecType& redVars,
                                  const Loop&    loop)
{
  if (redVars.empty()) return;

  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable& redVar = **it;
    assert (redVar.mPhi && redVar.mStartVal && redVar.mUpdates);

    // Generate function F_RO_SIMD:
    Function* F_RO_SIMD = generateReductionFunctionSIMD(redVar, mVectorizationFactor);

    // Create call if possible.
    // TODO: Decide whether it is impossible to place the call BEFORE starting all
    //       the transformations!
    assert (false && "not implemented");
    //CallInst* call = generateReductionCallSIMD(redVar, F_RO_SIMD, loop);

    // Replace uses etc.
    //transformReductionSCC(redVar);
  }
}
#endif


char NoiseWFVWrapper::ID = 0;
} // namespace llvm

INITIALIZE_PASS_BEGIN(NoiseWFVWrapper, "wfv-wrapper",
                      "wrapper pass around WFV library", false, false)
INITIALIZE_PASS_DEPENDENCY(DominatorTree)
INITIALIZE_PASS_DEPENDENCY(LoopInfo)
INITIALIZE_PASS_END(NoiseWFVWrapper, "wfv-wrapper",
                    "wrapper pass around WFV library", false, false)

#endif

