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

#include <sstream>

#include <wfvInterface.h>

using namespace llvm;

namespace llvm {

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
  mSIMDWidth(vectorizationWidth),
  mUseAVX(useAVX),
  mUseDivergenceAnalysis(useDivergenceAnalysis),
  mVerbose(verbose)
{
  initializeNoiseWFVWrapperPass(*PassRegistry::getPassRegistry());
}

NoiseWFVWrapper::~NoiseWFVWrapper()
{
}

// Create SIMD type from scalar type.
// -> only 32bit-float, integers <= 32bit, pointers, arrays and structs allowed
// -> no scalar datatypes allowed
// -> no pointers to pointers allowed
// TODO: i8* should not be transformed to <4 x i8>* !
Type*
NoiseWFVWrapper::vectorizeSIMDType(Type* oldType, const unsigned simdWidth)
{
  if (oldType->isFloatTy() ||
      (oldType->isIntegerTy() && oldType->getPrimitiveSizeInBits() <= 32U))
  {
    return VectorType::get(oldType, simdWidth);
  }

  switch (oldType->getTypeID())
  {
  case Type::PointerTyID:
    {
      PointerType* pType = cast<PointerType>(oldType);
      return PointerType::get(vectorizeSIMDType(pType->getElementType(), simdWidth),
                              pType->getAddressSpace());
    }
  case Type::ArrayTyID:
    {
      ArrayType* aType = cast<ArrayType>(oldType);
      return ArrayType::get(vectorizeSIMDType(aType->getElementType(), simdWidth),
                            aType->getNumElements());
    }
  case Type::StructTyID:
    {
      StructType* sType = cast<StructType>(oldType);
      std::vector<Type*> newParams;
      for (unsigned i=0; i<sType->getNumContainedTypes(); ++i)
      {
        newParams.push_back(vectorizeSIMDType(sType->getElementType(i), simdWidth));
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

  // Make sure there are no values that are live across loop boundaries (LALB).
  // This is because WFV only supports loops without loop-carried dependencies.
  // NOTE: We rely on LCSSA here, which allows us to simply test if there is
  //       a phi in the exit block. If so, there are dependencies.
  assert (!isa<PHINode>(exitBB->begin()) &&
          "vectorization of loops with loop-carried dependencies not supported!");

  // Do some sanity checks to test assumptions about our construction.
  assert (preheaderBB == &noiseFn->getEntryBlock());
  assert (preheaderBB->getTerminator()->getNumSuccessors() == 1);
  assert (headerBB == preheaderBB->getTerminator()->getSuccessor(0));
  assert (isa<PHINode>(headerBB->begin()));
  assert (cast<PHINode>(headerBB->begin())->getNumIncomingValues() == 2);

  // Extract the loop body.
  // This is a non-trivial task, since the code that is not part of the body
  // (induction variable increment etc.) in the C code is part of it in LLVM IR.
  // This function attempts to split out only the relevant parts of the code.
  PHINode* indVarPhi = 0;
  SmallVector<BasicBlock*, 4> loopBody;
  Function* loopBodyFn = extractLoopBody(loop, indVarPhi, loopBody);
  if (!loopBodyFn || !indVarPhi)
  {
    errs() << "ERROR: Loop body extraction failed!\n";
    return false;
  }

  assert (loopBodyFn->getNumUses() == 1);
  CallInst* loopBodyCall = cast<CallInst>(*loopBodyFn->use_begin());
  assert (loopBodyCall->use_empty());

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
  assert (indVarArg);
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
  WFVInterface::WFVInterface wfvInterface(mModule,
                                          &mModule->getContext(),
                                          loopBodyFn,
                                          simdFn,
                                          mSIMDWidth,
                                          mUseAVX,
                                          mUseDivergenceAnalysis,
                                          mVerbose);

  // Add semantics to the induction variable vector.
  wfvInterface.addSIMDSemantics(*indVarArg, false, true, false, true, false, true);

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

  assert (loopBodyFn);

  // The generated function is not required anymore.
  simdFn->eraseFromParent();

  // Finally, re-inline the loop body function into the noise function.
  assert (loopBodyFn->getNumUses() == 1 &&
          "There should be only one call to the extracted loop body function");
  assert (isa<CallInst>(*loopBodyFn->use_begin()));
  CallInst* call = cast<CallInst>(*loopBodyFn->use_begin());
  InlineFunctionInfo IFI;
  InlineFunction(call, IFI);

  // Remove the now inlined loop body function again.
  assert (loopBodyFn->use_empty());
  loopBodyFn->eraseFromParent();

  return true;
}

template<unsigned S>
Function*
NoiseWFVWrapper::extractLoopBody(Loop* loop,
                                 PHINode*& indVarPhi,
                                 SmallVector<BasicBlock*, S>& loopBody)
{
  assert (loop);
  assert (!indVarPhi);

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

  // Get loop induction variable phi.
  indVarPhi = loop->getCanonicalInductionVariable();
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
  BasicBlock* newLatchBB = SplitBlock(latchBB, indVarUpdate, mDomTree);
  newLatchBB->setName(latchBB->getName()+".wfv.latch");

  // latchBB is now the part of the latch that is only the body.
  loopBody.push_back(latchBB);

  CodeExtractor extractor(loopBody, mDomTree, false);
  assert (extractor.isEligible());
  Function* bodyFn = extractor.extractCodeRegion();
  assert (bodyFn);

  // Now, adjust the original loop.
  // Increment by 'simdWidth' instead of 1.
  Constant* simdWidthConst = ConstantInt::get(indVarUpdate->getType(), mSIMDWidth, false);
  Instruction* newIndVarUpdate = BinaryOperator::Create(Instruction::Add,
                                                        indVarPhi,
                                                        simdWidthConst,
                                                        "wfv.inc",
                                                        indVarUpdate);
  indVarUpdate->moveBefore(newIndVarUpdate);
  indVarUpdate->replaceAllUsesWith(newIndVarUpdate);
  newIndVarUpdate->replaceUsesOfWith(newIndVarUpdate, indVarUpdate);

  return bodyFn;
}

void
NoiseWFVWrapper::getAnalysisUsage(AnalysisUsage &AU) const
{
  AU.addRequired<DominatorTree>();
  AU.addRequired<LoopInfo>();
}

char NoiseWFVWrapper::ID = 0;
} // namespace llvm

INITIALIZE_PASS_BEGIN(NoiseWFVWrapper, "wfv-wrapper",
                      "wrapper pass around WFV library", false, false)
INITIALIZE_PASS_DEPENDENCY(DominatorTree)
INITIALIZE_PASS_DEPENDENCY(LoopInfo)
INITIALIZE_PASS_END(NoiseWFVWrapper, "wfv-wrapper",
                    "wrapper pass around WFV library", false, false)

#endif

