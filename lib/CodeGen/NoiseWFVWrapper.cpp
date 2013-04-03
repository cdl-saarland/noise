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

// Create SIMD type from scalar type.
// -> only 32bit-float, integers <= 32bit, pointers, arrays and structs allowed
// -> no scalar datatypes allowed
// -> no pointers to pointers allowed
// TODO: i8* should not be transformed to <4 x i8>* !
Type*
NoiseWFVWrapper::vectorizeSIMDType(Type* oldType, const unsigned vectorizationFactor)
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

  // Get loop induction variable phi.
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


  DenseMap<Function*, Function*> simdMappings;
  handleReductions(loop, indVarPhi, mVectorizationFactor, simdMappings);

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
  SmallVector<BasicBlock*, 4> loopBody;
  Function* loopBodyFn = extractLoopBody(loop, indVarPhi, indVarUpdate, loopBody);
  if (!loopBodyFn)
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
  for (DenseMap<Function*, Function*>::iterator it=simdMappings.begin(),
       E=simdMappings.end(); it!=E; ++it)
  {
    const int maskIdx = it->second->getFunctionType()->getNumParams() <= 2 ? -1 : 2;
    const bool mayHaveSideEffects = maskIdx != -1;
    wfvInterface.addSIMDMapping(*it->first, *it->second, maskIdx, mayHaveSideEffects);
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

  // Inline reduction functions (if any) into the vectorized code.
  // The "scalar" dummy reduction function can't be erased until the temporary
  // function that served as the basis for WFV was erased.
  for (DenseMap<Function*, Function*>::iterator it=simdMappings.begin(),
       E=simdMappings.end(); it!=E; ++it)
  {
    Function* fn = it->second;

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

namespace {

struct ReductionVariable
{
  ReductionVariable()
  : mStartVal(0), mPhi(0), mUpdateOp(0), mOtherOperand(0), mResult(0), mRequiresMask(false)
  {}

  Value*       mStartVal;
  PHINode*     mPhi;
  Instruction* mUpdateOp;
  Value*       mOtherOperand;
  PHINode*     mResult;
  bool         mRequiresMask;
};

typedef SmallVector<ReductionVariable*, 2> RedVarVecType;

void
collectReductionVariables(Loop*                loop,
                          PHINode*             indVarPhi,
                          const DominatorTree& domTree,
                          RedVarVecType&       redVars)
{
  assert (loop && indVarPhi);

  BasicBlock* preheaderBB = loop->getLoopPreheader();
  BasicBlock* headerBB    = loop->getHeader();
  BasicBlock* latchBB     = loop->getLoopLatch();
  BasicBlock* exitBB      = loop->getUniqueExitBlock();

  for (BasicBlock::iterator I=headerBB->begin(),
       IE=headerBB->end(); I!=IE; ++I)
  {
    if (headerBB->getFirstNonPHI() == I) break;
    if (indVarPhi == I) continue;

    PHINode* phi = cast<PHINode>(I);
    outs() << "  reduction candidate phi: " << *phi << "\n";

    ReductionVariable* redVar = new ReductionVariable();
    redVar->mPhi = phi;
    assert (phi->getNumUses() <= 2 &&
            "Phi should have at most two uses: the phis in the header and the exit block!");

    assert (phi->getIncomingValueForBlock(preheaderBB));
    redVar->mStartVal = phi->getIncomingValueForBlock(preheaderBB);
    outs() << "    start value: " << *redVar->mStartVal << "\n";

    assert (phi->getIncomingValueForBlock(latchBB));
    assert (isa<Instruction>(phi->getIncomingValueForBlock(latchBB)));
    Instruction* updateOp = cast<Instruction>(phi->getIncomingValueForBlock(latchBB));
    outs() << "    update op: " << *updateOp << "\n";
    assert (updateOp->isBinaryOp() && "Can only handle reductions with binary operations");
    assert (updateOp->getNumUses() <= 2 &&
            "Update op should have at most two uses: the phis in the header and the exit block!");
    redVar->mUpdateOp = updateOp;

    Instruction::op_iterator O = updateOp->op_begin();
    Value* op0 = *O++;
    Value* op1 = *O;
    redVar->mOtherOperand = op0 == phi ? op1 : op0;
    outs() << "    other operand: " << *redVar->mOtherOperand << "\n";

    for (BasicBlock::iterator I2=exitBB->begin(),
         IE2=exitBB->end(); I2!=IE2; ++I2)
    {
      if (exitBB->getFirstNonPHI() == I2) break;
      PHINode* exitPhi = cast<PHINode>(I2);
      assert (exitPhi->getNumIncomingValues() == 1);
      if (exitPhi->getIncomingValue(0) != updateOp &&
          exitPhi->getIncomingValue(0) != phi)
      {
        continue;
      }
      redVar->mResult = exitPhi;
      break;
    }
    assert (redVar->mResult && "Could not find corresponding phi in exit block!");
    outs() << "    result phi: " << *redVar->mResult << "\n";

    // Determine if we require masked reduction.
    // NOTE: It would be beneficial to have divergence information here.
    redVar->mRequiresMask = !domTree.dominates(updateOp->getParent(), latchBB);
    outs() << "    requires mask? " << redVar->mRequiresMask << "\n";

    redVars.push_back(redVar);
  }
}

} // unnamed namespace


// State after execution of this function:
// - parent block of inst is split at the position of inst
// - first if-block is former parent block of 'inst' ("upper part")
// - last if-block is new block containing "lower part" of former parent block of 'inst'
// - each if-block holds mask extraction and scalar comparison if mask-instance is true
// - each target-block only holds an unconditional branch to the next if-block
void
NoiseWFVWrapper::generateIfCascade(Instruction*   inst,
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

Function*
NoiseWFVWrapper::generateReductionFunction(Instruction* updateOp)
{
  assert (updateOp);
  assert (updateOp->getParent());
  assert (updateOp->getParent()->getParent());
  assert (updateOp->getParent()->getParent()->getParent());

  Type* type = updateOp->getType();
  LLVMContext& context = type->getContext();

  SmallVector<Type*, 2> params;
  params.push_back(type);
  params.push_back(PointerType::getUnqual(type));
  FunctionType* fType = FunctionType::get(Type::getVoidTy(context), params, false);

  Module* mod = updateOp->getParent()->getParent()->getParent();
  return Function::Create(fType, Function::ExternalLinkage, "red_fn", mod);
}

Function*
NoiseWFVWrapper::generateReductionFunctionSIMD(Instruction*   updateOp,
                                               const unsigned vectorizationFactor,
                                               const bool     requiresMask)
{
  assert (updateOp);
  assert (updateOp->isBinaryOp());
  assert (updateOp->getParent());
  assert (updateOp->getParent()->getParent());
  assert (updateOp->getParent()->getParent()->getParent());

  Type* type = updateOp->getType();
  Type* simdType = vectorizeSIMDType(type, vectorizationFactor);
  assert (simdType);
  LLVMContext& context = type->getContext();

  SmallVector<Type*, 2> params;
  // Add the parameter for the operand vector.
  params.push_back(simdType);
  // Add the parameter for the alloca.
  params.push_back(PointerType::getUnqual(type));
  // Add parameter for the mask (if required).
  if (requiresMask)
  {
    params.push_back(VectorType::get(Type::getInt1Ty(context), vectorizationFactor));
  }
  FunctionType* fType = FunctionType::get(Type::getVoidTy(context), params, false);

  Module* mod = updateOp->getParent()->getParent()->getParent();
  Function* f = Function::Create(fType, Function::ExternalLinkage, "red_fn_SIMD", mod);

  // Find out what operation we are creating.
  const Instruction::BinaryOps opcode = (Instruction::BinaryOps)updateOp->getOpcode();

  // Create reduction code.
  // *A <- *A (RO) O_SIMD[0] (RO) O_SIMD[1] (RO) ... (RO) O_SIMD[W-1]
  BasicBlock* entryBB = BasicBlock::Create(context, "entry", f);

  Function::arg_iterator it = f->arg_begin();
  Argument* O = it++;
  Argument* A = it++;
  Argument* mask = requiresMask ? it : 0;
  LoadInst* load = new LoadInst(A, "A", entryBB);

  ReturnInst* retI = ReturnInst::Create(context, entryBB);

  // If there is no mask, simply generate W extracts and W reduction operations.
  // Otherwise, generate an if-cascade that only performs the reduction if the
  // corresponding mask element is true.
  Instruction* reductionOp = load;
  if (!mask)
  {
    for (unsigned i=0; i<vectorizationFactor; ++i)
    {
        ConstantInt* c = ConstantInt::get(context, APInt(32, i));
        Instruction* extract = ExtractElementInst::Create(O, c, "O", retI);
        reductionOp = BinaryOperator::Create(opcode, reductionOp, extract, "red", retI);
    }
  }
  else
  {
    // Create if-cascade:
    // Each if-block holds mask extraction and scalar comparison if mask-instance is true.
    // Each use-block holds scalar use.
    BasicBlock** ifBlocks     = new BasicBlock*[vectorizationFactor+1]();
    BasicBlock** targetBlocks = new BasicBlock*[vectorizationFactor]();

    // Start splitting at the return.
    generateIfCascade(retI, mask, ifBlocks, targetBlocks, vectorizationFactor);

    // Create reduction operations in the correct blocks.
    for (unsigned i=0; i<vectorizationFactor; ++i)
    {
      Instruction* insertBefore = targetBlocks[i]->getTerminator();
      ConstantInt* c = ConstantInt::get(context, APInt(32, i));
      Instruction* extract = ExtractElementInst::Create(O, c, "O", insertBefore);
      Instruction* newRedOp = BinaryOperator::Create(opcode, reductionOp, extract, "red", insertBefore);

      // Create phis in the if blocks.
      assert (!ifBlocks[i+1]->empty());
      Instruction* phiPos = ifBlocks[i+1]->getFirstNonPHI();

      PHINode* phi = PHINode::Create(type, 2U, "", phiPos);
      phi->addIncoming(newRedOp, targetBlocks[i]);
      // Insert value from previous if (the load if i == 0, last phi otherwise)
      // where the mask is 0.
      phi->addIncoming(reductionOp, ifBlocks[i]);

      reductionOp = phi;
    }

    delete [] targetBlocks;
    delete [] ifBlocks;
  }

  new StoreInst(reductionOp, A, retI);

  return f;
}

// For each reduction, Perform "reg2mem" of the variable, extract the update
// into a function, and create a SIMD function which performs the reduction.
void
NoiseWFVWrapper::handleReductions(Loop*                           loop,
                                  PHINode*                        indVarPhi,
                                  const unsigned                  vectorizationFactor,
                                  DenseMap<Function*, Function*>& simdMappings)
{
  assert (loop && indVarPhi);
  assert (simdMappings.empty());

  BasicBlock* preheaderBB = loop->getLoopPreheader();
  BasicBlock* headerBB    = loop->getHeader();
  BasicBlock* exitBB      = loop->getUniqueExitBlock();

  outs() << "function: " << *indVarPhi->getParent()->getParent() << "\n";

  // Identify reduction variables.
  // Given by phi and update operation (+,-,*,/,%,<<,>>,&,|,^,&&,||,min,max).
  RedVarVecType redVars;
  collectReductionVariables(loop, indVarPhi, *mDomTree, redVars);

  // TODO: Make sure there is no interference between reduction variables.

  // For each reduction variable phi P, start value S, update operation U,
  // other operand O, reduction result R, reduction operator RO
  // % U must have exactly two uses: P and R
  // - Generate an alloca A
  // - Generate a store in the preheader: *A <- S
  // - Generate a reduction function F_RO(O, A)
  // - Generate vector equivalent F_RO_SIMD(O_SIMD, A) that performs the reduction
  //   - *A <- *A (RO) O_SIMD[0] (RO) O_SIMD[1] (RO) ... (RO) O_SIMD[W-1]
  // - Add mapping RF -> RF_SIMD to WFV
  // - Insert call to RF before U
  // - Generate a load L_P in the header: L_P <- *A
  // - Replace uses of P by L_P
  // - Generate a load L_R in the exit block: L_R <- *A
  // - Replace uses of R by L_R
  // - Remove P, U, and R
  Instruction* allocaInsertPos = headerBB->getParent()->getEntryBlock().getFirstNonPHI();
  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    ReductionVariable* redVar = *it;
    Value*       S = redVar->mStartVal;
    PHINode*     P = redVar->mPhi;
    Instruction* U = redVar->mUpdateOp;
    Value*       O = redVar->mOtherOperand;
    PHINode*     R = redVar->mResult;
    assert (S && P && U && O && R);

    const bool requiresMask = redVar->mRequiresMask;

    outs() << "  S: " << *S << "\n";
    outs() << "  P: " << *P << "\n";
    outs() << "  U: " << *U << "\n";
    outs() << "  O: " << *O << "\n";
    outs() << "  R: " << *R << "\n";

    Type* type = P->getType();

    assert (type == S->getType());
    assert (type == U->getType());
    assert (type == O->getType());
    assert (type == R->getType());

    AllocaInst* A = new AllocaInst(type, "red.storage", allocaInsertPos);
    outs() << "  alloca: " << *A << "\n";

    new StoreInst(S, A, preheaderBB->getTerminator());

    Function* F_RO      = generateReductionFunction(U);
    Function* F_RO_SIMD = generateReductionFunctionSIMD(U, vectorizationFactor, requiresMask);
    assert (F_RO && F_RO_SIMD);
    outs() << "  F_RO: " << *F_RO << "\n";
    outs() << "  F_RO_SIMD: " << *F_RO_SIMD << "\n";

    simdMappings[F_RO] = F_RO_SIMD;

    SmallVector<Value*, 2> args;
    args.push_back(O);
    args.push_back(A);
    CallInst::Create(F_RO, args, "", U);

    LoadInst* L_P = new LoadInst(A, "red.reload.header", headerBB->getFirstNonPHI());
    LoadInst* L_R = new LoadInst(A, "red.reload.exit",   exitBB->getFirstNonPHI());
    outs() << "  L_P: " << *L_P << "\n";
    outs() << "  L_R: " << *L_R << "\n";

    P->replaceAllUsesWith(L_P);
    R->replaceAllUsesWith(L_R);

    P->eraseFromParent();
    R->eraseFromParent();
    assert (U->use_empty() && "uses of U (= P, R) should be deleted now");
    U->eraseFromParent();
  }

  outs() << "function after reduction transformation: " << *indVarPhi->getParent()->getParent() << "\n";

  for (RedVarVecType::iterator it=redVars.begin(), E=redVars.end(); it!=E; ++it)
  {
    delete *it;
  }
}

template<unsigned S>
Function*
NoiseWFVWrapper::extractLoopBody(Loop*                        loop,
                                 PHINode*                     indVarPhi,
                                 Instruction*                 indVarUpdate,
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
  BasicBlock* newLatchBB = SplitBlock(latchBB, indVarUpdate, mDomTree);
  newLatchBB->setName(latchBB->getName()+".wfv.latch");

  // latchBB is now the part of the latch that is only the body.
  loopBody.push_back(latchBB);

  CodeExtractor extractor(loopBody, mDomTree, false);
  assert (extractor.isEligible());
  Function* bodyFn = extractor.extractCodeRegion();
  assert (bodyFn);

  // Now, adjust the original loop.
  // Increment by 'vectorizationFactor' instead of 1.
  Constant* vecFactorConst = ConstantInt::get(indVarUpdate->getType(), mVectorizationFactor, false);
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

