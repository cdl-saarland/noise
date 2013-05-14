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

#include "llvm/Pass.h"
#include "llvm/PassRegistry.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SetVector.h"

namespace llvm {
class Module;
class LLVMContext;
class DominatorTree;
class LoopInfo;
class Loop;
class Type;
class PHINode;
class Function;
class Instruction;
class Value;
class AllocaInst;
class CallInst;
class StoreInst;
class Argument;
}

// Forward decl.
class RedVarVecType;

using namespace llvm;

namespace llvm {

//Pass* createNoiseWFVWrapperPass();
void initializeNoiseWFVWrapperPass(PassRegistry&);

struct NoiseWFVWrapper : public FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid

  bool           mFinished;

  Module*        mModule;
  LLVMContext*   mContext;
  DominatorTree* mDomTree;
  LoopInfo*      mLoopInfo;

  unsigned mVectorizationFactor;
  bool mUseAVX;
  bool mUseDivergenceAnalysis;
  bool mVerbose;

  struct ReductionUpdate
  {
    ~ReductionUpdate();

    // The update operation.
    Instruction*      mOperation;
    // The operands that are *not* part of the reduction SCC.
    typedef SmallVector<Value*, 2> OtherOperandsVec;
    OtherOperandsVec* mOtherOperands;
    // The users of this update operation that are *not* part of the reduction SCC (if any).
    typedef SetVector<Instruction*> ResultUsersVec;
    ResultUsersVec*   mResultUsers;
    // The alloca of the scalar result of this reduction operation (given
    // as output parameter to call).
    Instruction*      mIntermediateResultPtr;
  };

  typedef DenseMap<Instruction*, ReductionUpdate*> RedUpMapType;

  struct ReductionVariable
  {
    ~ReductionVariable();

    // The reduction phi in the loop header.
    PHINode*      mPhi;
    // The start value (phi operand from pre header).
    Value*        mStartVal;
    // All update operations that belong to the reduction SCC.
    RedUpMapType* mUpdates;
    // The final reduction result user (if any).
    PHINode*      mResultUser;

    // The position where the reduction operations will be performed after WFV.
    Instruction*  mReductionPos;
    // The scalar reduction function (dummy declaration only).
    Function*     mReductionFn;
    // The call to the scalar reduction function.
    CallInst*     mReductionFnCall;
    // The SIMD reduction function.
    Function*     mReductionFnSIMD;

    // The alloca that stores the final reduction result in the original function.
    AllocaInst*   mResultPtr;

    // The argument of the SIMD reduction function that corresponds to the reduction phi.
    Argument*     mPhiArg;
    // The argument of the SIMD reduction function that corresponds to the result pointer.
    Argument*     mOutArg;
    // The store instruction that writes back the final reduction result to mOutArg.
    StoreInst*    mStoreBack;
    // The value that goes back to the reduction phi from the latch in the original function.
    Instruction*  mBackEdgeVal;
  };

  typedef SmallVector<ReductionVariable*, 2> RedVarVecType;

  explicit NoiseWFVWrapper(const unsigned vectorizationWidth=4,
                           const bool     useAVX=false,
                           const bool     useDivergenceAnalysis=true,
                           const bool     verbose=false);
  virtual ~NoiseWFVWrapper();

  virtual bool runOnFunction(Function &F);

  virtual void getAnalysisUsage(AnalysisUsage &AU) const;

  bool runWFV(Function* noiseFn);

  void collectReductionVariables(RedVarVecType&       redVars,
                                 PHINode*             indVarPhi,
                                 const Loop&          loop,
                                 const DominatorTree& domTree);
};

}

