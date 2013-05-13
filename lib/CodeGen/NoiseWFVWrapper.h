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
    Instruction*             mOperation;
    // The operands that are *not* part of the reduction SCC.
    SetVector<Value*>*       mOtherOperands;
    // The users of this update operation that are *not* part of the reduction SCC (if any).
    SetVector<Instruction*>* mResultUsers;
    // The mask that is required for this update.
    bool                     mRequiresMask;
    // The alloca of the scalar result of this reduction operation (given
    // as output parameter to call).
    AllocaInst*              mReductionResultPtr;
    // The call to the scalar function that replaces the operation before WFV.
    // The result of the call is the result vector that contains the W different
    // results of each iteration.
    CallInst*                mScalarCall;
    // The target function that corresponds to this operation (has a single call only after WFV).
    Function*                mAfterWFVFunction;
    // The mask that is required for this update (valid after call merging after WFV).
    Value*                   mMask;
    // The index of the mask parameter of mAfterWFVFunction.
    int                      mMaskIndex;
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
  void prepareReductionsForWFV(RedVarVecType&                  redVars,
                               const unsigned                  vectorizationFactor,
                               DenseMap<Function*, Function*>& simdMappings);
  // UNUSED
  void demoteReductionPhisToMemory(RedVarVecType&                  redVars,
                                   Instruction*                    indVarUpdate,
                                   const Loop&                     loop,
                                   DenseMap<Function*, Function*>& simdMappings);
  void mapReductionVarInfo(RedVarVecType& redVars,
                           Function*      scalarFn,
                           Function*      simdFn,
                           const Loop&    loop);
  void finishReductions(RedVarVecType& redVars,
                        const Loop&    loop);
};

}

