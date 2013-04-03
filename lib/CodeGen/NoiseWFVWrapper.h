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
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/DenseMap.h"

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
}

using namespace llvm;

namespace llvm {

//Pass* createNoiseWFVWrapperPass();
void initializeNoiseWFVWrapperPass(PassRegistry&);

struct NoiseWFVWrapper : public FunctionPass {
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

  explicit NoiseWFVWrapper(const unsigned vectorizationWidth=4,
                           const bool     useAVX=false,
                           const bool     useDivergenceAnalysis=true,
                           const bool     verbose=false);
  virtual ~NoiseWFVWrapper();

  Type* vectorizeSIMDType(Type* oldType, const unsigned VectorizationFactor);

  virtual bool runOnFunction(Function &F);

  bool runWFV(Function* noiseFn);

  void handleReductions(Loop*                           loop,
                        PHINode*                        indVarPhi,
                        const unsigned                  vectorizationFactor,
                        DenseMap<Function*, Function*>& simdMappings);

  void generateIfCascade(Instruction*   inst,
                         Value*         mask,
                         BasicBlock**   ifBlocks,
                         BasicBlock**   targetBlocks,
                         const unsigned vectorizationFactor);
  Function* generateReductionFunction(Instruction* updateOp, const bool requiresRetVal);
  Function* generateReductionFunctionSIMD(Instruction*   updateOp,
                                          const unsigned vectorizationFactor,
                                          const bool     requiresRetVal,
                                          const bool     requiresMask);

  template<unsigned S>
  Function* extractLoopBody(Loop*                        loop,
                            PHINode*                     indVarPhi,
                            Instruction*                 indVarUpdate,
                            SmallVector<BasicBlock*, S>& loopBody);

  virtual void getAnalysisUsage(AnalysisUsage &AU) const;
};

}

