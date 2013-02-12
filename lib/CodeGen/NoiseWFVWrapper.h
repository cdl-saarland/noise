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

namespace llvm {
class Module;
class LLVMContext;
class DominatorTree;
class LoopInfo;
class Loop;
class Type;
class PHINode;
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

  static const unsigned simdWidth = 4;
  static const bool use_avx = false;
  static const bool use_divergence_analysis = true;
  static const bool verbose = false;

  NoiseWFVWrapper();
  virtual ~NoiseWFVWrapper();

  Type* vectorizeSIMDType(Type* oldType, const unsigned simdWidth);

  virtual bool runOnFunction(Function &F);

  bool runWFV(Function* noiseFn);

  template<unsigned S>
  Function* extractLoopBody(Loop* loop,
                            PHINode*& indVarPhi,
                            SmallVector<BasicBlock*, S>& loopBody);

  virtual void getAnalysisUsage(AnalysisUsage &AU) const;
};

}

