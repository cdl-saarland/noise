//===--- NoiseFusion.h - Noise Fusion Loop Dispatch -----------------------===//
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

#ifndef CLANG_CODEGEN_NOISEFUSION_H
#define CLANG_CODEGEN_NOISEFUSION_H

#include "llvm/Pass.h"
#include "llvm/PassRegistry.h"
#include "llvm/ADT/SmallVector.h"

namespace llvm {
class DominatorTree;
class Function;
class LLVMContext;
class Loop;
class LoopInfo;
class Module;
class Type;
}

namespace llvm {

void initializeNoiseFusionPass(PassRegistry&);

struct NoiseFusion : public FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid

  Module        *mModule;
  LLVMContext   *mContext;
  LoopInfo      *mLoopInfo;
  DominatorTree *mDomTree;

  NoiseFusion();
  virtual ~NoiseFusion() {}

  virtual bool runOnFunction(Function &F);
  virtual void getAnalysisUsage(AnalysisUsage &AU) const;
  void fuse(const Loop *Loop1, const Loop *Loop2);
};

}

#endif /* CLANG_CODEGEN_NOISEFUSION_H */
