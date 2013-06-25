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
class BasicBlock;
class BranchInst;
class DominatorTree;
class Function;
class LLVMContext;
class Loop;
class LoopInfo;
class Module;
class PHINode;
class Type;
class Value;
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

  BasicBlock    *PreHeader1;
  BasicBlock    *Header1;
  BranchInst    *HeaderBranch1;
  BasicBlock    *Latch1;

  NoiseFusion();
  virtual ~NoiseFusion() {}

  virtual bool runOnFunction(Function &F);
  virtual void getAnalysisUsage(AnalysisUsage &AU) const;
  void fuse(int ExitIndex, const Loop *Loop2);
};

}

#endif /* CLANG_CODEGEN_NOISEFUSION_H */
