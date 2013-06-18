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
class Module;
class LLVMContext;
class LoopInfo;
class Loop;
class Type;
class PHINode;
class Function;
}

using namespace llvm;

namespace llvm {

void initializeNoiseFusionPass(PassRegistry&);

struct NoiseFusion : public FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid

  Module*                    mModule;
  LLVMContext*               mContext;
  LoopInfo*                  mLoopInfo;
  const StringRef            mVariable;
  const SmallVector<int, 4>* mValues;

  NoiseFusion();

  virtual ~NoiseFusion() {}

  virtual bool runOnFunction(Function &F);

  virtual void getAnalysisUsage(AnalysisUsage &AU) const;
};

}

#endif /* CLANG_CODEGEN_NOISEFUSION_H */
