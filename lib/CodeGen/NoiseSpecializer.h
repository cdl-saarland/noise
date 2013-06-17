//===--- NoiseSpecializer.h - Noise Specialized Loop Dispatch -------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// The specialized loop dispatch transformation for noise functions
//
//===----------------------------------------------------------------------===//

#ifndef CLANG_CODEGEN_NOISESPECIALIZER_H
#define CLANG_CODEGEN_NOISESPECIALIZER_H

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

//Pass* createNoiseSpecializerPass();
void initializeNoiseSpecializerPass(PassRegistry&);

struct NoiseSpecializer : public FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid

  Module*                    mModule;
  LLVMContext*               mContext;
  LoopInfo*                  mLoopInfo;
  const StringRef            mVariable;
  const SmallVector<int, 4>* mValues;

  NoiseSpecializer();
  NoiseSpecializer(StringRef&                 variable,
                   const SmallVector<int, 4>& values);

  virtual ~NoiseSpecializer();

  virtual bool runOnFunction(Function &F);

  virtual void getAnalysisUsage(AnalysisUsage &AU) const;

  bool runSLD(Function* noiseFn);
};

}

#endif /* CLANG_CODEGEN_NOISESPECIALIZER_H */
