//===--- NoiseSpecializer.h - Noise Specialized Dispatch -------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// The specialized dispatch transformation for noise functions
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
  const std::string          mVariable;
  const SmallVector<int, 4>* mValues;

  NoiseSpecializer();
  NoiseSpecializer(const std::string&         variable,
                   const SmallVector<int, 4>* values);

  virtual ~NoiseSpecializer();

  virtual bool runOnFunction(Function &F);

  virtual void getAnalysisUsage(AnalysisUsage &AU) const;

  bool runSpecializer(Function* noiseFn);
};

}

#endif /* CLANG_CODEGEN_NOISESPECIALIZER_H */
