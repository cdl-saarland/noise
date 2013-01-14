//===--- NoiseOptimizer.h - Noise Specific Optimizations --------*- C++ -*-===//
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

#ifndef CLANG_CODEGEN_NOISEOPTIMIZER_H
#define CLANG_CODEGEN_NOISEOPTIMIZER_H

#include "llvm/ADT/SmallVector.h"

namespace llvm {

  class Module;
  class Function;
  class NamedMDNode;
  class PassRegistry;
  class CallInst;
  class MDString;

namespace noise {

  struct NoiseFnInfo {
    Function* mOrigFn;
    Function* mMovedFn;
    CallInst* mCall;
    bool      mReinline;
    MDString* mOptString;

    NoiseFnInfo(Function* origFn, CallInst* call=0, bool reinline=false)
      : mOrigFn(origFn), mMovedFn(0), mCall(call),
      mReinline(reinline), mOptString(0)
    {}
  };

  typedef SmallVector<NoiseFnInfo*, 4> NoiseFnInfoVecType;

  class NoiseOptimizer {
  public:
    NoiseOptimizer(Module *M);
    ~NoiseOptimizer();

    void PerformOptimization();
    void Reassemble();
    void Finalize();

  private:
    Module       *Mod;
    Module       *NoiseMod;
    PassRegistry *Registry;
    NamedMDNode  *MD;

    NoiseFnInfoVecType noiseFnInfoVec;
  };

}  // end namespace noise
}  // end namespace llvm

#endif
