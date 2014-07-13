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

#include "NoiseOptimization.h"

namespace llvm {

  class Value;
  class Module;
  class Function;
  class NamedMDNode;
  class Pass;
  class PassRegistry;
  class CallInst;
  class MDNode;
  class StringRef;
  class FunctionPassManager;

namespace noise {

  struct NoiseFnInfo {
    Function* mOrigFn;
    Function* mMovedFn;
    CallInst* mCall;
    bool      mReinline;
    MDNode*   mOptDesc;

    NoiseFnInfo(Function* origFn, CallInst* call=0, bool reinline=false)
      : mOrigFn(origFn), mMovedFn(0), mCall(call),
      mReinline(reinline), mOptDesc(0)
    {}

    void UpdateOptDesc(MDNode* OptDesc, NoiseDiagnostics &Diag);

    size_t GetNumOptimizations() const;
    NoiseOptimization* GetOptimization(size_t i);
  };

  typedef SmallVector<NoiseFnInfo*, 4> NoiseFnInfoVecType;

  class NoiseOptimizer : public NoiseDiagnostics {
  public:
    NoiseOptimizer(Module *M);
    virtual ~NoiseOptimizer();

    void PerformOptimization();
    void Reassemble();
    void Finalize();
    virtual Module* GetModule() { return Mod; }

  private:
    Module       *Mod;
    Module       *NoiseMod;
    PassRegistry *Registry;
    NamedMDNode  *MD;

    NoiseFnInfoVecType noiseFnInfoVec;
    SmallVector<Function*, 4> dummyFnVec;
  };

}  // end namespace noise
}  // end namespace llvm

#endif
