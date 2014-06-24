//===--- NoiseOptimization.h - Noise Specific Optimizations -----*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Noise optimization representation
//
//===----------------------------------------------------------------------===//

#ifndef CLANG_CODEGEN_NOISEOPTIMIZATION_H
#define CLANG_CODEGEN_NOISEOPTIMIZATION_H

#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"

namespace llvm {

  class LLVMContext;
  class Value;
  class MDNode;
  class PassRegistry;
  class Pass;
  class PassManagerBase;

namespace noise {

  // Avoid the explicit creation of custom classes
  // which makes it harder to maintain the code
  typedef MDNode NoiseOptimization;

  /*
   Pass description from the parser contains:
   - PassName
   - Arg0
   - Arg1
   - ...
   - ArgN

   -> NumOperands = NumArgs() - 1
   */

#define NOISEOPTIMIZATION_TYPES(X) \
  X( OPT, opt ) \
  X( INLINE, inline ) \
  X( LOOPUNROLL, unroll ) \
  X( LOOPFUSION, loop-fusion ) \
  X( SPECIALIZE, specialize ) \
  X( VECTORIZE, wfv )

  enum NoiseOptimizationType {
#define TYPE_ELEM(Type, Name) \
    NOISE_OPTIMIZATION_TYPE_ ## Type,
    NOISEOPTIMIZATION_TYPES(TYPE_ELEM)
#undef TYPE_ELEM
    NOISE_OPTIMIZATION_TYPE_LLVMPASS
  };

  class NoiseOptimizationInfo {
  public:
    NoiseOptimizationInfo(NoiseOptimization *Opt);

    NoiseOptimizationType GetType() const { return type; }

    StringRef GetPassName() const;
    size_t GetNumArgs() const;
    Value* GetArg(size_t i) const;
    bool HasArg(size_t i) const;

    int GetArgAsInt(size_t i) const;
    StringRef GetArgAsString(size_t i) const;

    Value* operator[](size_t i) const {
        return GetArg(i);
    }

  private:
    NoiseOptimization *opt;
    NoiseOptimizationType type;
  };

  class NoiseOptimizations {
  public:
    NoiseOptimizations(PassRegistry &Registry);

    static NoiseOptimization* CreateOptimization(LLVMContext &C, ArrayRef<Value*> Values);

    void Register(NoiseOptimization *Opt);
    void Register(Pass *Pass);
    void RegisterDefaultOpts();
    void Populate(PassManagerBase &Manager);

    PassRegistry& GetRegistry() { return registry; }

  private:
    PassRegistry &registry;
    std::vector<Pass*> passes;
  };

}  // end namespace noise
}  // end namespace llvm

#endif
