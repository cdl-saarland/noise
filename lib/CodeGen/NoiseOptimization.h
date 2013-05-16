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

namespace llvm {

  class LLVMContext;
  class Value;
  class MDNode;
  class PassRegistry;
  class FunctionPassManager;

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

  class NoiseOptimizations {
  public:
    static MDNode* CreateOptimization(LLVMContext& C, ArrayRef<Value*> Values);

    static StringRef GetPassName(NoiseOptimization* Opt);
    static size_t GetNumPassArgs(NoiseOptimization* Opt);

    static bool HasPassArg(NoiseOptimization* Opt, size_t i);
    static Value* GetPassArg(NoiseOptimization* Opt, size_t i);

    static int GetPassArgAsInt(NoiseOptimization* Opt, size_t i);
    static StringRef GetPassArgAsString(NoiseOptimization* Opt, size_t i);

    static void Instantiate(NoiseOptimization* Opt, PassRegistry* Registry,
                            FunctionPassManager& Passes);
  };

}  // end namespace noise
}  // end namespace llvm

#endif
