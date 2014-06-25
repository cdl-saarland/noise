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

#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/SmallVector.h"

using namespace llvm;

namespace llvm {

class Pass;
Pass* createNoiseSpecializerPass(StringRef variable, const SmallVector<int, 4> &values);

}

#endif /* CLANG_CODEGEN_NOISESPECIALIZER_H */
