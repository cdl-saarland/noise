//===--- NoiseWFVWrapper.h - Noise Optimizations --------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Noise vectorizer interface
//
//===----------------------------------------------------------------------===//

#ifndef CLANG_CODEGEN_NOISEWFVWRAPPER_H
#define CLANG_CODEGEN_NOISEWFVWRAPPER_H

#include "llvm/Pass.h"
#include "llvm/PassRegistry.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/SetVector.h"

// Forward decl.
class RedVarVecType;

namespace llvm {

class Pass;

Pass* createNoiseWFVPass(const unsigned vectorizationWidth=4,
                         const bool     useAVX=false,
                         const bool     verbose=false);


}

#endif /* CLANG_CODEGEN_NOISEWFVWRAPPER_H */
