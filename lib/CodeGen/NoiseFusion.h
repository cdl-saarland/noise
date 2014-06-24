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

namespace llvm {

class Pass;

Pass* createNoiseFusionPass();

}

#endif /* CLANG_CODEGEN_NOISEFUSION_H */
