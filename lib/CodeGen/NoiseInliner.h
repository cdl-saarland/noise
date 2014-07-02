//===--- NoiseInliner.h - Noise Function Inliner --------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Noise inliner definitions
//
//===----------------------------------------------------------------------===//

#ifndef CLANG_CODEGEN_NOISEINLINER_H
#define CLANG_CODEGEN_NOISEINLINER_H

#include <string>
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"

namespace llvm {
namespace noise {
  class NoiseDiagnostics;
}

class Pass;
class BasicBlock;

// Collects all blocks between the block "block" and the end block "endBB"
// TODO: There's functionality inside LLVM for this: llvm::Region
template<unsigned SetSize>
void collectBlocks(BasicBlock* block,
                   BasicBlock* endBB,
                   SmallPtrSet<BasicBlock*, SetSize>& region);

Pass* createNoiseInlinerPass(SmallVector<std::string, 2> &fnNames,
                             noise::NoiseDiagnostics &Diag);

}

#endif /* CLANG_CODEGEN_NOISEINLINER_H */