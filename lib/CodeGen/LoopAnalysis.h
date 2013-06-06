//===--- LoopAnalysis.h - Analyze Loops for Vectorization -------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Analyze loops for vectorization purposes.
//
//===----------------------------------------------------------------------===//

#ifndef CLANG_CODEGEN_LOOPANALYSIS_H
#define CLANG_CODEGEN_LOOPANALYSIS_H

namespace llvm {
  class Module;

namespace loopanalysis {

class LoopAnalysis {
public:
  LoopAnalysis(Module *M);
  ~LoopAnalysis();
  void Analyze();
private:
  Module       *Mod;
};

}  // namespace loopanalysis
}  // namespace llvm

#endif
