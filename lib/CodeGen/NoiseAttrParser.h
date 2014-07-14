//===--- NoiseAttrParser.h - Noise Specific Optimizations ------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// The parser for noise attributes
//
//===----------------------------------------------------------------------===//

#ifndef CLANG_CODEGEN_NOISEATTRPARSER_H
#define CLANG_CODEGEN_NOISEATTRPARSER_H

namespace clang {
  class NoiseAttr;
  namespace CodeGen {
    class CodeGenModule;
  }
}

namespace llvm {

  class LLVMContext;
  class MDNode;

namespace noise {

  class NoiseDiagnostics;

  /*
   MDNode from the Parse method contains:
   - PassDesc0 (see above)
   - PassDesc1 (see above)
   - ...
   - PassDescN (see above)
   */

  class NoiseAttrParser {
  public:
    NoiseAttrParser(LLVMContext &C, clang::CodeGen::CodeGenModule &CGM);
    ~NoiseAttrParser();

    MDNode* Parse(const clang::NoiseAttr &attr);

  private:
    LLVMContext &C;
    clang::CodeGen::CodeGenModule &CGM;
  };

}  // end namespace noise
}  // end namespace llvm

#endif
