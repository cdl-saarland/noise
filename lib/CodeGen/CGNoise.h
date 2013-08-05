//===--- CGNoise.h - Code Generator for Noise stmts and functions -*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// The main code generation for noise functions
//
//===----------------------------------------------------------------------===//

#ifndef CLANG_CODEGEN_CODEGENNOISE_H
#define CLANG_CODEGEN_CODEGENNOISE_H

#include "NoiseAttrParser.h"
#include "CodeGenFunction.h"
#include "CGBuilder.h"

namespace clang {
namespace noise {

class NoiseCodeGenerator {
public:
  NoiseCodeGenerator(CodeGen::CodeGenFunction *generator);
  ~NoiseCodeGenerator();

  // Registering phase

  bool RegisterFunction(const Decl *D, llvm::Function *Fn,
                        const CodeGen::CGFunctionInfo &FnInfo,
                        const CodeGen::FunctionArgList &Args);

  llvm::MDNode* RegisterStmt(const AttributedStmt &S);

  // Code emission phase

  void EmitStmt(llvm::MDNode* NoiseDesc, const Stmt &S);

  llvm::Function* GetFunction() { return Generator->CurFn; }
  llvm::Module& GetModule() { return Generator->CGM.getModule(); }
  CodeGen::CGBuilderTy& GetBuilder() { return Generator->Builder; }

private:
  CodeGen::CodeGenFunction *Generator;
  llvm::noise::NoiseAttrParser AttrParser;
};

}  // end namespace noise
}  // end namespace clang

#endif
