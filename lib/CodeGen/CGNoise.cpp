//===--- CGNoise.cpp - Emit LLVM Code from Statements ----------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This contains code to emit Stmt nodes as LLVM code.
//
//===----------------------------------------------------------------------===//

#include "CGNoise.h"
#include "NoiseAttrParser.h"

#include "CGDebugInfo.h"
#include "CodeGenModule.h"
#include "CodeGenFunction.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/DerivedTypes.h" // FunctionType
#include "llvm/IR/Constants.h" // UndefValue
#include "llvm/IR/Instructions.h" // CallInst
#include "llvm/IR/Intrinsics.h" // Intrinsics
#include "llvm/IR/Metadata.h"
#include "llvm/Transforms/Utils/Cloning.h" // CloneFunction()
#include "llvm/PassManager.h"


//===----------------------------------------------------------------------===//
//                              Noise Code Emission
//===----------------------------------------------------------------------===//

namespace clang {
namespace noise {

using namespace CodeGen;

NoiseCodeGenerator::NoiseCodeGenerator(CodeGen::CodeGenFunction *Generator)
  : Generator(Generator)
  , AttrParser(Generator->getLLVMContext(), Generator->CGM)
{
}

NoiseCodeGenerator::~NoiseCodeGenerator()
{
}

void NoiseCodeGenerator::EmitError(const SourceLocation &location, const std::string &error)
{
  Generator->CGM.Error(location, error);
  exit(1);
}

bool NoiseCodeGenerator::RegisterFunction(const Decl *D, llvm::Function *Fn, const CGFunctionInfo &FnInfo,
                                          const FunctionArgList &Args)
{
  if(!D || !D->hasAttr<NoiseAttr>())
    return false;
  llvm::Module* Module = Fn->getParent();
  assert(Module);
  llvm::LLVMContext& Context = Fn->getContext();

  llvm::MDNode* noiseOpt = AttrParser.Parse(*D->getAttr<NoiseAttr>());
  llvm::Value* params[] = { Fn, noiseOpt };
  llvm::NamedMDNode* MD = Module->getOrInsertNamedMetadata("noise");
  MD->addOperand(llvm::MDNode::get(Context, llvm::ArrayRef<llvm::Value*>(params)));

  return true;
}

llvm::MDNode* NoiseCodeGenerator::RegisterStmt(const AttributedStmt &S)
{
  // check attribute
  const ArrayRef<const Attr*> &attrs = S.getAttrs();
  const NoiseAttr* noiseAttr = 0;
  // try to detect noise attributes
  for(ArrayRef<const Attr*>::const_iterator it = attrs.begin(), e = attrs.end();
      it != e; ++it) {
    if (!isa<NoiseAttr>(*it))
      continue;
    if (noiseAttr)
      EmitError(S.getLocStart(), "Must not insert more than one noise attribute.");
    noiseAttr = cast<NoiseAttr>(*it);
  }
  assert( noiseAttr && "noiseAttr must be set here" );
  // parse our noise attribute
  return AttrParser.Parse(*noiseAttr);
}

void NoiseCodeGenerator::EmitStmt(llvm::MDNode* NoiseDesc, const Stmt &S)
{

  if (S.getStmtClass() != Stmt::CompoundStmtClass && S.getStmtClass() != Stmt::ForStmtClass)
    EmitError(S.getLocStart(), "Trying to noise unsupported statement.");

  CGBuilderTy& Builder = GetBuilder();
  llvm::LLVMContext& Context = GetModule().getContext();

  // create noise blocks
  llvm::BasicBlock* entry = Generator->createBasicBlock("noise.entry");
  llvm::BasicBlock* body  = Generator->createBasicBlock("noise.body");
  llvm::BasicBlock* exit  = Generator->createBasicBlock("noise.exit");
  llvm::BasicBlock* succ  = Generator->createBasicBlock("noise.succ");
  Generator->EmitBlock(entry, false);
  llvm::BranchInst* entryInstr = Builder.CreateBr(body);

  // emit body of the noise loop
  Generator->EmitBlock(body, false);

  switch(S.getStmtClass())
  {
    case Stmt::CompoundStmtClass:
      Generator->EmitCompoundStmt((const CompoundStmt&)S);
      break;
    case Stmt::ForStmtClass:
      Generator->EmitForStmt((const ForStmt&)S);
      break;
    default:
      assert( false && "trying to noise not supported stmt" );
  }

  llvm::BranchInst* exitInstr = Builder.CreateBr(exit);
  Generator->EmitBlock(exit, false);
  llvm::BranchInst* succInstr = Builder.CreateBr(succ);
  Generator->EmitBlock(succ, false);

  assert( &entry->back() == entryInstr );
  // create our marker node
  llvm::Value* params[] = { entry, exit, NoiseDesc };
  entryInstr->setMetadata("noise_compound_stmt",
                          llvm::MDNode::get(Context, llvm::ArrayRef<llvm::Value*>(params)));

  // Also mark exit and succ blocks so that we can delete them again later.
  exitInstr->setMetadata("noise_tmp_block", llvm::MDNode::get(Context, 0));
  succInstr->setMetadata("noise_tmp_block", llvm::MDNode::get(Context, 0));
}

}
}
