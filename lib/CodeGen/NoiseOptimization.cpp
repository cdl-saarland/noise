//===--- NoiseOptimization.cpp - Noise Specific Optimizations ---*- C++ -*-===//
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

#include "NoiseOptimization.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Constants.h"
#include "llvm/PassManager.h"
#include "llvm/PassRegistry.h"

namespace llvm {
namespace noise {

MDNode* NoiseOptimizations::CreateOptimization(LLVMContext& C, ArrayRef<Value*> Values)
{
  return MDNode::get(C, Values);
}

StringRef NoiseOptimizations::GetPassName(NoiseOptimization* Opt)
{
  assert( isa<MDString>(Opt->getOperand(0)) );
  return cast<MDString>(Opt->getOperand(0))->getString();
}

size_t NoiseOptimizations::GetNumPassArgs(NoiseOptimization* Opt)
{
  return Opt->getNumOperands() - 1U;
}

Value* NoiseOptimizations::GetPassArg(NoiseOptimization* Opt, size_t i)
{
  return Opt->getOperand(i + 1U);
}

bool NoiseOptimizations::HasPassArg(NoiseOptimization* Opt, size_t i)
{
  return GetNumPassArgs(Opt) > i;
}

int NoiseOptimizations::GetPassArgAsInt(NoiseOptimization* Opt, size_t i)
{
  return cast<ConstantInt>(GetPassArg(Opt, i))->getSExtValue();
}

StringRef NoiseOptimizations::GetPassArgAsString(NoiseOptimization* Opt, size_t i)
{
  return cast<MDString>(GetPassArg(Opt, i))->getString();
}

}
}
