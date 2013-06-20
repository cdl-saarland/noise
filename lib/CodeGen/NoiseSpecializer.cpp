//===--- NoiseSpecializer.cpp - Noise Specialized Dispatch -----------===//
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

#include "NoiseSpecializer.h"

#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/PassRegistry.h"
#include "llvm/PassManagers.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Transforms/Utils/Cloning.h" // CloneFunction()
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h" // FunctionType
#include "llvm/IR/Constants.h" // UndefValue
#include "llvm/IR/Instructions.h" // CallInst

#include <sstream>

using namespace llvm;

namespace llvm {

#if 0
Pass*
createNoiseSpecializerPass()
{
    return new NoiseSpecializer();
}
#endif


NoiseSpecializer::NoiseSpecializer()
: FunctionPass(ID), mVariable(""), mValues(0)
{
    assert (false && "empty constructor must never be called!");
    initializeNoiseSpecializerPass(*PassRegistry::getPassRegistry());
}

NoiseSpecializer::NoiseSpecializer(const std::string&         variable,
                                   const SmallVector<int, 4>* values)
: FunctionPass(ID), mVariable(variable), mValues(values)
{
    initializeNoiseSpecializerPass(*PassRegistry::getPassRegistry());
}

NoiseSpecializer::~NoiseSpecializer()
{
}

bool
NoiseSpecializer::runOnFunction(Function &F)
{
  mModule   = F.getParent();
  mContext  = &F.getContext();

  const bool success = runSpecializer(&F);

  if (!success)
  {
    errs() << "ERROR: Specialized dispatching failed!\n";
  }

  // If not successful, nothing changed.
  return success;
}

void
NoiseSpecializer::getAnalysisUsage(AnalysisUsage &AU) const
{
}


bool
NoiseSpecializer::runSpecializer(Function* noiseFn)
{
  assert (noiseFn);

  //-------------------------------------------------------------------------//
  // Get the expected name of the specialize function.
  std::stringstream sstr;
  sstr << "__noise_specialize_" << mVariable;
  const std::string& specializeFnName = sstr.str();

  //-------------------------------------------------------------------------//
  // Find the Noise specialize call for this variable and the corresponding
  // argument where it is given to the noise function.
  Module* module = noiseFn->getParent();
  Function* specializeFn = module->getFunction(specializeFnName);
  assert (specializeFn->getNumUses() == 1);
  CallInst* specializeCall = cast<CallInst>(*specializeFn->use_begin());

  assert (specializeCall->getType()->isIntegerTy() &&
          "specialized dispatch currently only implemented for integer values");
  IntegerType* variableType = cast<IntegerType>(specializeCall->getType());

  assert (specializeCall->getNumUses() == 1);
  CallInst* noiseFnCall = cast<CallInst>(*specializeCall->use_begin());

  Argument* specializeCallArg = 0;
  Function::arg_iterator A = noiseFn->arg_begin();
  for (CallInst::op_iterator OP=noiseFnCall->op_begin(),
       OPE=noiseFnCall->op_end(); OP!=OPE; ++OP, ++A)
  {
      if (*OP != specializeCall) continue;
      specializeCallArg = A;
      break;
  }
  assert (specializeCallArg);

  //-------------------------------------------------------------------------//
  // Create new function for switch statement.
  const unsigned numVariants = mValues->size();

  Function* switchFn = Function::Create(noiseFn->getFunctionType(),
                                        Function::ExternalLinkage,
                                        "switch_fn",
                                        noiseFn->getParent());

  BasicBlock* entryBB = BasicBlock::Create(*mContext, "noiseSpecializeBegin", switchFn);

  //-------------------------------------------------------------------------//
  // Duplicate code once for each specialization variant and specialize.
  SmallVector<BasicBlock*, 4> entryBlocks;
  SmallVector<BasicBlock*, 4> exitBlocks;
  Argument* mappedCallArg = 0;
  for (unsigned i=0; i<=numVariants; ++i)
  {
      ValueToValueMapTy valueMap;
      Function::arg_iterator destI = switchFn->arg_begin();
      for (Function::const_arg_iterator I = noiseFn->arg_begin(),
          E = noiseFn->arg_end(); I != E; ++I)
      {
          if (valueMap.count(I) == 0)          // Is this argument preserved?
          {
              destI->setName(I->getName()); // Copy the name over...
              valueMap[I] = destI++;           // Add mapping to ValueMap
          }
      }
      SmallVector<ReturnInst*, 2>  returns;
      ClonedCodeInfo               clonedFInfo;
      const char*                  nameSuffix = ".";
      CloneFunctionInto(switchFn,
                        noiseFn,
                        valueMap,
                        false,
                        returns,
                        nameSuffix,
                        &clonedFInfo);

      // Store the mapped entry block.
      entryBlocks.push_back(cast<BasicBlock>(valueMap[&noiseFn->getEntryBlock()]));

      // Store the mapped exit block.
      assert (returns.size() == 1);
      exitBlocks.push_back(returns[0]->getParent());

      // Get the mapped noise specialize calls.
      mappedCallArg = cast<Argument>(valueMap[specializeCallArg]);

      // If this is the last iteration, skip the specialization (default case).
      // Only store the mapped call argument.
      if (i == numVariants) continue;

      // Replace uses of specializeCallArg in each variant by the corresponding value.
      ConstantInt* onVal = ConstantInt::get(variableType,
                                            (*mValues)[i],
                                            true);
      mappedCallArg->replaceAllUsesWith(onVal);
  }

  //BasicBlock* exitBB = BasicBlock::Create(*mContext, "noiseSpecializeEnd", switchFn);

  //-------------------------------------------------------------------------//
  // Create switch statement.
  SwitchInst* switchInst = SwitchInst::Create(mappedCallArg,
                                              entryBlocks[numVariants],
                                              numVariants+1,
                                              entryBB);

  for (unsigned i=0; i<numVariants; ++i)
  {
      ConstantInt* onVal = ConstantInt::get(variableType,
                                            (*mValues)[i],
                                            true);
      BasicBlock* destBB = entryBlocks[i];
      switchInst->addCase(onVal, destBB);
  }

//  //-------------------------------------------------------------------------//
//  // Create branches from return blocks to exitBB.
//  for (unsigned i=0; i<numVariants; ++i)
//  {
//      BasicBlock* srcBB = exitBlocks[i];
//      assert (isa<ReturnInst>(srcBB->getTerminator()));
//      assert (!(cast<ReturnInst>(srcBB->getTerminator()))->getReturnValue());
//      srcBB->getTerminator()->eraseFromParent();
//      BranchInst::Create(exitBB, srcBB);
//  }

  //-------------------------------------------------------------------------//
  // Replace body of old function with new function.
  noiseFn->deleteBody();
  ValueToValueMapTy valueMap;
  Function::arg_iterator destI = noiseFn->arg_begin();
  for (Function::const_arg_iterator I = switchFn->arg_begin(),
       E = switchFn->arg_end(); I != E; ++I)
  {
      if (valueMap.count(I) == 0)          // Is this argument preserved?
      {
          destI->setName(I->getName()); // Copy the name over...
          valueMap[I] = destI++;           // Add mapping to ValueMap
      }
  }

  SmallVector<ReturnInst*, 2>  returns;
  ClonedCodeInfo               clonedFInfo;
  const char*                  nameSuffix = ".";
  CloneFunctionInto(noiseFn,
                    switchFn,
                    valueMap,
                    false,
                    returns,
                    nameSuffix,
                    &clonedFInfo);

  switchFn->eraseFromParent();

  //-------------------------------------------------------------------------//
  // Replace dummy call by the original value again.
  Value* specializedVal = specializeCall->getOperand(0);
  specializeCall->replaceAllUsesWith(specializedVal);
  specializeCall->eraseFromParent();

  return true;
}



char NoiseSpecializer::ID = 0;
} // namespace llvm

INITIALIZE_PASS_BEGIN(NoiseSpecializer, "noise-specialized-dispatch",
                      "Specialized dispatching for noise functions", false, false)
INITIALIZE_PASS_END(NoiseSpecializer, "noise-specialized-dispatch",
                    "Specialized dispatching for noise functions", false, false)
