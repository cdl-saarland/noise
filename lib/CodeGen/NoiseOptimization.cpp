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
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/PassManagers.h"
#include "llvm/PassRegistry.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/PassRegistry.h"
#include "llvm/Support/raw_ostream.h"

#include "NoiseInliner.h"
#ifdef COMPILE_NOISE_WFV_WRAPPER
#include "NoiseWFVWrapper.h"
#endif
#include "NoiseFusion.h"
#include "NoiseSpecializer.h"

namespace llvm {
namespace noise {

NoiseOptimizationInfo::NoiseOptimizationInfo(NoiseOptimization* Opt)
  : opt(Opt)
  , type(NOISE_OPTIMIZATION_TYPE_LLVMPASS)
{
#define TYPE_ELEM(Type, Name) \
  if (GetPassName() == #Name ) \
    this->type = NOISE_OPTIMIZATION_TYPE_ ## Type;
    NOISEOPTIMIZATION_TYPES(TYPE_ELEM);
#undef TYPE_ELEM
}

StringRef NoiseOptimizationInfo::GetPassName() const
{
  assert( isa<MDString>(opt->getOperand(0)) );
  return cast<MDString>(opt->getOperand(0))->getString();
}

size_t NoiseOptimizationInfo::GetNumArgs() const
{
  return opt->getNumOperands() - 1U;
}

Value* NoiseOptimizationInfo::GetArg(size_t i) const
{
  return opt->getOperand(i + 1U);
}

bool NoiseOptimizationInfo::HasArg(size_t i) const
{
  return GetNumArgs() > i;
}

int NoiseOptimizationInfo::GetArgAsInt(size_t i) const
{
  return cast<ConstantInt>(GetArg(i))->getSExtValue();
}

StringRef NoiseOptimizationInfo::GetArgAsString(size_t i) const
{
  return cast<MDString>(GetArg(i))->getString();
}

NoiseOptimization* NoiseOptimizations::CreateOptimization(LLVMContext &C, ArrayRef<Value*> Values)
{
  return MDNode::get(C, Values);
}

class HookFunctionPassManager : FunctionPassManager
{
public:
  explicit HookFunctionPassManager(NoiseOptimizations &Opt)
    : FunctionPassManager(0)
    , opt(Opt)
  {}

  virtual void add(Pass *pass) {
    opt.Register(pass);
  }

private:
  NoiseOptimizations &opt;
};

static void InitBuiltinPass_OPT(const NoiseOptimizationInfo &Info, NoiseOptimizations &Opt)
{
  assert(Info.GetType() == NOISE_OPTIMIZATION_TYPE_OPT);
  PassManagerBuilder builder;
  // use 2 instead of 3 in order to avoid the creation of passes which
  // are incompatible with our pass setup
  // during (the invocation of the populateModulePassManager method)
  HookFunctionPassManager hook(Opt);
  builder.OptLevel = 2U;
  builder.SizeLevel = 0U;
  builder.DisableUnitAtATime = true;
  builder.populateFunctionPassManager((FunctionPassManager&)hook);
  builder.populateModulePassManager((PassManagerBase&)hook);
}

static void InitBuiltinPass_INLINE(const NoiseOptimizationInfo &Info, NoiseOptimizations &Opt)
{
  assert(Info.GetType() == NOISE_OPTIMIZATION_TYPE_INLINE);
  SmallVector<std::string, 2> fnNames;
  for (unsigned i = 0, e = Info.GetNumArgs(); i < e; ++i) {
    std::string fnName = Info.GetArgAsString(i);
    fnNames.push_back(fnName);
  }
  Opt.Register(createNoiseInlinerPass(fnNames));
}

static void InitBuiltinPass_LOOPUNROLL(const NoiseOptimizationInfo &Info, NoiseOptimizations &Opt)
{
  assert(Info.GetType() == NOISE_OPTIMIZATION_TYPE_LOOPUNROLL);
  const int count = Info.HasArg(0U) ? Info.GetArgAsInt(0U) : -1;

  Opt.Register(createIndVarSimplifyPass());
  Opt.Register(createLoopRotatePass());
  Opt.Register(createLoopUnrollPass(-1, count, false));
}

static void InitBuiltinPass_LOOPFUSION(const NoiseOptimizationInfo &Info, NoiseOptimizations &Opt)
{
  assert(Info.GetType() == NOISE_OPTIMIZATION_TYPE_LOOPFUSION);
  Opt.Register(createLoopSimplifyPass());
  Opt.Register(createNoiseFusionPass());
}

static void InitBuiltinPass_SPECIALIZE(const NoiseOptimizationInfo &Info, NoiseOptimizations &Opt)
{
  // pass = "specialize(x,0,1,13)"
  assert(Info.GetType() == NOISE_OPTIMIZATION_TYPE_SPECIALIZE);
  assert (Info.GetNumArgs() > 1 && "expected at least two arguments for specialized dispatching!");
  const std::string variable = Info.GetArgAsString(0U);
  SmallVector<int, 4> values;
  for (unsigned i=1, e=Info.GetNumArgs(); i<e; ++i) {
    values.push_back(Info.GetArgAsInt(i));
  }
  Opt.Register(createNoiseSpecializerPass(Info.GetArgAsString(0U), values));
}

static void InitBuiltinPass_VECTORIZE(const NoiseOptimizationInfo &Info, NoiseOptimizations &Opt)
{
  assert(Info.GetType() == NOISE_OPTIMIZATION_TYPE_VECTORIZE);
#ifndef COMPILE_NOISE_WFV_WRAPPER
  errs() << "ERROR: No support for WFV is available!\n";
  abort();
#else

  // Add preparatory passes for WFV.
  Opt.Register(createLoopSimplifyPass());
  Opt.Register(createLowerSwitchPass());
  // Add induction variable simplification pass.
  Opt.Register(createIndVarSimplifyPass());
  // Convert to loop-closed SSA form to simplify applicability analysis.
  Opt.Register(createLCSSAPass());

  // WFV may receive argument to specify vectorization width, whether to
  // use AVX and whether to use the divergence analysis.
  // "wfv-vectorize"          -> width 4, do not use avx, use divergence analysis (default)
  // "wfv-vectorize (4,0,1)"  -> width 4, do not use avx, use divergence analysis (default)
  // "wfv-vectorize (8,1,1)"  -> width 8, use avx, use divergence analysis
  // "wfv-vectorize (8,1)"    -> width 8, use avx, use divergence analysis
  // "wfv-vectorize (16,0,0)" -> width 16, do not use avx, do not use divergence analysis
  unsigned vectorizationWidth = Info.HasArg(0U) ? (unsigned)Info.GetArgAsInt(0U) : 4U;
  bool useAVX = Info.HasArg(1U) && Info.GetArgAsInt(1U);
  const bool verbose = false;

  // Add WFV pass wrapper.
  Opt.Register(createNoiseWFVPass(vectorizationWidth, useAVX, verbose));
#endif
}

static void InitBuiltinPass_LLVMPASS(const NoiseOptimizationInfo &Info, NoiseOptimizations &Opt)
{
  assert(Info.GetType() == NOISE_OPTIMIZATION_TYPE_LLVMPASS);
  const PassInfo* info = Opt.GetRegistry().getPassInfo(Info.GetPassName());
  if(!info) {
    errs() << "ERROR: Pass not found: " << Info.GetPassName() << "\n";
    abort();
  }
  Pass* pass = info->createPass();
  if (info->isAnalysis())
    Opt.Register(pass);
  else
  {
    switch(pass->getPassKind()) {
      case PT_BasicBlock:
      case PT_Function:
      case PT_Loop:
      case PT_Region:
        Opt.Register(pass);
        break;
      default:
        errs() << "ERROR: \"" << pass->getPassName() << "\" (" << Info.GetPassName() << ") is not a function pass\n";
        abort();
    }
  }
}

NoiseOptimizations::NoiseOptimizations(PassRegistry &Registry)
  : registry(Registry)
{}

void NoiseOptimizations::Register(NoiseOptimization *Opt) {
  const NoiseOptimizationInfo info(Opt);
  switch (info.GetType()) {
  case NOISE_OPTIMIZATION_TYPE_LLVMPASS:
    InitBuiltinPass_LLVMPASS(info, *this);
    break;
#define TYPE_ELEM(Type, Name) \
  case NOISE_OPTIMIZATION_TYPE_ ## Type: \
    InitBuiltinPass_ ## Type(info, *this); \
    break;
    NOISEOPTIMIZATION_TYPES(TYPE_ELEM)
#undef TYPE_ELEM
  default:
    assert(false);
  }
}

void NoiseOptimizations::Register(Pass *Pass) {
  passes.push_back(Pass);
}

void NoiseOptimizations::RegisterDefaultOpts() {
  Register(createTypeBasedAliasAnalysisPass());
  Register(createBasicAliasAnalysisPass());
  Register(createCFGSimplificationPass());
  Register(createScalarReplAggregatesPass());
  Register(createEarlyCSEPass());
}

void NoiseOptimizations::Populate(PassManagerBase &Manager) {
  for (std::vector<Pass*>::iterator it = passes.begin(), e = passes.end(); it != e; ++it) {
    outs() << "Running pass: " << (*it)->getPassName() << "\n";
    Manager.add(*it);
  }
}

}
}
