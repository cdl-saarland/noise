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

#include "clang/Frontend/TextDiagnosticPrinter.h"

#include "NoiseInliner.h"
#ifdef COMPILE_NOISE_WFV_WRAPPER
#include "NoiseWFVWrapper.h"
#endif
#include "NoiseFusion.h"
#include "NoiseSpecializer.h"

using namespace clang;

namespace llvm {
namespace noise {

// TODO: move theses messages to tablegen files from clang

#define NOISEDIAG_MSGS(X) \
  X( invalid_opt,           "Invalid noise optimization " ) \
  X( invalid_nested_return, "Marked compound statements must not contain return statements." ) \
  \
  X( specialize_multiple_var_with_same_name, "Specialization of multiple variables of same name (%0) not supported." ) \
  X( specialize_no_use_of_specialized_var, "Cannot find unique use of specialized variable %0." ) \
  X( specialize_depend_on_non_primitive_value, "Cannot specialize variable %0 that depends on non-constant primitive value." ) \
  X( specialize_two_arguments_expected, "At least two arguments required for specialization." ) \
  X( specialize_variable_no_longer_available, "Variable %0 no longer available. Inlined?" ) \
  X( specialize_must_be_integer_value, "Specialization variable %0 must be of integer type." ) \
  X( specialize_must_be_mutable, "Variable %0 could not be specialized since it was not declared as mutable within the current scope." ) \
  \
  X( inline_cannot_find_func, "Function %0 requested for inlining does not exist in module.\\Did you forget to mark the function as external ''C''?" ) \
  \
  X( wfv_not_available, "WFV not available. Recompile noise with WFV support." ) \
  X( wfv_failed, "WFV failed." ) \
  X( wfv_non_simplified_loops, "Vectorization of non-simplified loop not supported." ) \
  X( wfv_multiple_exits, "Vectorization of loop with multiple exits not supported." ) \
  X( wfv_exiting_not_header, "Expected exiting block to be the loop header." ) \
  X( wfv_cannot_place_reduction_call, "Placing of reduction call is impossible for variable %0." ) \
  X( wfv_loop_body_does_not_depend_on_induction, "Loop body seems to be independent of induction variable." ) \
  X( wfv_bad_common_reduction_found, "Bad common reduction operation found. Should be a simple operation (+, *)." ) \
  X( wfv_not_more_reduction_users_outside_loop, "Must not have more than one reduction user outside the loop." )\
  X( wfv_multiple_backedges, "Vectorization of loops with multiple back edges not supported." ) \
  X( wfv_reverse_induction, "Vectorization of loops with reverse induction not supported." ) \
  X( wfv_pointer_induction, "Vectorization of loops with pointer induction variable not supported." ) \
  X( wfv_multiple_inductions, "Vectorization of loops with multiple induction variables not supported." ) \
  X( wfv_non_canonical_induction, "Vectorization of loops without canonical induction variable not supported." ) \
  X( wfv_induction_update_in_header, "Expected induction variable update operation in latch or header block." ) \
  X( wfv_induction_update_no_int_addition, "Vectorization of loop with induction variable update operation that is no integer addition not supported." ) \
  X( wfv_induction_no_simple_increment, "Vectorization of loop with induction variable update operation that is no simple increment not supported." ) \
  \
  X( pass_not_found, "The requested pass %0 could not be found." ) \
  X( pass_not_a_function_pass, "The requested pass %0 is not a function pass." )

#define DIAG_MSG(Type, M) \
static const char *msg_ ## Type = M;
  NOISEDIAG_MSGS(DIAG_MSG)
#undef DIAG_MSG

NoiseDiagnostics::NoiseDiagnostics()
  : diagOpts(new DiagnosticOptions)
  , diag(new DiagnosticsEngine(IntrusiveRefCntPtr<DiagnosticIDs>(new DiagnosticIDs), &*diagOpts,
    new TextDiagnosticPrinter(llvm::errs(), &*diagOpts)))
#define DIAG_ELEM(Type, IsError) \
  , err_ ## Type(diag->getCustomDiagID(IsError ? DiagnosticsEngine::Error : DiagnosticsEngine::Warning, \
                 std::string(msg_ ## Type)))
    NOISEDIAG_TYPES(DIAG_ELEM)
#undef DIAG_ELEM
{}

size_t NoiseDiagnostics::GetNumErrors() const
{
  return diag->getClient()->getNumErrors();
}

DiagnosticBuilder NoiseDiagnostics::Report(unsigned ID)
{
  return diag->Report(ID);
}

void NoiseDiagnostics::TerminateOnError()
{
  if (GetNumErrors() > 0)
    exit(1);
}

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
  Opt.Register(createNoiseInlinerPass(fnNames, Opt.GetDiag()));
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
  if (Info.GetNumArgs() < 2)
  {
    Opt.GetDiag().Report(Opt.GetDiag().err_specialize_two_arguments_expected);
    return;
  }

  const std::string variable = Info.GetArgAsString(0U);
  SmallVector<int, 4> values;
  for (unsigned i=1, e=Info.GetNumArgs(); i<e; ++i) {
    values.push_back(Info.GetArgAsInt(i));
  }
  Opt.Register(createNoiseSpecializerPass(Info.GetArgAsString(0U), values, Opt.GetDiag()));
}

static void InitBuiltinPass_VECTORIZE(const NoiseOptimizationInfo &Info, NoiseOptimizations &Opt)
{
  assert(Info.GetType() == NOISE_OPTIMIZATION_TYPE_VECTORIZE);
#ifndef COMPILE_NOISE_WFV_WRAPPER
  Opt.GetDiag().Report(Opt.GetDiag().err_wfv_not_available);
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
  Opt.Register(createNoiseWFVPass(vectorizationWidth, useAVX, verbose, &Opt.GetDiag()));
#endif
}

static void InitBuiltinPass_LLVMPASS(const NoiseOptimizationInfo &Info, NoiseOptimizations &Opt)
{
  assert(Info.GetType() == NOISE_OPTIMIZATION_TYPE_LLVMPASS);
  const PassInfo* info = Opt.GetRegistry().getPassInfo(Info.GetPassName());
  if(!info) {
    Opt.GetDiag().Report(Opt.GetDiag().err_pass_not_found).AddString(Info.GetPassName());
    return;
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
        Opt.GetDiag().Report(Opt.GetDiag().err_pass_not_a_function_pass).AddString(Info.GetPassName());
        return;
    }
  }
}

NoiseOptimizations::NoiseOptimizations(PassRegistry &Registry, NoiseDiagnostics &Diag)
  : registry(Registry), diag(Diag)
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
