//===--- NoiseOptimization.h - Noise Specific Optimizations -----*- C++ -*-===//
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

#ifndef CLANG_CODEGEN_NOISEOPTIMIZATION_H
#define CLANG_CODEGEN_NOISEOPTIMIZATION_H

#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"

#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/DiagnosticIDs.h"
#include "clang/Basic/DiagnosticOptions.h"

namespace llvm {

  class LLVMContext;
  class Value;
  class MDNode;
  class PassRegistry;
  class Pass;
  class PassManagerBase;

namespace noise {

#define NOISEDIAG_TYPES(X) \
  X( invalid_opt, true ) \
  X( invalid_nested_return, true ) \
  \
  X( specialize_multiple_var_with_same_name, true ) \
  X( specialize_no_use_of_specialized_var, true ) \
  X( specialize_depend_on_non_primitive_value, true ) \
  X( specialize_two_arguments_expected, true ) \
  X( specialize_variable_no_longer_available, false ) \
  X( specialize_must_be_integer_value, true ) \
  X( specialize_must_be_mutable, true ) \
  \
  X( inline_cannot_find_func, true ) \
  \
  X( wfv_not_available, true ) \
  X( wfv_failed, true ) \
  X( wfv_non_simplified_loops, true ) \
  X( wfv_multiple_exits, true ) \
  X( wfv_exiting_not_header, true ) \
  X( wfv_cannot_place_reduction_call, true) \
  X( wfv_loop_body_does_not_depend_on_induction, true) \
  X( wfv_bad_common_reduction_found, true) \
  X( wfv_not_more_reduction_users_outside_loop, true) \
  X( wfv_multiple_backedges, true) \
  X( wfv_reverse_induction, false) \
  X( wfv_pointer_induction, false) \
  X( wfv_multiple_inductions, false) \
  X( wfv_non_canonical_induction, true) \
  X( wfv_induction_update_in_header, true) \
  X( wfv_induction_update_no_int_addition, true) \
  X( wfv_induction_no_simple_increment, true) \
  \
  X( pass_not_found, true ) \
  X( pass_not_a_function_pass, true )

  // Special noise diagnostics
  class NoiseDiagnostics {
  public:
    NoiseDiagnostics();

    clang::DiagnosticBuilder Report(unsigned ID);
    void TerminateOnError();
    size_t GetNumErrors() const;

  private:
    IntrusiveRefCntPtr<clang::DiagnosticOptions> diagOpts;
    IntrusiveRefCntPtr<clang::DiagnosticsEngine> diag;

  public:
#define DIAG_ELEM(Type, IsError) \
    const unsigned err_ ## Type;
    NOISEDIAG_TYPES(DIAG_ELEM)
#undef DIAG_ELEM
  };

  // Avoid the explicit creation of custom classes
  // which makes it harder to maintain the code
  typedef MDNode NoiseOptimization;

  /*
   Pass description from the parser contains:
   - PassName
   - Arg0
   - Arg1
   - ...
   - ArgN

   -> NumOperands = NumArgs() - 1
   */

#define NOISEOPTIMIZATION_TYPES(X) \
  X( OPT, opt ) \
  X( INLINE, inline ) \
  X( LOOPUNROLL, unroll ) \
  X( LOOPFUSION, loop-fusion ) \
  X( SPECIALIZE, specialize ) \
  X( VECTORIZE, wfv )

  enum NoiseOptimizationType {
#define TYPE_ELEM(Type, Name) \
    NOISE_OPTIMIZATION_TYPE_ ## Type,
    NOISEOPTIMIZATION_TYPES(TYPE_ELEM)
#undef TYPE_ELEM
    NOISE_OPTIMIZATION_TYPE_LLVMPASS
  };

  class NoiseOptimizationInfo {
  public:
    NoiseOptimizationInfo(NoiseOptimization *Opt);

    NoiseOptimizationType GetType() const { return type; }

    StringRef GetPassName() const;
    size_t GetNumArgs() const;
    Value* GetArg(size_t i) const;
    bool HasArg(size_t i) const;

    int GetArgAsInt(size_t i) const;
    StringRef GetArgAsString(size_t i) const;

    Value* operator[](size_t i) const {
        return GetArg(i);
    }

  private:
    NoiseOptimization *opt;
    NoiseOptimizationType type;
  };

  class NoiseOptimizations {
  public:
    NoiseOptimizations(PassRegistry &Registry, NoiseDiagnostics &Diag);

    static NoiseOptimization* CreateOptimization(LLVMContext &C, ArrayRef<Value*> Values);

    void Register(NoiseOptimization *Opt);
    void Register(Pass *Pass);
    void RegisterDefaultOpts();
    void Populate(PassManagerBase &Manager);

    PassRegistry& GetRegistry() { return registry; }
    NoiseDiagnostics& GetDiag() { return diag; }

  private:
    PassRegistry &registry;
    NoiseDiagnostics &diag;
    std::vector<Pass*> passes;
  };

}  // end namespace noise
}  // end namespace llvm

#endif
