//===--- NoiseAttr.h --------------------------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines functions for the Noise clang extension
//
//===----------------------------------------------------------------------===//
#include "NoiseAttr.h"

// NoiseAttr.cpp:28:47: error: no member named 
//          'err_attribute_wrong_number_arguments' in namespace 'clang::diag'

#include "clang/Sema/SemaInternal.h"

using namespace clang;

static Attr* ProduceErrorMessage(Sema &S, const AttributeList &attr, unsigned diagId, unsigned index) {
  S.Diag(attr.getLoc(), diagId) << "noise" << index;
  attr.setInvalid();
  return 0;
}

Attr* clang::CreateNoiseAttr(Sema &S, const AttributeList &attr) {
  const size_t numArgs = attr.getNumArgs();
  if (numArgs < 1 || numArgs > 2)
    return ProduceErrorMessage(S, attr, diag::err_attribute_wrong_number_arguments, 0);

  const StringLiteral* opt = dyn_cast<StringLiteral>(attr.getArg(0));
  if(!opt)
    return ProduceErrorMessage(S, attr, diag::err_attribute_argument_n_not_int, 1);

  return ::new (S.Context) NoiseAttr(attr.getRange(), S.Context, opt->getString());
}
