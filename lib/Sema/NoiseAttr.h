//===- NoiseAttr.h -----------------------------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This header defines macros, functions and definitions for the Noise clang
// extension
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_NOISE_NOISEATTR_H
#define LLVM_CLANG_NOISE_NOISEATTR_H

namespace clang {
    class Attr;
    class Sema;
    class AttributeList;
}

namespace clang {

  Attr* CreateNoiseAttr(Sema &S, const AttributeList &attr);

}

#endif // LLVM_CLANG_NOISE_NOISE_H
