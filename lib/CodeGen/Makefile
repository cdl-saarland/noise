##===- clang/lib/CodeGen/Makefile --------------------------*- Makefile -*-===##
# 
#                     The LLVM Compiler Infrastructure
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
# 
##===----------------------------------------------------------------------===##
#
# This implements the AST -> LLVM code generation library for the 
# C-Language front-end.
#
##===----------------------------------------------------------------------===##

CLANG_LEVEL := ../..
LIBRARYNAME := clangCodeGen

include $(CLANG_LEVEL)/Makefile


ifeq ($(WFV_INSTALL_DIR),)
# Do not set any special flags
else
CPP.Flags += -I$(WFV_INSTALL_DIR)/include -DCOMPILE_NOISE_WFV_WRAPPER
endif
