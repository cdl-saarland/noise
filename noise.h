/**
 * @file   noise.h
 * Copyright (C) 2013 Saarland University
 *
 */
#ifndef _NOISE_H
#define _NOISE_H

// TODO: Our modified clang should set a define, e.g. __CLANG_NOISE_EXT__,
//       that can be queried here to define empty makros for other compilers.
#define RAWNOISE(arg) __attribute__((noise(arg)))
#define NOISE(arg) RAWNOISE("tbaa basicaa scalarrepl simplifycfg early-cse " arg)

#endif /* _NOISE_H */

