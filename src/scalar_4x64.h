/***********************************************************************
 * Copyright (c) 2013, 2014 Pieter Wuille                              *
 * Distributed under the MIT software license, see the accompanying    *
 * file COPYING or https://www.opensource.org/licenses/mit-license.php.*
 *                                                                      *
 * Extracted from bitcoin-core/secp256k1 for formal verification with   *
 * Rocq / Verifiable C.                                                 *
 *                                                                      *
 * Scope: secp256k1_scalar_mul_512 only — the schoolbook 4-limb         *
 * multiply that produces an 8-limb 512-bit result.                     *
 * No __int128, no inline assembly, no modular reduction.               *
 ***********************************************************************/

#ifndef SECP256K1_SCALAR_4X64_H
#define SECP256K1_SCALAR_4X64_H

#include <stdint.h>

/** A scalar modulo the group order of the secp256k1 curve. */
typedef struct {
    uint64_t d[4];
} secp256k1_scalar;

/**
 * Compute the full 512-bit product of two 256-bit scalars.
 *
 *   l8[0..7]  =  a  *  b        (little-endian 64-bit limbs)
 *
 * This is the verification target.
 */
void secp256k1_scalar_mul_512(uint64_t *l8,
                              const secp256k1_scalar *a,
                              const secp256k1_scalar *b);

#endif /* SECP256K1_SCALAR_4X64_H */
