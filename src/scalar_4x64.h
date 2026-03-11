/***********************************************************************
 * Copyright (c) 2013, 2014 Pieter Wuille                              *
 * Distributed under the MIT software license, see the accompanying    *
 * file COPYING or https://www.opensource.org/licenses/mit-license.php.*
 *                                                                      *
 * Extracted from bitcoin-core/secp256k1 for formal verification with   *
 * Rocq / Verifiable C.                                                 *
 *                                                                      *
 * Scope: secp256k1_scalar_mul:  schoolbook 4-limb multiply followed    *
 * by modular folding reduction mod the secp256k1 group order.          *
 * No __int128, no inline assembly.                                     *
 ***********************************************************************/

#ifndef SECP256K1_SCALAR_4X64_H
#define SECP256K1_SCALAR_4X64_H

#include <stdint.h>

/** A scalar modulo the group order of the secp256k1 curve. */
typedef struct {
    uint64_t d[4];
} secp256k1_scalar;

/**
 * Modular scalar multiplication.
 *
 *   r  =  a * b  (mod N)
 */
void secp256k1_scalar_mul(secp256k1_scalar *r,
                          const secp256k1_scalar *a,
                          const secp256k1_scalar *b);

#endif /* SECP256K1_SCALAR_4X64_H */
