/***********************************************************************
 * Copyright (c) 2013, 2014 Pieter Wuille                              *
 * Distributed under the MIT software license, see the accompanying    *
 * file COPYING or https://www.opensource.org/licenses/mit-license.php.*
 *                                                                      *
 * Extracted from bitcoin-core/secp256k1 for formal verification with   *
 * Rocq / Verifiable C.                                                 *
 *                                                                      *
 * Scope: secp256k1_scalar_mul_512 — the non-assembly branch from       *
 * scalar_4x64_impl.h. No __int128, no inline assembly.                 *
 ***********************************************************************/

#include "scalar_4x64.h"

/* On other systems, emulate 64x64->128 multiplications using 32x32->64 multiplications. */
static inline uint64_t secp256k1_umul128(uint64_t a, uint64_t b, uint64_t *hi) {
    uint64_t ll = (uint64_t)(uint32_t)a * (uint32_t)b;
    uint64_t lh = (uint32_t)a * (b >> 32);
    uint64_t hl = (a >> 32) * (uint32_t)b;
    uint64_t hh = (a >> 32) * (b >> 32);
    uint64_t mid34 = (ll >> 32) + (uint32_t)lh + (uint32_t)hl;
    *hi = hh + (lh >> 32) + (hl >> 32) + (mid34 >> 32);
    return (mid34 << 32) + (uint32_t)ll;
}

static inline void secp256k1_u128_mul(secp256k1_uint128 *r, uint64_t a, uint64_t b) {
   r->lo = secp256k1_umul128(a, b, &r->hi);
}

static inline uint64_t secp256k1_u128_to_u64(const secp256k1_uint128 *a) {
   return a->lo;
}

static inline uint64_t secp256k1_u128_hi_u64(const secp256k1_uint128 *a) {
   return a->hi;
}

/** 192-bit accumulator: (c2 : c1 : c0). */
typedef struct {
    uint64_t c0;
    uint64_t c1;
    uint32_t c2;
} secp256k1_acc;

/** Add a*b to the number defined by (c0,c1,c2). c2 must never overflow. */
static inline void muladd(secp256k1_acc *acc, uint64_t a, uint64_t b) {
    uint64_t tl, th;
    secp256k1_uint128 t;
    secp256k1_u128_mul(&t, a, b);
    th = secp256k1_u128_hi_u64(&t);  /* at most 0xFFFFFFFFFFFFFFFE */
    tl = secp256k1_u128_to_u64(&t);
    acc->c0 += tl;                   /* overflow is handled on the next line */
    th += (acc->c0 < tl);            /* at most 0xFFFFFFFFFFFFFFFF */
    acc->c1 += th;                   /* overflow is handled on the next line */
    acc->c2 += (acc->c1 < th);       /* never overflows by contract */
}

/** Add a*b to the number defined by (c0,c1). c1 must never overflow. */
static inline void muladd_fast(secp256k1_acc *acc, uint64_t a, uint64_t b) {
    uint64_t tl, th;
    secp256k1_uint128 t;
    secp256k1_u128_mul(&t, a, b);
    th = secp256k1_u128_hi_u64(&t);  /* at most 0xFFFFFFFFFFFFFFFE */
    tl = secp256k1_u128_to_u64(&t);
    acc->c0 += tl;                   /* overflow is handled on the next line */
    th += (acc->c0 < tl);            /* at most 0xFFFFFFFFFFFFFFFF */
    acc->c1 += th;                   /* never overflows by contract */
}

/** Add a to the number defined by (c0,c1,c2). c2 must never overflow. */
static inline void sumadd(secp256k1_acc *acc, uint64_t a) {
    unsigned int over;
    acc->c0 += a;                    /* overflow is handled on the next line */
    over = (acc->c0 < a);
    acc->c1 += over;                 /* overflow is handled on the next line */
    acc->c2 += (acc->c1 < over);     /* never overflows by contract */
}

/** Add a to the number defined by (c0,c1). c1 must never overflow, c2 must be zero. */
static inline void sumadd_fast(secp256k1_acc *acc, uint64_t a) {
    acc->c0 += a;                    /* overflow is handled on the next line */
    acc->c1 += (acc->c0 < a);        /* never overflows by contract */
}

/** Extract the lowest 64 bits of (c0,c1,c2) into *n, and left shift the number 64 bits. */
static inline void extract(secp256k1_acc *acc, uint64_t *n) {
    *n = acc->c0;
    acc->c0 = acc->c1;
    acc->c1 = acc->c2;
    acc->c2 = 0;
}

/** Extract the lowest 64 bits of (c0,c1,c2) into *n, and left shift the number 64 bits. c2 is required to be zero. */
static inline void extract_fast(secp256k1_acc *acc, uint64_t *n) {
    *n = acc->c0;
    acc->c0 = acc->c1;
    acc->c1 = 0;
}

void secp256k1_scalar_mul_512(uint64_t *l8, const secp256k1_scalar *a, const secp256k1_scalar *b) {
    /* 160 bit accumulator. */
    secp256k1_acc acc = {0, 0, 0};

    /* l8[0..7] = a[0..3] * b[0..3]. */
    muladd_fast(&acc, a->d[0], b->d[0]);
    extract_fast(&acc, &l8[0]);
    muladd(&acc, a->d[0], b->d[1]);
    muladd(&acc, a->d[1], b->d[0]);
    extract(&acc, &l8[1]);
    muladd(&acc, a->d[0], b->d[2]);
    muladd(&acc, a->d[1], b->d[1]);
    muladd(&acc, a->d[2], b->d[0]);
    extract(&acc, &l8[2]);
    muladd(&acc, a->d[0], b->d[3]);
    muladd(&acc, a->d[1], b->d[2]);
    muladd(&acc, a->d[2], b->d[1]);
    muladd(&acc, a->d[3], b->d[0]);
    extract(&acc, &l8[3]);
    muladd(&acc, a->d[1], b->d[3]);
    muladd(&acc, a->d[2], b->d[2]);
    muladd(&acc, a->d[3], b->d[1]);
    extract(&acc, &l8[4]);
    muladd(&acc, a->d[2], b->d[3]);
    muladd(&acc, a->d[3], b->d[2]);
    extract(&acc, &l8[5]);
    muladd_fast(&acc, a->d[3], b->d[3]);
    extract_fast(&acc, &l8[6]);
    l8[7] = acc.c0;
}
