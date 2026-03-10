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

/* VERIFY_CHECK is a no-op outside of the original build. */
#define VERIFY_CHECK(cond) do { (void)(cond); } while(0)

/* Inspired by the macros in OpenSSL's crypto/bn/asm/x86_64-gcc.c. */

/** Add a*b to the number defined by (c0,c1,c2). c2 must never overflow. */
#define muladd(a,b) { \
    uint64_t tl, th; \
    { \
        secp256k1_uint128 t; \
        secp256k1_u128_mul(&t, a, b); \
        th = secp256k1_u128_hi_u64(&t);  /* at most 0xFFFFFFFFFFFFFFFE */ \
        tl = secp256k1_u128_to_u64(&t); \
    } \
    c0 += tl;                 /* overflow is handled on the next line */ \
    th += (c0 < tl);          /* at most 0xFFFFFFFFFFFFFFFF */ \
    c1 += th;                 /* overflow is handled on the next line */ \
    c2 += (c1 < th);          /* never overflows by contract (verified in the next line) */ \
    VERIFY_CHECK((c1 >= th) || (c2 != 0)); \
}

/** Add a*b to the number defined by (c0,c1). c1 must never overflow. */
#define muladd_fast(a,b) { \
    uint64_t tl, th; \
    { \
        secp256k1_uint128 t; \
        secp256k1_u128_mul(&t, a, b); \
        th = secp256k1_u128_hi_u64(&t);  /* at most 0xFFFFFFFFFFFFFFFE */ \
        tl = secp256k1_u128_to_u64(&t); \
    } \
    c0 += tl;                 /* overflow is handled on the next line */ \
    th += (c0 < tl);          /* at most 0xFFFFFFFFFFFFFFFF */ \
    c1 += th;                 /* never overflows by contract (verified in the next line) */ \
    VERIFY_CHECK(c1 >= th); \
}

/** Add a to the number defined by (c0,c1,c2). c2 must never overflow. */
#define sumadd(a) { \
    unsigned int over; \
    c0 += (a);                  /* overflow is handled on the next line */ \
    over = (c0 < (a));         \
    c1 += over;                 /* overflow is handled on the next line */ \
    c2 += (c1 < over);          /* never overflows by contract */ \
}

/** Add a to the number defined by (c0,c1). c1 must never overflow, c2 must be zero. */
#define sumadd_fast(a) { \
    c0 += (a);                 /* overflow is handled on the next line */ \
    c1 += (c0 < (a));          /* never overflows by contract (verified the next line) */ \
    VERIFY_CHECK((c1 != 0) | (c0 >= (a))); \
    VERIFY_CHECK(c2 == 0); \
}

/** Extract the lowest 64 bits of (c0,c1,c2) into n, and left shift the number 64 bits. */
#define extract(n) { \
    (n) = c0; \
    c0 = c1; \
    c1 = c2; \
    c2 = 0; \
}

/** Extract the lowest 64 bits of (c0,c1,c2) into n, and left shift the number 64 bits. c2 is required to be zero. */
#define extract_fast(n) { \
    (n) = c0; \
    c0 = c1; \
    c1 = 0; \
    VERIFY_CHECK(c2 == 0); \
}

void secp256k1_scalar_mul_512(uint64_t *l8, const secp256k1_scalar *a, const secp256k1_scalar *b) {
    /* 160 bit accumulator. */
    uint64_t c0 = 0, c1 = 0;
    uint32_t c2 = 0;

    /* l8[0..7] = a[0..3] * b[0..3]. */
    muladd_fast(a->d[0], b->d[0]);
    extract_fast(l8[0]);
    muladd(a->d[0], b->d[1]);
    muladd(a->d[1], b->d[0]);
    extract(l8[1]);
    muladd(a->d[0], b->d[2]);
    muladd(a->d[1], b->d[1]);
    muladd(a->d[2], b->d[0]);
    extract(l8[2]);
    muladd(a->d[0], b->d[3]);
    muladd(a->d[1], b->d[2]);
    muladd(a->d[2], b->d[1]);
    muladd(a->d[3], b->d[0]);
    extract(l8[3]);
    muladd(a->d[1], b->d[3]);
    muladd(a->d[2], b->d[2]);
    muladd(a->d[3], b->d[1]);
    extract(l8[4]);
    muladd(a->d[2], b->d[3]);
    muladd(a->d[3], b->d[2]);
    extract(l8[5]);
    muladd_fast(a->d[3], b->d[3]);
    extract_fast(l8[6]);
    VERIFY_CHECK(c1 == 0);
    l8[7] = c0;
}
