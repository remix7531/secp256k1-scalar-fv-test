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

/* Limbs of the secp256k1 order. */
#define SECP256K1_N_0 ((uint64_t)0xBFD25E8CD0364141ULL)
#define SECP256K1_N_1 ((uint64_t)0xBAAEDCE6AF48A03BULL)
#define SECP256K1_N_2 ((uint64_t)0xFFFFFFFFFFFFFFFEULL)
#define SECP256K1_N_3 ((uint64_t)0xFFFFFFFFFFFFFFFFULL)

/* Limbs of 2^256 minus the secp256k1 order. */
#define SECP256K1_N_C_0 (~SECP256K1_N_0 + 1)
#define SECP256K1_N_C_1 (~SECP256K1_N_1)
#define SECP256K1_N_C_2 (1)

/* Limbs of half the secp256k1 order. */
#define SECP256K1_N_H_0 ((uint64_t)0xDFE92F46681B20A0ULL)
#define SECP256K1_N_H_1 ((uint64_t)0x5D576E7357A4501DULL)
#define SECP256K1_N_H_2 ((uint64_t)0xFFFFFFFFFFFFFFFFULL)
#define SECP256K1_N_H_3 ((uint64_t)0x7FFFFFFFFFFFFFFFULL)

typedef struct {
    uint64_t lo;
    uint64_t hi;
} secp256k1_uint128;

/* Internal 256-bit limb container (not necessarily reduced mod N). */
typedef secp256k1_scalar secp256k1_uint256;

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
    uint64_t c2;
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

/** Set r to a. */
static inline void secp256k1_u128_from_u64(secp256k1_uint128 *r, uint64_t a) {
    r->lo = a;
    r->hi = 0;
}

/** Add a to r (128-bit). */
static inline void secp256k1_u128_accum_u64(secp256k1_uint128 *r, uint64_t a) {
    r->lo += a;
    r->hi += (r->lo < a);
}

/** Add a*b to r (128-bit). */
static inline void secp256k1_u128_accum_mul(secp256k1_uint128 *r, uint64_t a, uint64_t b) {
    secp256k1_uint128 t;
    secp256k1_u128_mul(&t, a, b);
    r->lo += t.lo;
    r->hi += t.hi + (r->lo < t.lo);
}

/** Right-shift r by 64 bits (n must be 64). */
static inline void secp256k1_u128_rshift(secp256k1_uint128 *r, unsigned int n) {
    (void)n;
    r->lo = r->hi;
    r->hi = 0;
}

/** Return 1 if a >= N, 0 otherwise. */
static inline int secp256k1_scalar_check_overflow(const secp256k1_uint256 *a) {
    int yes = 0;
    int no = 0;
    no |= (a->d[3] < SECP256K1_N_3); /* No need for a > check. */
    no |= (a->d[2] < SECP256K1_N_2);
    yes |= (a->d[2] > SECP256K1_N_2) & ~no;
    no |= (a->d[1] < SECP256K1_N_1);
    yes |= (a->d[1] > SECP256K1_N_1) & ~no;
    yes |= (a->d[0] >= SECP256K1_N_0) & ~no;
    return yes;
}

/** Conditionally subtract N if overflow is nonzero. Returns overflow. */
static inline int secp256k1_scalar_reduce(secp256k1_uint256 *r, unsigned int overflow) {
    secp256k1_uint128 t;

    secp256k1_u128_from_u64(&t, r->d[0]);
    secp256k1_u128_accum_u64(&t, (uint64_t)overflow * SECP256K1_N_C_0);
    r->d[0] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift(&t, 64);
    secp256k1_u128_accum_u64(&t, r->d[1]);
    secp256k1_u128_accum_u64(&t, (uint64_t)overflow * SECP256K1_N_C_1);
    r->d[1] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift(&t, 64);
    secp256k1_u128_accum_u64(&t, r->d[2]);
    secp256k1_u128_accum_u64(&t, (uint64_t)overflow * SECP256K1_N_C_2);
    r->d[2] = secp256k1_u128_to_u64(&t); secp256k1_u128_rshift(&t, 64);
    secp256k1_u128_accum_u64(&t, r->d[3]);
    r->d[3] = secp256k1_u128_to_u64(&t);

    return overflow;
}

static void secp256k1_scalar_reduce_512(secp256k1_uint256 *r, const uint64_t *l) {
    secp256k1_uint128 c128;
    uint64_t n0 = l[4], n1 = l[5], n2 = l[6], n3 = l[7];
    uint64_t m0, m1, m2, m3, m4, m5;
    uint32_t m6;
    uint64_t p0, p1, p2, p3;
    uint32_t p4;
    uint64_t c;

    /* Reduce 512 bits into 385. */
    /* m[0..6] = l[0..3] + n[0..3] * SECP256K1_N_C. */
    {
        secp256k1_acc acc = {l[0], 0, 0};
        muladd_fast(&acc, n0, SECP256K1_N_C_0);
        extract_fast(&acc, &m0);
        sumadd_fast(&acc, l[1]);
        muladd(&acc, n1, SECP256K1_N_C_0);
        muladd(&acc, n0, SECP256K1_N_C_1);
        extract(&acc, &m1);
        sumadd(&acc, l[2]);
        muladd(&acc, n2, SECP256K1_N_C_0);
        muladd(&acc, n1, SECP256K1_N_C_1);
        sumadd(&acc, n0);
        extract(&acc, &m2);
        sumadd(&acc, l[3]);
        muladd(&acc, n3, SECP256K1_N_C_0);
        muladd(&acc, n2, SECP256K1_N_C_1);
        sumadd(&acc, n1);
        extract(&acc, &m3);
        muladd(&acc, n3, SECP256K1_N_C_1);
        sumadd(&acc, n2);
        extract(&acc, &m4);
        sumadd_fast(&acc, n3);
        extract_fast(&acc, &m5);
        m6 = (uint32_t)acc.c0;
    }

    /* Reduce 385 bits into 258. */
    /* p[0..4] = m[0..3] + m[4..6] * SECP256K1_N_C. */
    {
        secp256k1_acc acc = {m0, 0, 0};
        muladd_fast(&acc, m4, SECP256K1_N_C_0);
        extract_fast(&acc, &p0);
        sumadd_fast(&acc, m1);
        muladd(&acc, m5, SECP256K1_N_C_0);
        muladd(&acc, m4, SECP256K1_N_C_1);
        extract(&acc, &p1);
        sumadd(&acc, m2);
        muladd(&acc, m6, SECP256K1_N_C_0);
        muladd(&acc, m5, SECP256K1_N_C_1);
        sumadd(&acc, m4);
        extract(&acc, &p2);
        sumadd_fast(&acc, m3);
        muladd_fast(&acc, m6, SECP256K1_N_C_1);
        sumadd_fast(&acc, m5);
        extract_fast(&acc, &p3);
        p4 = (uint32_t)(acc.c0 + m6);
    }

    /* Reduce 258 bits into 256. */
    /* r[0..3] = p[0..3] + p[4] * SECP256K1_N_C. */
    secp256k1_u128_from_u64(&c128, p0);
    secp256k1_u128_accum_mul(&c128, SECP256K1_N_C_0, p4);
    r->d[0] = secp256k1_u128_to_u64(&c128); secp256k1_u128_rshift(&c128, 64);
    secp256k1_u128_accum_u64(&c128, p1);
    secp256k1_u128_accum_mul(&c128, SECP256K1_N_C_1, p4);
    r->d[1] = secp256k1_u128_to_u64(&c128); secp256k1_u128_rshift(&c128, 64);
    secp256k1_u128_accum_u64(&c128, p2);
    secp256k1_u128_accum_u64(&c128, p4);
    r->d[2] = secp256k1_u128_to_u64(&c128); secp256k1_u128_rshift(&c128, 64);
    secp256k1_u128_accum_u64(&c128, p3);
    r->d[3] = secp256k1_u128_to_u64(&c128);
    c = secp256k1_u128_hi_u64(&c128);

    /* Final reduction of r. */
    secp256k1_scalar_reduce(r, (unsigned int)(c + secp256k1_scalar_check_overflow(r)));
}

static void secp256k1_scalar_mul_512(uint64_t *l8, const secp256k1_uint256 *a, const secp256k1_uint256 *b) {
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

void secp256k1_scalar_mul(secp256k1_scalar *r, const secp256k1_scalar *a, const secp256k1_scalar *b) {
    uint64_t l[8];
    secp256k1_scalar_mul_512(l, a, b);
    secp256k1_scalar_reduce_512(r, l);
}
