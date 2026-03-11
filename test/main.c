/* Unit tests for secp256k1_scalar_mul. */

#include <stdio.h>
#include <string.h>
#include "scalar_4x64.h"

/* Limbs of the secp256k1 order. */
#define SECP256K1_N_0 ((uint64_t)0xBFD25E8CD0364141ULL)
#define SECP256K1_N_1 ((uint64_t)0xBAAEDCE6AF48A03BULL)
#define SECP256K1_N_2 ((uint64_t)0xFFFFFFFFFFFFFFFEULL)
#define SECP256K1_N_3 ((uint64_t)0xFFFFFFFFFFFFFFFFULL)

static int tests_run    = 0;
static int tests_passed = 0;

static int eq_scalar(const secp256k1_scalar *a, const secp256k1_scalar *b) {
    return memcmp(a->d, b->d, 4 * sizeof(uint64_t)) == 0;
}

static void print_scalar(const char *label, const secp256k1_scalar *s) {
    printf("  %s = 0x%016llx%016llx%016llx%016llx\n", label,
           (unsigned long long)s->d[3], (unsigned long long)s->d[2],
           (unsigned long long)s->d[1], (unsigned long long)s->d[0]);
}

static void test_mul(const char *name,
                     const secp256k1_scalar *a,
                     const secp256k1_scalar *b,
                     const secp256k1_scalar *expected) {
    secp256k1_scalar r;
    tests_run++;
    secp256k1_scalar_mul(&r, a, b);
    if (eq_scalar(&r, expected)) {
        printf("[PASS] %s\n", name);
        tests_passed++;
    } else {
        printf("[FAIL] %s\n", name);
        print_scalar("expected", expected);
        print_scalar("got     ", &r);
    }
}

static void test_one_times_one(void) {
    secp256k1_scalar a = {{ 1, 0, 0, 0 }};
    secp256k1_scalar b = {{ 1, 0, 0, 0 }};
    secp256k1_scalar expected = {{ 1, 0, 0, 0 }};
    test_mul("1 * 1", &a, &b, &expected);
}

static void test_zero(void) {
    secp256k1_scalar a = {{ 0, 0, 0, 0 }};
    secp256k1_scalar b = {{ 5, 0, 0, 0 }};
    secp256k1_scalar expected = {{ 0, 0, 0, 0 }};
    test_mul("0 * 5", &a, &b, &expected);
}

static void test_small(void) {
    secp256k1_scalar a = {{ 3, 0, 0, 0 }};
    secp256k1_scalar b = {{ 7, 0, 0, 0 }};
    secp256k1_scalar expected = {{ 21, 0, 0, 0 }};
    test_mul("3 * 7", &a, &b, &expected);
}

static void test_n_times_one(void) {
    /* N * 1 = 0 (mod N) */
    secp256k1_scalar a = {{ SECP256K1_N_0, SECP256K1_N_1,
                            SECP256K1_N_2, SECP256K1_N_3 }};
    secp256k1_scalar b = {{ 1, 0, 0, 0 }};
    secp256k1_scalar expected = {{ 0, 0, 0, 0 }};
    test_mul("N * 1 = 0", &a, &b, &expected);
}

static void test_n_minus_one_squared(void) {
    /* (N-1)^2 = 1 (mod N)  since (N-1) = -1 mod N */
    secp256k1_scalar a = {{ SECP256K1_N_0 - 1, SECP256K1_N_1,
                            SECP256K1_N_2, SECP256K1_N_3 }};
    secp256k1_scalar expected = {{ 1, 0, 0, 0 }};
    test_mul("(N-1)^2 = 1", &a, &a, &expected);
}

static void test_two_times_two(void) {
    secp256k1_scalar a = {{ 2, 0, 0, 0 }};
    secp256k1_scalar expected = {{ 4, 0, 0, 0 }};
    test_mul("2 * 2", &a, &a, &expected);
}

static void test_commutativity(void) {
    secp256k1_scalar a = {{ 0x1234567890ABCDEFULL, 0xFEDCBA0987654321ULL,
                            0x0011223344556677ULL, 0x8899AABBCCDDEEFFULL }};
    secp256k1_scalar b = {{ 0xAAAAAAAAAAAAAAAAULL, 0x5555555555555555ULL,
                            0x1111111111111111ULL, 0x2222222222222222ULL }};
    secp256k1_scalar r1, r2;
    tests_run++;
    secp256k1_scalar_mul(&r1, &a, &b);
    secp256k1_scalar_mul(&r2, &b, &a);
    if (eq_scalar(&r1, &r2)) {
        printf("[PASS] commutativity\n");
        tests_passed++;
    } else {
        printf("[FAIL] commutativity\n");
        print_scalar("a*b", &r1);
        print_scalar("b*a", &r2);
    }
}

static void test_n_minus_one_times_two(void) {
    /* (N-1) * 2 = N-2 (mod N)  since (N-1)*2 = 2N-2 = -2 mod N = N-2 */
    secp256k1_scalar a = {{ SECP256K1_N_0 - 1, SECP256K1_N_1,
                            SECP256K1_N_2, SECP256K1_N_3 }};
    secp256k1_scalar b = {{ 2, 0, 0, 0 }};
    secp256k1_scalar expected = {{ SECP256K1_N_0 - 2, SECP256K1_N_1,
                                  SECP256K1_N_2, SECP256K1_N_3 }};
    test_mul("(N-1)*2 = N-2", &a, &b, &expected);
}

static void test_large_product(void) {
    /* (2^128) * (2^128) mod N
       = 2^256 mod N = C = N_C_0 + N_C_1*2^64 + 1*2^128 */
    secp256k1_scalar a = {{ 0, 0, 1, 0 }};
    secp256k1_scalar expected = {{ (uint64_t)(~SECP256K1_N_0 + 1),
                                  (uint64_t)(~SECP256K1_N_1),
                                  1, 0 }};
    test_mul("2^128 * 2^128 = 2^256 mod N", &a, &a, &expected);
}

int main(void) {
    printf("=== secp256k1_scalar_mul unit tests ===\n\n");

    test_one_times_one();
    test_zero();
    test_small();
    test_two_times_two();
    test_n_times_one();
    test_n_minus_one_squared();
    test_n_minus_one_times_two();
    test_large_product();
    test_commutativity();

    printf("\n%d / %d tests passed.\n", tests_passed, tests_run);
    return (tests_passed == tests_run) ? 0 : 1;
}
