/* Unit tests for secp256k1_scalar_mul_512. */

#include <stdio.h>
#include <string.h>
#include "scalar_4x64.h" /* found via -Isrc */

static int tests_run    = 0;
static int tests_passed = 0;

static void print_512(const char *label, const uint64_t *v) {
    printf("  %s = 0x", label);
    for (int i = 7; i >= 0; i--)
        printf("%016llx", (unsigned long long)v[i]);
    printf("\n");
}

static int eq_512(const uint64_t *a, const uint64_t *b) {
    return memcmp(a, b, 8 * sizeof(uint64_t)) == 0;
}

static void test_mul512(const char *name,
                        const secp256k1_scalar *a,
                        const secp256k1_scalar *b,
                        const uint64_t expected[8]) {
    uint64_t result[8];
    tests_run++;
    secp256k1_scalar_mul_512(result, a, b);
    if (eq_512(result, expected)) {
        printf("[PASS] %s\n", name);
        tests_passed++;
    } else {
        printf("[FAIL] %s\n", name);
        print_512("expected", expected);
        print_512("got     ", result);
    }
}

static void test_mul_one_times_one(void) {
    secp256k1_scalar a = {{ 1, 0, 0, 0 }};
    secp256k1_scalar b = {{ 1, 0, 0, 0 }};
    uint64_t expected[8] = { 1, 0, 0, 0, 0, 0, 0, 0 };
    test_mul512("1 * 1", &a, &b, expected);
}

static void test_mul_zero(void) {
    secp256k1_scalar a = {{ 0, 0, 0, 0 }};
    secp256k1_scalar b = {{ 0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL,
                            0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL }};
    uint64_t expected[8] = { 0, 0, 0, 0, 0, 0, 0, 0 };
    test_mul512("0 * max256", &a, &b, expected);
}

static void test_mul_small(void) {
    secp256k1_scalar a = {{ 3, 0, 0, 0 }};
    secp256k1_scalar b = {{ 7, 0, 0, 0 }};
    uint64_t expected[8] = { 21, 0, 0, 0, 0, 0, 0, 0 };
    test_mul512("3 * 7", &a, &b, expected);
}

static void test_mul_single_limb_overflow(void) {
    /* (2^64 - 1)^2 = 2^128 - 2^65 + 1 */
    secp256k1_scalar a = {{ 0xFFFFFFFFFFFFFFFFULL, 0, 0, 0 }};
    secp256k1_scalar b = {{ 0xFFFFFFFFFFFFFFFFULL, 0, 0, 0 }};
    uint64_t expected[8] = { 0x0000000000000001ULL,
                             0xFFFFFFFFFFFFFFFEULL,
                             0, 0, 0, 0, 0, 0 };
    test_mul512("(2^64-1)^2", &a, &b, expected);
}

static void test_mul_max256(void) {
    /* (2^256 - 1)^2 = 2^512 - 2^257 + 1 */
    secp256k1_scalar a = {{ 0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL,
                            0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL }};
    secp256k1_scalar b = {{ 0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL,
                            0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL }};
    uint64_t expected[8] = {
        0x0000000000000001ULL, 0x0000000000000000ULL,
        0x0000000000000000ULL, 0x0000000000000000ULL,
        0xFFFFFFFFFFFFFFFEULL, 0xFFFFFFFFFFFFFFFFULL,
        0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL,
    };
    test_mul512("(2^256-1)^2", &a, &b, expected);
}

static void test_mul_power_of_two(void) {
    /* 2^128 * 2^128 = 2^256 */
    secp256k1_scalar a = {{ 0, 0, 1, 0 }};
    secp256k1_scalar b = {{ 0, 0, 1, 0 }};
    uint64_t expected[8] = { 0, 0, 0, 0, 1, 0, 0, 0 };
    test_mul512("2^128 * 2^128", &a, &b, expected);
}

static void test_mul_mixed(void) {
    /* (2^192 + 1)(2^64 + 1) = 2^256 + 2^192 + 2^64 + 1 */
    secp256k1_scalar a = {{ 1, 0, 0, 1 }};
    secp256k1_scalar b = {{ 1, 1, 0, 0 }};
    uint64_t expected[8] = { 1, 1, 0, 1, 1, 0, 0, 0 };
    test_mul512("(2^192+1) * (2^64+1)", &a, &b, expected);
}

static void test_mul_secp256k1_order(void) {
    /* n * 1 = n */
    secp256k1_scalar a = {{ 0xBFD25E8CD0364141ULL, 0xBAAEDCE6AF48A03BULL,
                            0xFFFFFFFFFFFFFFFEULL, 0xFFFFFFFFFFFFFFFFULL }};
    secp256k1_scalar b = {{ 1, 0, 0, 0 }};
    uint64_t expected[8] = {
        0xBFD25E8CD0364141ULL, 0xBAAEDCE6AF48A03BULL,
        0xFFFFFFFFFFFFFFFEULL, 0xFFFFFFFFFFFFFFFFULL,
        0, 0, 0, 0
    };
    test_mul512("n * 1", &a, &b, expected);
}

static void test_mul_commutativity(void) {
    /* a*b == b*a */
    secp256k1_scalar a = {{ 0x1234567890ABCDEFULL, 0xFEDCBA0987654321ULL,
                            0x0011223344556677ULL, 0x8899AABBCCDDEEFFULL }};
    secp256k1_scalar b = {{ 0xAAAAAAAAAAAAAAAAULL, 0x5555555555555555ULL,
                            0x1111111111111111ULL, 0x2222222222222222ULL }};
    uint64_t r1[8], r2[8];
    tests_run++;
    secp256k1_scalar_mul_512(r1, &a, &b);
    secp256k1_scalar_mul_512(r2, &b, &a);
    if (eq_512(r1, r2)) {
        printf("[PASS] commutativity\n");
        tests_passed++;
    } else {
        printf("[FAIL] commutativity\n");
        print_512("a*b", r1);
        print_512("b*a", r2);
    }
}

int main(void) {
    printf("=== secp256k1_scalar_mul_512 unit tests ===\n\n");

    test_mul_one_times_one();
    test_mul_zero();
    test_mul_small();
    test_mul_single_limb_overflow();
    test_mul_max256();
    test_mul_power_of_two();
    test_mul_mixed();
    test_mul_secp256k1_order();
    test_mul_commutativity();

    printf("\n%d / %d tests passed.\n", tests_passed, tests_run);
    return (tests_passed == tests_run) ? 0 : 1;
}
