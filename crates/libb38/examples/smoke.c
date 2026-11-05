/* smoke.c — the "hand it to a stranger" proof: a plain C79 file
 * linking the shared library. No Rust knowledge needed.
 *
 *   cc smoke.c -L../../target/debug -llibb38 -o smoke && ./smoke
 *
 * The strings are balanced base-38, not decimal — multi-digit strings
 * are never read as decimal (the INANNA trap). "+528" is 7304,
 * "+4pe" is 6740, "+ew" is 564.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "b38.h"

static int failures = 0;

static void i128_print(__int128 v) {
    if (v < 0) {
        putchar('-');
        v = -v;
    }
    char buf[64];
    int n = 0;
    do {
        buf[n++] = (char)('0' + v % 10);
        v /= 10;
    } while (v);
    while (n) putchar(buf[--n]);
}

static void check(const char *a, const char *b, const char *want) {
    char *got = b38_add(a, b);
    if (got == NULL) {
        printf("FAIL b38_add(%s, %s) -> NULL\n", a, b);
        failures++;
        return;
    }
    if (strcmp(got, want) != 0) {
        printf("FAIL b38_add(%s, %s) -> %s, want %s\n", a, b, got, want);
        failures++;
    }
    b38_free(got);
}

static void check_sub(const char *a, const char *b, const char *want) {
    char *got = b38_sub(a, b);
    if (got == NULL) {
        printf("FAIL b38_sub(%s, %s) -> NULL\n", a, b);
        failures++;
        return;
    }
    if (strcmp(got, want) != 0) {
        printf("FAIL b38_sub(%s, %s) -> %s, want %s\n", a, b, got, want);
        failures++;
    }
    b38_free(got);
}

static void check_mul(const char *a, const char *b, const char *want) {
    char *got = b38_mul(a, b);
    if (got == NULL) {
        printf("FAIL b38_mul(%s, %s) -> NULL\n", a, b);
        failures++;
        return;
    }
    if (strcmp(got, want) != 0) {
        printf("FAIL b38_mul(%s, %s) -> %s, want %s\n", a, b, got, want);
        failures++;
    }
    b38_free(got);
}

static void check_neg(const char *a, const char *want) {
    char *got = b38_neg(a);
    if (got == NULL) {
        printf("FAIL b38_neg(%s) -> NULL\n", a);
        failures++;
        return;
    }
    if (strcmp(got, want) != 0) {
        printf("FAIL b38_neg(%s) -> %s, want %s\n", a, got, want);
        failures++;
    }
    b38_free(got);
}

static void check_div_rem(const char *a, const char *b,
                          const char *want_q, const char *want_r) {
    char *q = NULL, *r = NULL;
    int rc = b38_div_rem(a, b, &q, &r);
    if (rc != 0) {
        printf("FAIL b38_div_rem(%s, %s) -> status %d\n", a, b, rc);
        failures++;
        return;
    }
    if (strcmp(q, want_q) != 0 || strcmp(r, want_r) != 0) {
        printf("FAIL b38_div_rem(%s, %s) -> q=%s r=%s, want q=%s r=%s\n",
               a, b, q, r, want_q, want_r);
        failures++;
    }
    b38_free(q);
    b38_free(r);
}

static void check_cmp(const char *a, const char *b, int want) {
    int got = b38_cmp(a, b);
    if (got != want) {
        printf("FAIL b38_cmp(%s, %s) -> %d, want %d\n", a, b, got, want);
        failures++;
    }
}

static void check_to_i128(const char *a, __int128 want) {
    __int128 got = 0;
    int rc = b38_to_i128(a, &got);
    if (rc != 0) {
        printf("FAIL b38_to_i128(%s) -> status %d\n", a, rc);
        failures++;
        return;
    }
    if (got != want) {
        printf("FAIL b38_to_i128(%s) -> ", a);
        i128_print(got);
        printf(", want ");
        i128_print(want);
        putchar('\n');
        failures++;
    }
}

static void check_from_i128(__int128 v, const char *want) {
    char *got = NULL;
    int rc = b38_from_i128(v, &got);
    if (rc != 0) {
        printf("FAIL b38_from_i128(...) -> status %d\n", rc);
        failures++;
        return;
    }
    if (got == NULL || strcmp(got, want) != 0) {
        printf("FAIL b38_from_i128(...) -> %s, want %s\n", got, want);
        failures++;
    }
    b38_free(got);
}

/* ── the fraction doors (v3) ────────────────────────────────────── */

static void check_ratio2(const char *a, const char *b, const char *want,
                         char *(*fn)(const char *, const char *),
                         const char *name) {
    char *got = fn(a, b);
    if (got == NULL) {
        printf("FAIL %s(%s, %s) -> NULL\n", name, a, b);
        failures++;
        return;
    }
    if (strcmp(got, want) != 0) {
        printf("FAIL %s(%s, %s) -> %s, want %s\n", name, a, b, got, want);
        failures++;
    }
    b38_free(got);
}

static void check_ratio(const char *a, const char *want,
                        char *(*fn)(const char *),
                        const char *name) {
    char *got = fn(a);
    if (got == NULL) {
        printf("FAIL %s(%s) -> NULL\n", name, a);
        failures++;
        return;
    }
    if (strcmp(got, want) != 0) {
        printf("FAIL %s(%s) -> %s, want %s\n", name, a, got, want);
        failures++;
    }
    b38_free(got);
}

static void check_ratio_cmp(const char *a, const char *b, int want) {
    int got = b38_ratio_cmp(a, b);
    if (got != want) {
        printf("FAIL b38_ratio_cmp(%s, %s) -> %d, want %d\n", a, b, got, want);
        failures++;
    }
}

int main(void) {
    printf("libb38 version %u\n", b38_version());

    /* add */
    check("2", "3", "+5");
    check("0", "0", "0");
    check("+1", "-1", "0");
    check("-3", "-4", "-7");
    check("f", "g", "+v");
    check("1z", "1", "+1_");
    /* the Hubble receipt, scaled by 100: decimal 7304 = "+528" (5*38^2+2*38+8),
       decimal 6740 = "+4pe", residual 564 = "+ew"; 564/100 = 141/25 = 5.64 */
    check("+528", "-4pe", "+ew");

    /* sub — the reflection law, as a door */
    check_sub("5", "3", "+2");
    check_sub("+1", "-1", "+2");
    check_sub("+528", "+4pe", "+ew"); /* 7304 - 6740 = 564 */
    check_sub("ew", "ew", "0");
    check_sub("-3", "4", "-7");

    /* mul — the signed grid */
    check_mul("f", "g", "+6c");       /* 15 * 16 = 240 */
    check_mul("1z", "1", "+1z");      /* 73 * 1 = 73 */
    check_mul("-7", "2", "-e");       /* -14 */
    check_mul("0", "f", "0");         /* the Void binds nothing */
    check_mul("2o", "2o", "+6z6");    /* 100 * 100 = 10000 */
    check_mul("+10p4451iy8_~i", "+10p4451iy8_~i",
              "+11coup_jar_ds8z4zwsn~l2ak"); /* 2^63 * 2^63 = 2^126 */

    /* neg — the mirror */
    check_neg("+528", "-528");
    check_neg("-ew", "+ew");
    check_neg("0", "0");

    /* div_rem — the shore road, Euclidean */
    check_div_rem("-7", "2", "-4", "+1");   /* -7 / 2 = -4 r 1 */
    check_div_rem("-7", "-2", "+4", "+1");
    check_div_rem("1", "4a", "0", "+1");    /* 1 / 38 = 0 r 1 */
    check_div_rem("+528", "+4pe", "+1", "+ew"); /* 7304 / 6740 = 1 r 564 */

    /* cmp — order as exact integers, like strcmp */
    check_cmp("+528", "+4pe", 1);
    check_cmp("+4pe", "+528", -1);
    check_cmp("7", "7", 0);
    check_cmp("0", "0", 0);
    check_cmp("f", "g", -1);

    /* to_i128 — the honest shore door */
    check_to_i128("+528", 7304);
    check_to_i128("-7", -7);
    check_to_i128("0", 0);
    check_to_i128("1z", 73);
    check_to_i128("-1k", -58);

    /* from_i128 — the value never refuses */
    check_from_i128(7304, "+528");
    check_from_i128(-58, "-1k");
    check_from_i128(0, "0");
    check_from_i128(240, "+6c");

    /* the extremes, round-tripped through the lane's own doors */
    {
        const __int128 MAX = (((__int128)0x7FFFFFFFFFFFFFFFLL << 64)
                              | 0xFFFFFFFFFFFFFFFFULL);
        const __int128 MIN = -MAX - 1;
        char *s = NULL;
        __int128 back = 0;
        if (b38_from_i128(MAX, &s) != 0 || s == NULL) {
            printf("FAIL b38_from_i128(i128::MAX)\n");
            failures++;
        } else {
            if (b38_to_i128(s, &back) != 0 || back != MAX) {
                printf("FAIL i128::MAX round trip (got ");
                i128_print(back);
                printf(")\n");
                failures++;
            }
            b38_free(s);
        }
        s = NULL;
        back = 0;
        if (b38_from_i128(MIN, &s) != 0 || s == NULL) {
            printf("FAIL b38_from_i128(i128::MIN)\n");
            failures++;
        } else {
            if (b38_to_i128(s, &back) != 0 || back != MIN) {
                printf("FAIL i128::MIN round trip (got ");
                i128_print(back);
                printf(")\n");
                failures++;
            }
            b38_free(s);
        }
    }

    /* refusals — loud, never wrapped */
    if (b38_add("ZZZ", "1") != NULL) {
        printf("FAIL b38_add bad input must refuse (NULL)\n");
        failures++;
    }
    if (b38_add("", "1") != NULL) {
        printf("FAIL b38_add empty string must refuse (NULL)\n");
        failures++;
    }
    if (b38_mul("+21c88a2~uhz__", "+21c88a2~uhz__") != NULL) {
        /* 2^64 * 2^64 = 2^128, one past the i128 shore */
        printf("FAIL b38_mul beyond-shore product must refuse (NULL)\n");
        failures++;
    }
    {
        char *q = NULL, *r = NULL;
        if (b38_div_rem("5", "0", &q, &r) != -1 || q != NULL || r != NULL) {
            printf("FAIL b38_div_rem Void divisor must refuse (status -1)\n");
            failures++;
        }
        b38_free(q);
        b38_free(r);
    }
    if (b38_cmp("ZZZ", "1") != B38_CMP_REFUSAL) {
        printf("FAIL b38_cmp bad input must refuse (B38_CMP_REFUSAL)\n");
        failures++;
    }
    {
        __int128 out = 0;
        if (b38_to_i128("zzzzzzzzzzzzzzzzzzzzzzzzz", &out) != -1) {
            /* a 25-place all-19 string sits beyond the shore */
            printf("FAIL b38_to_i128 beyond-shore must refuse (status -1)\n");
            failures++;
        }
        if (b38_to_i128("ZZZ", &out) != -1) {
            printf("FAIL b38_to_i128 bad input must refuse (status -1)\n");
            failures++;
        }
    }

    /* ── the rational doors (v3): the promise lands ─────────────── */
    /* fractions are storage: reduced, den > 0, sign on the numerator */
    check_ratio2("+3/+4", "+1/+2", "+5/+4", b38_ratio_add, "b38_ratio_add");
    check_ratio2("+3/+4", "+1/+2", "+1/+4", b38_ratio_sub, "b38_ratio_sub");
    check_ratio2("1/4", "2/3", "+1/+6", b38_ratio_mul, "b38_ratio_mul");
    check_ratio2("1/2", "1/3", "+3/+2", b38_ratio_div, "b38_ratio_div");
    check_ratio2("-3/4", "+1/8", "-5/+8", b38_ratio_add, "b38_ratio_add");
    check_ratio2("0", "1/7", "+1/+7", b38_ratio_add, "b38_ratio_add");
    check_ratio("-3/4", "+3/+4", b38_ratio_neg, "b38_ratio_neg");
    check_ratio("0", "0", b38_ratio_neg, "b38_ratio_neg");
    check_ratio("6/8", "-3/+4", b38_ratio_neg, "b38_ratio_neg");
    check_ratio_cmp("1/2", "1/3", 1);
    check_ratio_cmp("-1/2", "-1/3", -1);
    check_ratio_cmp("+3/+4", "+6/+8", 0);
    check_ratio_cmp("0", "1/z", -1); /* 0 < 1/35 ('z' is the digit 35) */

    /* the fraction door of the Hubble receipt: 141/25 = "+3r/+p" */
    check_ratio2("+3r/+p", "0", "+3r/+p", b38_ratio_add, "b38_ratio_add");
    check_ratio2("+3r/+p", "+3r/+p", "+7g/+p", b38_ratio_add, "b38_ratio_add");
    /* 141+141 = 282 = 7·38 + 16: digits "7g" — the INANNA trap again */

    /* the radix VIEW doors */
    check_ratio("+1/+3", "0.(cp)", b38_ratio_to_radix, "b38_ratio_to_radix");
    check_ratio("+1/+10", "0.1", b38_ratio_to_radix, "b38_ratio_to_radix");
    /* "10" is the balanced string for thirty-eight */
    check_ratio("+3/+4", "0.sj", b38_ratio_to_radix, "b38_ratio_to_radix");
    check_ratio("+1/+7", "0.(5gawlr)", b38_ratio_to_radix, "b38_ratio_to_radix");
    check_ratio("-1/2", "-1.j", b38_ratio_to_radix, "b38_ratio_to_radix");
    check_ratio("+2/+1", "+2", b38_ratio_to_radix, "b38_ratio_to_radix");
    check_ratio("0", "0", b38_ratio_to_radix, "b38_ratio_to_radix");
    check_ratio("+3r/+p",
                "+5.(oc631jsxgrdpvy_i94la)", b38_ratio_to_radix, "b38_ratio_to_radix");
    check_ratio("0.(cp)", "+1/+3", b38_ratio_from_radix, "b38_ratio_from_radix");
    check_ratio("0.1", "+1/+10", b38_ratio_from_radix, "b38_ratio_from_radix");
    check_ratio("0.sj", "+3/+4", b38_ratio_from_radix, "b38_ratio_from_radix");
    check_ratio("-1.j", "-1/+2", b38_ratio_from_radix, "b38_ratio_from_radix");
    check_ratio("+5.(oc631jsxgrdpvy_i94la)", "+3r/+p",
                b38_ratio_from_radix, "b38_ratio_from_radix");

    /* fraction refusals — loud, never a wrapped value */
    if (b38_ratio_div("1", "0") != NULL) {
        printf("FAIL b38_ratio_div Void divisor must refuse (NULL)\n");
        failures++;
    }
    if (b38_ratio_add("1/0", "1") != NULL) {
        printf("FAIL b38_ratio_add Void denominator must refuse (NULL)\n");
        failures++;
    }
    if (b38_ratio_add("1/2/3", "1") != NULL) {
        printf("FAIL b38_ratio_add two slashes must refuse (NULL)\n");
        failures++;
    }
    if (b38_ratio_mul("+21c88a2~uhz__/1", "+21c88a2~uhz__/1") != NULL) {
        /* 2^64/1 * 2^64/1 = 2^128, one past the i128 shore */
        printf("FAIL b38_ratio_mul beyond-shore product must refuse (NULL)\n");
        failures++;
    }
    if (b38_ratio_cmp("ZZZ", "1") != B38_CMP_REFUSAL) {
        printf("FAIL b38_ratio_cmp bad input must refuse (B38_CMP_REFUSAL)\n");
        failures++;
    }
    if (b38_ratio_cmp("1", "1/0") != B38_CMP_REFUSAL) {
        printf("FAIL b38_ratio_cmp Void denominator must refuse (B38_CMP_REFUSAL)\n");
        failures++;
    }
    /* radix refusals: the horizon, the malformed, the forever-lies */
    if (b38_ratio_to_radix("1/7") == NULL) {
        /* the period-6 expansion is well within any horizon — must NOT refuse */
        printf("FAIL b38_ratio_to_radix(1/7) must not refuse\n");
        failures++;
    }
    if (b38_ratio_from_radix("5.") != NULL) {
        printf("FAIL b38_ratio_from_radix bare dot must refuse (NULL)\n");
        failures++;
    }
    if (b38_ratio_from_radix("0.(2)(3)") != NULL) {
        printf("FAIL b38_ratio_from_radix doubled period must refuse (NULL)\n");
        failures++;
    }
    {
        /* 1 followed by 30 zeros after the dot = 38^30, past the shore */
        char big[34] = "0.";
        memset(big + 2, '0', 30);
        big[32] = '1';
        if (b38_ratio_from_radix(big) != NULL) {
            printf("FAIL b38_ratio_from_radix beyond-shore view must refuse (NULL)\n");
            failures++;
        }
    }
    if (b38_ratio_to_radix("1/+11coup_jar_ds8z4zwsn~l2ak") != NULL) {
        /* den = 2^126 rides the shore, but the walk's 38*r product
         * climbs one rung past it and must refuse loudly (NULL) */
        printf("FAIL b38_ratio_to_radix beyond-shore walk must refuse (NULL)\n");
        failures++;
    }

    if (failures == 0) {
        printf("ALL SMOKE CHECKS PASS\n");
        return 0;
    }
    printf("%d FAILURES\n", failures);
    return 1;
}