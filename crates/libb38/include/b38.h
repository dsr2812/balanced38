/* b38.h — libb38: the key. Balanced base-38 strings in, exact answers out.
 *
 * Two decimal-looking strings are NOT decimal: every digit char is
 * balanced base-38 (0-9, a-z, _ for 36, ~ for 37), MSB-first, with an
 * optional +/- sign. "0" is zero (the Void). No leading zeros.
 *
 *   char *s = b38_add("f", "g");   // returns "+v" (15+16=31)
 *   b38_free(s);
 *
 * Refusal is always loud, never a wrapped value: the string-returning
 * doors hand back NULL, the integer doors hand back a distinct status.
 * The caller owns every returned string and must free it with
 * b38_free.
 *
 * The i128 doors (b38_to_i128, b38_from_i128) use __int128 — GCC and
 * Clang on every supported target. Check b38_version() before trusting
 * the surface; it is bumped on every breaking change.
 *
 * v3 — the RATIONAL doors. Fractions are the storage: "p/q" over the
 * same alphabet, ALWAYS reduced, denominator positive, sign on the
 * numerator ("+5/+4"), a bare integer rides as "n/1", zero is "0".
 * The radix door is a VIEW, never the storage: "0.(cp)" is a third
 * (the recurring block in trailing parens), "0.1" is 1/38, "0.sj" is
 * three quarters. The Euclidean floor split puts the sign on the
 * integer part — "-1.j" is minus one half. A base-38 literal like
 * "0.75" is NOT decimal and refuses (no digit '7'? no — '7' IS a
 * digit; "0.75" reads as 7·38^-1 + 5·38^-2 = 0.191..., the INANNA
 * trap: only the fraction door means what a human means).
 */

#ifndef B38_H
#define B38_H

#ifdef __cplusplus
extern "C" {
#endif

/* The ABI version. Bump on every breaking change to this surface.
 * v1: b38_add alone. v2: the full certified lane (sub, mul, div_rem,
 * neg, cmp, to_i128, from_i128). v3: the rational layer — fractions
 * and the radix VIEW doors below. */
extern unsigned int b38_version(void);

/* Add a and b exactly. NULL on error (bad input, allocation failure). */
extern char *b38_add(const char *a, const char *b);

/* Subtract b from a exactly. NULL on error. */
extern char *b38_sub(const char *a, const char *b);

/* Multiply a by b exactly. NULL on bad input, a product beyond the
 * i128 shore, or allocation failure. */
extern char *b38_mul(const char *a, const char *b);

/* Negate a exactly. NULL on error. */
extern char *b38_neg(const char *a);

/* Euclidean quotient-remainder of a / b (the remainder lies in
 * 0..|b|). Writes the quotient string to *out_q and the remainder
 * string to *out_r; the caller frees both with b38_free. Returns 0 on
 * success, B38_REFUSAL (-1) on refusal — bad input, the Void divisor b,
 * a beyond-shore quotient or remainder, or allocation failure — and on
 * refusal leaves *out_q and *out_r untouched. */
extern int b38_div_rem(const char *a, const char *b, char **out_q, char **out_r);

/* The honest shore door: parse a and write its exact i128 value to
 * *out. Returns 0 on success, B38_REFUSAL (-1) on refusal — bad input,
 * or a string whose value sits beyond the i128 shore. Never wraps. */
extern int b38_to_i128(const char *a, __int128 *out);

/* Format an exact i128 value as its canonical balanced base-38 string,
 * written to *out (the caller frees it with b38_free). The value never
 * refuses; returns 0 on success, B38_REFUSAL (-1) only on allocation
 * failure, with *out untouched. */
extern int b38_from_i128(__int128 v, char **out);

/* Order a and b as exact integers, like strcmp: a negative value if
 * a < b, zero if equal, a positive value if a > b (returns -1, 0, +1).
 * On bad input returns B38_CMP_REFUSAL — a positive value no valid
 * comparison ever returns — so a refusal is never mistaken for an
 * order. */
#define B38_CMP_REFUSAL 1000000
extern int b38_cmp(const char *a, const char *b);

/* The RATIONAL doors (v3). Arguments are canonical fraction strings;
 * bare integers ride as n/1. Same ceremony: NULL on refusal, caller
 * owns and frees result strings with b38_free. The cross-product of
 * the compare refuses in-shore exactly like the integer doors. */
extern char *b38_ratio_add(const char *a, const char *b);
extern char *b38_ratio_sub(const char *a, const char *b);
extern char *b38_ratio_mul(const char *a, const char *b);
extern char *b38_ratio_div(const char *a, const char *b);
extern char *b38_ratio_neg(const char *a);

/* Order a and b as exact fractions, like b38_cmp (-1, 0, +1); returns
 * B38_CMP_REFUSAL on refusal. */
extern int b38_ratio_cmp(const char *a, const char *b);

/* The radix VIEW doors: to_radix hands back the base-38 expansion with
 * its recurring block in "(...)" (NULL at the 2^16-digit horizon or a
 * beyond-shore 38*r product); from_radix re-reads a radix string into
 * the canonical fraction store ("0.(cp)" -> "+1/+3") and refuses
 * strings whose closed form crosses the shore — a long view refuses to
 * re-read rather than lie. */
extern char *b38_ratio_to_radix(const char *a);
extern char *b38_ratio_from_radix(const char *a);

#define B38_REFUSAL (-1)

/* Free a string returned by a libb38 function. NULL is a no-op. */
extern void b38_free(char *s);

#ifdef __cplusplus
}
#endif

#endif /* B38_H */