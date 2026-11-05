# THE THEOREM LEDGER — balanced38, one page

The balanced signed base-38 lane. Digits 1..=19 are +, 20..=37 are −18..=−1
read signed, zero is the empty string ("the Void"). The digit set
{−18..−1, 0, +1..+19} is a complete residue system mod 38, so the residue
walk is forced at every place and every integer has exactly one form.

## The laws

| # | Law | Status | Where |
|---|---|---|---|
| 1 | **Unique form**: every integer has exactly one membrane string; zero only as the empty string; no string ends on a gap | exhaustive test (−20k..+20k) + Lean canonicality | `every_integer_has_exactly_one_form`; Lean `from_i128_canonical` |
| 2 | **Add**: value of the scribe's add = sum of the values; column sums t ∈ [−37, +39], settled by compare and ±38 | exhaustive (2500² pairs) + Lean | `the_opposing_pair_resolves_to_the_void`; Lean `checked_add_value`, `addDigits_value`; the Avizienis invariant + closure: `column_sum_bounds`, `rebalance_invariant` (11 Sep) |
| 3 | **Negation**: digit-wise mirror with the debt walked up; −(+19) rebalances; negate∘negate = id | exhaustive (−5000..+5000) + Lean | `the_double_reflection_is_the_identity`; Lean `to_i128_neg` |
| 4 | **Reflection law**: sub IS add-of-negation | exhaustive (3000² pairs) + Lean | `sub_is_add_of_the_negation`; Lean `sub_value` |
| 5 | **Mul**: signed grid folds to the exact product; cells ≤ 19·19 = 361, half the dense bound; **Rust**: product beyond the i128 shore refused (None); **Lean**: the value law is total (unbounded `Int`) | exhaustive (1500²) + 20k wide + shore refuse + Lean | `the_signed_grid_…`, `the_wide_product_law`, `the_shore_refuses_…`; Lean `product_law`, `schoolbook_mul_value` |
| 6 | **Div**: Euclid's shape a = q·b + r, 0 ≤ r < |b|, carried through the lane's OWN mul and add; **Rust**: Void divisor and i128::MIN ÷ −1 refused loudly; **Lean**: the `Int` identity is total | exhaustive (1500²) + 20k wide + Lean | `the_identity_carries_through_the_lane`, `the_wide_shore_law`; Lean `identity_carries_through_the_lane`; the band is a theorem: `tmod_band`, `div_rem_euclidean_band` (11 Sep) |
| 7 | **The shore bound and the refusal contract**: ≤ 24 places fold inside i128 (largest 19·(38²⁴−1)/37 ≈ 4.2e37 < 2¹²⁷−1). The **contract** is proved in `Shore.lean`: `checkedToI128` (`some` iff in range), `checkedMul` (zero-absorbing; refuses out-of-shore operands/product), `checkedDivRem` (zero divisor, `MIN / -1`, out-of-shore operands), **including `i128::MIN`**. The Rust algorithm is tested, not refined | **PROVEN in Lean:** `shore_bound_num` (19·(38²⁴−1) < 37·(2¹²⁷−1), native_decide), `shore_bound_frac`, `lval_geom_bound`, `shore_fold`, `shore_fold_stored`/`shore_fold_to_i128`; plus `Shore.lean`'s 18 contract theorems | `shore_bound_num`, `shore_fold` in Balanced38.lean; `Shore.lean`; `cargo test` shore receipts (24×19 folds, 25×19 refuses) |
| 8 | **Alphabet mirror**: dense_digit ∘ membrane_digit = id, both ways | exhaustive over all 38 digits + 0..50k above-gate strings | `the_alphabet_mirror_round_trips` |

## The Lean certificate

Shipped with the crate in `verify/`: `Balanced38.lean` — **3,118 lines,
159 theorems** — and `Shore.lean` — **222 lines, 18 theorems**;
core-only (`import Init`, no Mathlib), 0 errors, 0 sorries.
The **mathematical lane's** arithmetic-law spine is proven: add, sub, mul,
div, neg, canonical form, the O(n) fast walk `from_i128_fast` is certified
digit-identical to the reference walk, and the SHORE BOUND (A1) is a
theorem. `Shore.lean` proves the **signed-i128 refusal contract**:
`checkedToI128` (`some` iff in range), `checkedMul` (zero-absorbing;
refuses out-of-shore operands/product), and the `checkedDivRem` refusals
(zero divisor, `MIN / -1`, out-of-shore operands). `SmokeTest.lean` (168
lines): 2116 pairs × (mul+div) + 46 roundtrips + the shore edge,
**0 failures** — cross-checking the **Lean-compiled model**, not the Rust
crate, against native integer arithmetic at runtime.

The Rust crate is a separate implementation. Its laws are tested
(`cargo test`, debug and release) and cross-checked against a 3,145-value
independent Python oracle; there is no refinement proof linking the Rust
code to the Lean functions. The proof is of the lane; the tests are of the
crate.

A stranger reproduces the certificate in one command, from the crate
tarball alone:

```
sh verify/verify.sh       # Lean model: STATUS: PASS — 0 errors and FAILURES: 0 (Lean 4.33.1)
sh verify/verify_all.sh   # Lean + Rust (debug + release)
```

## What this lane is not

Not a bignum race: it stops at the i128 shore by design. The checked
doors refuse beyond it; add/sub/neg are total and can leave it; `to_i128`
wraps beyond it. The claim is exactness and honesty — the checked doors
never return a wrapped lie.