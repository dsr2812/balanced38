# verify — the balanced38 Lean certificate, shipped with the crate

The arithmetic laws of the **mathematical lane** and the **signed-i128
refusal contract** are proven theorems in Lean 4. This directory carries
the proof so a stranger can reproduce the certificate without leaving the
crate: no thesis, no repo spelunking, no Mathlib.

The certificate is not a refinement proof of the Rust crate. The crate is
a separate implementation, tested against the laws; the i128 refusal
contract is proved for the model in `Shore.lean`, while the Rust runtime
door is tested against it. See `docs/RIGHT_DOOR.md`.

## What is proven

`Balanced38.lean` (3,118 lines) proves, core-only (`import Init`, no
Mathlib), 0 sorries:

- the **canonical form** — every integer has exactly one membrane string,
  no string ends on a gap, the Void is the empty string
- **add** — value of the scribe's add = sum of the values
  (`checked_add_value`, `addDigits_value`, the Avizienis invariant:
  `column_sum_bounds`, `rebalance_invariant`)
- **sub** — sub IS add-of-negation (`sub_value`)
- **mul** — the signed grid folds to the exact product
  (`product_law`, `schoolbook_mul_value`), with the reflection law
- **div/rem** — Euclid's shape a = q·b + r, 0 ≤ r < |b|
  (`tmod_band`, `div_rem_euclidean_band`, `identity_carries_through_the_lane`)
- **neg** — the mirror with the debt walked (`to_i128_neg`,
  `double_reflection_is_identity`)
- **the shore bound** — every ≤24-place string folds inside i128
  (`shore_bound_num`, `shore_bound_frac`, `lval_geom_bound`,
  `shore_fold`, `shore_fold_stored`).
- **the i128 refusal contract** — `Shore.lean` proves `checkedToI128`
  (`some` iff in range), `checkedMul` (zero-absorbing; refuses
  out-of-shore operands or product), and the `checkedDivRem` refusals
  (zero divisor, `MIN / -1`, out-of-shore operands). This is the
  **contract**, not the Rust algorithm.
- the **fast walk** `from_i128_fast` is digit-identical to the
  reference walk

## What is not proven

- The Rust algorithms (chunked `38^12` conversion, `i32` schoolbook
  multiply) are not refined from the Lean functions. There is no
  theorem that Rust implements the Lean model; the crate's refusal path
  is tested by `cargo test`.
- `shore_fold` covers `|v| < 2^127`; it excludes `i128::MIN`. The Shore
  contract **includes** `MIN`.
- `native_decide` is part of the trust base (`shore_bound_num`,
  `shore_fold`, `inI128_zero`), alongside `propext`,
  `Classical.choice`, `Quot.sound`.

`SmokeTest.lean` (168 lines) cross-checks the **Lean-compiled** lane
(the model, not the Rust crate) against native integer arithmetic at
runtime: 2116 pairs × (mul + div), 46 round trips and negations, the
shore edge (24×19 folds, 25×19 value beyond the shore).

## How to reproduce

```
sh verify.sh        # the Lean model and its shore contract
sh verify_all.sh    # the Lean model + the Rust crate (debug + release)
```

`verify.sh` prints `STATUS: PASS — 0 errors and FAILURES: 0`. It verifies
the Lean model, not the Rust crate. The harness:

1. `lean -o Balanced38/Balanced38.olean Balanced38/Balanced38.lean`
   — elaborates and compiles the theorem file (zero errors).
2. `LEAN_PATH=. lean Balanced38/Shore.lean` — elaborates the i128
   refusal contract (zero errors).
3. `LEAN_PATH=. lean Balanced38/SmokeTest.lean` — runs the compiled
   lane's smoke test (`FAILURES: 0`).

Requires the Lean 4 toolchain pinned in `lean-toolchain`
(`leanprover/lean4:4.33.1`), installed via
[elan](https://github.com/leanprover/elan). No lake, no Mathlib, no
network package fetch.

## Single-source note

This directory is the shipped certificate and the artifact of record for
the released crate. When the theorems change, update this copy with them.