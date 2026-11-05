# THE RIGHT DOOR — what the Lean certificate covers, and what it does not

**Date:** 2026-11-04
**Status:** audit receipt. Claim narrowed; the i128 refusal contract is
now proved; no new version pressed.
**Cost:** $0 model spend.
**Owner:** Daniel Doyle.

## The one sentence

> The arithmetic is proved; the i128 refusal contract is proved; the
> implementation is tested; the bridge between model and code is a
> refinement proof that does not yet exist.

This is not a takedown. It is the footnote that makes the claim
bulletproof.

---

## What the certificate covers 🟢

The Lean 4 files `lean/Balanced38/Balanced38.lean` (3,118 lines, 159
theorems) and `lean/Balanced38/Shore.lean` (222 lines, 18 theorems) —
`import Init` only, 0 sorries — prove the **mathematical lane** and the
**signed-i128 refusal contract**:

| law | theorem | what it says |
|---|---|---|
| unique canonical form | `canonical_unique` | two in-range, no-trailing-zero lists with the same value are equal |
| round-trip | `from_i128_value`, `from_i128_canonical` | for `\|v\| < 2^127`, the walk returns `v`; the output is canonical |
| add | `checked_add_value`, `addDigits_value`, `checked_add_canonical` | the value is the sum; the output is canonical under the digit invariant |
| sub / neg | `sub_value`, `to_i128_neg`, `double_reflection_is_identity` | subtraction is add-of-negation; the mirror is exact |
| mul | `product_law`, `schoolbook_mul_value`, `checked_mul_canonical` | the value is the exact product; the output is canonical |
| div / rem | `div_rem_identity`, `tmod_band`, `div_rem_euclidean_band`, `identity_carries_through_the_lane` | `a = q·b + r`, `0 ≤ r < \|b\|` |
| shore bound | `shore_fold`, `shore_fold_to_i128`, `shore_fold_stored` | every in-range string of ≤ 24 places folds inside i128 |
| fast walk | `from_i128_fast_eq_from_i128` | the two conversion walks are digit-identical |
| i128 fold contract | `checkedToI128_eq_some_iff`, `checkedToI128_eq_none_iff`, `checkedToI128_value` | `some v` iff `v = to_i128 x` and `inI128 v`; `none` iff out of range |
| i128 product contract | `checkedMul_value`, `checkedMul_none_of_left_out`, `checkedMul_none_of_right_out`, `checkedMul_none_of_product_out`, `checkedMul_some_in_shore` | zero is absorbing; otherwise refuses out-of-shore operands or product; exact value when `some` |
| i128 division contract | `checkedDivRem_zero`, `checkedDivRem_min_neg_one`, `checkedDivRem_none_of_left_out`, `checkedDivRem_none_of_right_out` | refuses the zero divisor, `MIN / -1`, and out-of-shore operands |

`lake build` is not the receipt for `Shore.lean`; the direct `lean`
driver is. `sh verify/verify.sh` compiles the core, the Shore contract,
and the smoke test: `STATUS: PASS — 0 errors and FAILURES: 0`.

**What this means:** the algebra of the lane and the i128 refusal
contract are not claims. They are checked theorems about the Lean model.

---

## The gap 🔴

**The core model is unbounded; the Shore module is the bounded contract.
The Rust code is still a separate implementation.**

- The core's `checked_to_i128` is total (`checked_to_i128_value`), and
  its `checked_mul` always returns `some`. That is the mathematical lane,
  not the i128 runtime.
- `Shore.lean` proves the contract the Rust crate implements:
  - `checkedToI128 x = some v` iff `v = to_i128 x` and `inI128 v`;
    `none` iff out of range.
  - `checkedMul` is zero-absorbing; otherwise refuses out-of-shore
    operands or product; exact value when `some`.
  - `checkedDivRem` refuses the zero divisor, `MIN / -1`, and
    out-of-shore operands.
- **What remains unproved is the Rust algorithm itself.** The chunked
  `38^12` conversion, the `i32` schoolbook multiply, and the exact
  runtime refusal path are tested, not refined from the Lean functions.
  There is no theorem that Rust implements the Lean model.
- The `shore_fold` theorem covers `|v| < 2^127` and excludes
  `i128::MIN`; the Shore contract **includes** `MIN`.
- Trust base: Lean 4.33.1, `import Init`, 0 sorries; `native_decide` is
  used in `shore_bound_num` / `shore_fold` and in `inI128_zero`, alongside
  `propext`, `Classical.choice`, `Quot.sound`.

**The precise claim:** the algebraic laws and the i128 refusal contract
are proved for the model. The Rust implementation is tested against
them. The refinement bridge does not exist.

---

## The Rust seams — fixed and tested 🟢

| seam | before | now |
|---|---|---|
| `checked_div_rem` with divisor `i128::MIN` | debug panic from `b.abs()` | `unsigned_abs()` band check; `1/MIN`, `MIN/MIN`, `-1/MIN` tested |
| `checked_pow` beyond the shore | `.expect(...)` panic | `?` — returns `None`; `2^127` and `2^200` tested |
| `from_dense_digits` invalid bytes | debug panic / release wrap | `try_from_dense_digits` rejects bytes ≥ 38; `from_dense_digits` panics clearly |
| `from_dense_digits` trailing gaps | non-canonical; `Eq`/`Ord` disagreed | trailing gaps trimmed; `[0]` is zero, `[1,0]` equals `[1]` |
| `to_i128` beyond the shore | debug panic, release wrap | explicit `wrapping_*` in both profiles |
| `checked_mul` huge operand | `i32` grid could be stressed | operands longer than 25 places refuse before the grid |
| invalid digit in a raw store | folded a lie | `checked_to_i128` / `checked_mul` return `None` |
| `Rational38` sign read | unchecked `to_i128` | `checked_to_i128()?` — beyond-shore denominators refuse |
| `checked_add` / `sub` / `negate` | blanket "refuses loudly" claim | documented as total; they can leave the i128 shore — use `checked_to_i128` |

---

## The receipts 🟢

```
cargo test -p balanced38              # 34 unit + 5 differential, 0 failed (debug, 236.60s)
cargo test -p balanced38 --release    # 34 unit + 5 differential, 0 failed (release, ~24s)
cargo test -p libb38                  # 21 passed
cargo test -p weave-num               # 193 passed
sh verify/verify.sh                   # core + Shore + smoke: 0 errors, FAILURES: 0
sh verify/verify_all.sh               # the crate + the Lean model, one command
```

Lean certificate: **159 core theorems + 18 shore-contract theorems =
177**, 3,340 lines total, 0 sorries.

New tests:

- `the_min_divisor_is_not_a_panic`
- `checked_pow_refuses_instead_of_panicking`
- `the_dense_door_validates_and_canonicalises`
- `to_i128_wraps_beyond_the_shore`
- `invalid_digits_refuse_the_checked_doors`
- `huge_operands_refuse_before_the_grid`
- `beyond_shore_denominators_refuse_at_the_sign_read`
- `the_negative_lane_round_trips`

The paper's old **158 declarations** was a stale count; the core theorem
declarations are **159**, and the shore module adds **18**.

---

## The honest claim

**For the crate README:**

> The algebraic laws of the balanced base-38 lane and the signed-i128
> refusal contract are formally verified in Lean 4 (177 theorems,
> 0 sorries). The Rust implementation is tested against them, including
> an independent Python oracle (3,145 values) and the i128 shore edges.
> There is no refinement proof linking the Rust code to the Lean model;
> the proof is of the lane and its contract, the tests are of the crate.

**For the paper:**

> The shore theorem proves the ≤ 24-place bound. The 25+ refusal
> **contract** is proved in `Shore.lean` (`checkedToI128`,
> `checkedMul`, `checkedDivRem`), including `i128::MIN`. The Rust
> implementation of that contract is tested, not refined line by line;
> `to_i128` still wraps beyond the shore, while `checked_to_i128` is the
> separate refusing door.

**Sentences to strike:**

- "Formally verified — machine-checked, not claimed" as a **crate**
  headline. Say: "the arithmetic and the shore contract are formally
  verified; the implementation is tested."
- "The arithmetic laws of this number system are proved correct in
  Lean 4." Say: "the mathematical lane and its i128 refusal contract
  are proved."
- "Beyond the i128 shore, the lane refuses loudly (`None`)." The
  **checked** doors refuse; add/sub/neg are total and can exceed the
  shore; `to_i128` wraps.
- "The wrap that `to_i128` used to give beyond the shore was replaced
  by a refusal." `checked_to_i128` was added beside it; `to_i128` still
  wraps.
- "Every operation law is tested exhaustively against the hardware
  oracle." The Python oracle is nonnegative and in-shore; the unit
  sweeps are small-range.

---

## What would close it 🟡

- **B — done (this pass).** `Shore.lean` proves the i128 refusal
  contract, including `i128::MIN`. It proves the contract, not the Rust
  algorithm.
- **C — refinement proof.** Prove the Rust algorithms (chunked
  conversion, `i32` schoolbook, `SmallVec` layout) match the Lean
  functions. Aeneas/Charon or a hand proof; specialist work. Not needed
  for an honest claim.
- **A + D — done earlier.** A is the wording and this receipt; D is the
  boundary tests and the code fixes.

---

## Labels

🟢 measured / verified · 🟡 partial / tested, not proved · 🔴 gap · ⚪ unknown.

The Lean proof is 🟢 for the mathematical lane and the i128 refusal
contract. The Rust bridge is 🟡 tested, not proved. The refinement proof
is 🔴.
