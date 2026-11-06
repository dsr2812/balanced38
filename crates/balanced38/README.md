# balanced38

[![Crates.io](https://img.shields.io/crates/v/balanced38.svg)](https://crates.io/crates/balanced38)
[![Documentation](https://docs.rs/balanced38/badge.svg)](https://docs.rs/balanced38)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](#license)

## ✅ The arithmetic and the shore contract are proved; the crate is tested

**The algebraic laws of the balanced base-38 lane and the signed-i128 refusal contract are proved in Lean 4.**
177 theorems (159 core + 18 shore) · 3,340 lines · core-only (`import Init`, no Mathlib) · **0 errors, 0 sorries.**
The proof ships with this crate — reproduce the Lean model from the tarball alone, in about ten seconds:

```
sh verify/verify.sh       # Lean model: STATUS: PASS — 0 errors and FAILURES: 0 (Lean 4.33.1)
sh verify/verify_all.sh   # Lean + Rust (debug + release)
```

The certificate covers the **mathematical lane** and the **signed-i128
refusal contract** (`verify/Balanced38/Shore.lean`). The Rust crate is a
separate implementation: it is tested against those laws (including an
independent Python oracle and the i128 shore edges), but there is no
refinement proof linking the Rust code to the Lean functions. The proof
is of the lane and its contract; the tests are of the crate. See
[docs/RIGHT_DOOR.md](docs/RIGHT_DOOR.md).

---

A drop-in exact-arithmetic layer that lets any program compute with
rational numbers the way humans write them — no rounding, no overflow
surprises, no binary-decimal conversion tax.

An exact, honest, balanced signed base-38 integer lane. Read the dense
base-38 digits signed — d ≤ 19 is +d, d ≥ 20 is d−38 — and every integer,
positive or negative, gets exactly one form; zero is the empty string.

- **Exact**: add/sub/mul/div/neg carry the digit-invariant. The checked
  doors refuse beyond the i128 shore (`None`); add/sub/neg are total and
  can leave it, and `to_i128` wraps beyond it — use `checked_to_i128` for
  the honest fold.
- **Cheap**: column sums sit in [−37, +39] by construction, so the rebalance
  is one compare and ±38 — no division, no mod — and the whole store is a
  stack-riding `SmallVec<[i8; 26]>`.
- **Certified (the lane and its shore contract) and tested (the crate)**:
  the algebraic laws and the signed-i128 refusal contract are proved
  theorems in Lean 4, core-only (`import Init`, no Mathlib), 0 errors,
  0 sorries. The Rust implementation is tested against them —
  exhaustive unit sweeps, a 3,145-value independent Python oracle, and
  the i128 shore edges. There is no refinement proof linking the two.
  Reproduce with `sh verify/verify_all.sh`. See
  [docs/THEOREM_LEDGER.md](docs/THEOREM_LEDGER.md) and
  [docs/RIGHT_DOOR.md](docs/RIGHT_DOOR.md).

```rust
use balanced38::{Balanced38, Rational38};

let x = Balanced38::from_i128(20);
assert_eq!(x.to_i128(), 20);            // the debt walked up: [−18, 1]
let (q, r) = Balanced38::from_i128(-7)
    .checked_div_rem(&Balanced38::from_i128(2)).unwrap();
assert_eq!((q.to_i128(), r.to_i128()), (-4, 1)); // Euclid's shape

// the promise's store: rationals are exact fractions, never views
let a = Rational38::from_i128s(3, 4).unwrap();
let b = Rational38::from_i128s(1, 2).unwrap();
let sum = a.checked_add(&b).unwrap();
assert_eq!((sum.num().to_i128(), sum.den().to_i128()), (5, 4)); // reduced
```

## The membrane at a glance

| piece | what |
|---|---|
| `Balanced38::from_i128` / `to_i128` | the forced residue walk; `checked_to_i128` is the refusing fold, `to_i128` wraps beyond the shore |
| `Balanced38::checked_add` / `sub` | Avizienis rebalance; sub IS add-of-negation; total, can leave the shore |
| `Balanced38::checked_mul` | the signed grid (cells ≤ 19·19), shore-checked |
| `Balanced38::checked_div_rem` | Euclid: a = q·b + r, 0 ≤ r < |b|, loud refusals |
| `Balanced38::checked_to_i128` | the honest shore door — beyond-shore strings refuse |
| `Balanced38::try_from_dense_digits` / `from_dense_digits` | read a dense store's digits signed; rejects bytes ≥ 38 and trims gaps |
| `Rational38::from_ints` / `from_i128s` | reduced fractions, `den > 0`, sign on the num; refused zero divisors |
| `Rational38::checked_add` / `sub` / `mul` / `div` | the exact algebra, `None` one step past the i128 shore |
| `Rational38::checked_cmp` | cross-products, refused beyond the shore |

`verify/Balanced38/Shore.lean` proves the signed-i128 refusal contract:
`checkedToI128` (`some` iff in range), `checkedMul` (zero-absorbing;
refuses out-of-shore operands/product), `checkedDivRem` (refuses the zero
divisor, `MIN / -1`, and out-of-shore operands). The Rust algorithm that
implements it is tested, not refined.

MIT licensed, zero dependencies beyond `smallvec`.

## What this is not

- **Not a refinement proof.** The Lean model is proved; the Rust
  implementation is tested against it. There is no proof linking the two.
- **Not a general-purpose big-integer library.** It is an i128-shore lane;
  the checked doors refuse beyond the shore.
- **Not a base64-style encoder.** It is a balanced arithmetic lane, not a
  text encoding for arbitrary bytes.

## License

MIT — see [LICENSE](LICENSE). Copyright © Daniel Doyle & dsR1.