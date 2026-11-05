# Changelog

All notable changes to the libb38 crate. The receipt is in every build's
smoke test; this ledger just numbers them.

## [0.3.1] — 2026-11-04

The honest-front-door patch. **C-ABI stays v3; no new operations.**

- **Dependency pin** — `balanced38 = "1.2.0"`. This is why `balanced38`
  goes first at press time.
- **Right Door wording** — the Lean certificate proves the mathematical
  lane and its shore contract in the companion crate; this C-ABI library
  is tested against those laws, not refinement-proved. The public docs
  use engineering wording only; no private links.
- Rustfmt pass; README badges and a License section.
- Lint armor: `#![deny(unsafe_op_in_unsafe_fn)]` (the FFI blocks were
  already explicit — the lint now keeps them that way).

## [0.3.0] — 2026-09-17

The promise lands — rational numbers the way humans write them.

- **C-ABI v3**: the `b38_ratio_*` family — `add` / `sub` / `mul` / `div`
  / `neg` / `cmp` over exact reduced fractions (`"p/q"`, sign on the
  numerator, denominator positive, `"0"` the Void), built on the new
  `balanced38::Rational38` (1.1.0). A zero divisor, a two-slash string,
  a beyond-shore cross-product, all refuse loudly.
- **The radix VIEW doors**: `b38_ratio_to_radix` (base-38 expansion with
  the recurring block in trailing `(…)` — `"0.(cp)"` is a third,
  `"0.sj"` is three quarters; the Euclidean floor split reads `"-1.j"`
  for minus one half) and `b38_ratio_from_radix` (a view back into the
  fraction store, refusing at the 2^16-digit horizon and any closed
  form that crosses the i128 shore). The fraction is storage; the radix
  is exact-or-refused.
- `b38_version()` → 3, `libb38` → 0.3.0, `balanced38` → 1.1.0
  (Rational38 core, Lean certificate untouched).
- Two genuine novelty bugs surfaced and fixed in the string layer: the
  radix walk's repeat detection keyed the wrong remainder (one digit
  off; now keyed by the current state at digit production), and the
  paren-content check in the view parser swallowed its own closing
  brace (now bounded to the content between the parens).
- Python wrapper grows `ratio_add` … `ratio_from_radix`; the wheel
  receipt runs 82 exact cases + 32 refusals, the same strings as the C
  smoke. Man page, header, README all updated to the v3 surface.

## [0.2.0] — 2026-09-17

The complete C surface — the key that turns the whole arithmetic set.

- C-ABI v2: `b38_sub`, `b38_mul`, `b38_neg`, `b38_div_rem` (Euclidean),
  `b38_cmp` (like `strcmp`, with the `B38_CMP_REFUSAL` sentinel),
  `b38_to_i128` (the honest shore door via `checked_to_i128`),
  `b38_from_i128` (infallible on the value). Every ceremony kept:
  parse, compute, `fmt`, loud refusal — never a wrapped value.
- The i128 doors carry `__int128` (GCC/Clang), freed by `b38_free`.
- Python wrapper grows `sub` / `mul` / `neg` / `div_rem` / `cmp` /
  `to_i128` / `from_i128`; `version()` now returns 2. The wheel receipt
  runs 44 exact cases + 24 refusals, the same strings as the C smoke.
- Two genuine fixes surfaced by the new extremes: `fmt_b38_str` no
  longer overflows on `i128::MIN` (uses `unsigned_abs`), and `parse` is
  sign-applied and checked per place, so a beyond-shore magnitude
  refuses at parse instead of truncating into a wrapped lie.
- Man page (`docs/b38_add.1`) covers the full surface; README carries
  the door table; `b38_version()` bumped to 2.

## [0.1.0] — 2026-09-16

The key.

- `b38_add`: two balanced base-38 strings in, exact sum out. Zero
  allocation for the common path; one heap borrow for the wide path,
  freed by `b38_free`.
- `b38_version`: a `MAJOR.MINOR.PATCH` string.
- Language surfaces: Rust (`balanced38`), C (`include/b38.h` +
  smoke), Python (ctypes wrapper + receipt tests, wheel bundles the
  native library), man page (`docs/b38_add.1`).
- Built on `balanced38` 1.0.0 — one lane, one law, several doors.

[0.1.0]: https://crates.io/crates/libb38