# libb38 — the key

[![Crates.io](https://img.shields.io/crates/v/libb38.svg)](https://crates.io/crates/libb38)
[![Documentation](https://docs.rs/libb38/badge.svg)](https://docs.rs/libb38)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](#license)

## ✅ The arithmetic is proved; the ABI is tested

**The algebraic laws of the balanced base-38 lane and the signed-i128
refusal contract are proved in Lean 4** — 177 theorems (159 core + 18
shore) · core-only (`import Init`, no Mathlib) · **0 errors, 0 sorries.**
The proof lives in the companion crate
[`balanced38`](https://crates.io/crates/balanced38) and reproduces from
the tarball alone, in about ten seconds:

```
sh verify/verify.sh       # Lean model: STATUS: PASS — 0 errors and FAILURES: 0 (Lean 4.33.1)
sh verify/verify_all.sh   # Lean + Rust (debug + release)
```

The certificate is about the **mathematical lane**. The C-ABI library is a
separate implementation: it is tested against those laws, but there is no
refinement proof linking the C/Rust code to the Lean functions. The proof
is of the lane; the tests are of the key. See `docs/RIGHT_DOOR.md` in
the `balanced38` crate.

---

A drop-in exact-arithmetic layer that lets any program compute with
rational numbers the way humans write them — no rounding, no overflow
surprises, no binary-decimal conversion tax.

**What it is:** a standalone C-ABI library. Balanced base-38 strings in,
exact answers out — add, sub, mul, div_rem, neg, cmp, and the honest
i128 doors. No runtime, no dependencies. Rust crate, Python wheel, and
a man page.

From a fresh clone, the hand-it-to-a-stranger proof is these three
lines, in this order — build, link, run:

```
cargo build -p libb38
cc crates/libb38/examples/smoke.c -I crates/libb38/include \
   -L target/debug -Wl,-rpath,$PWD/target/debug -llibb38 -o smoke
./smoke
libb38 version 3
ALL SMOKE CHECKS PASS
```

The `-L` / `-I` paths are relative to the WORKSPACE ROOT (where the
`cargo build` lands `target/debug/liblibb38.so`); the man page's BUILDING
section carries the same spell.

## The Hubble receipt — one sum, three doors

Early-universe H₀ (CMB, Planck 2018 ΛCDM) is 67.4 km/s/Mpc; the SH0ES
2022 distance ladder gives 73.04. Scaled by 100 and written in balanced
base-38 (decimal 7304 = `"+528"`, decimal 6740 = `"+4pe"` — the strings
are base-38, not decimal), the exact residual is 564/100 = 141/25 = 5.64:

| door | the same arithmetic |
|---|---|
| Rust | `libb38::add("+528", "-4pe")` → `"+ew"` (= 564) — `examples/hubble.rs` |
| C | `b38_add("+528", "-4pe")` → `"+ew"` — the last check in `smoke.c` |
| Python | `libb38.add("+528", "-4pe")` → `"+ew"` — the last case in the receipt |

And as a fraction, v3: `b38_ratio_add("+3r/+p", "+3r/+p")` →
`"+7g/+p"` (141/25 twice — 282/25 = 7·38 + 16), whose radix VIEW is
`"+5.(oc631jsxgrdpvy_i94la)"` (period 20), the exact base-38 expansion.

No tolerance applied. No pass/fail criterion. No seal. The residual is
printed exact; no derivation from established physics closes the gap
without new physics or unquantified systematics.

## The format

A balanced base-38 number is a signed, MSB-first string over the alphabet
`0-9 a-z _ ~` (that is: 0–9, 10–35, 36, 37). `"0"` is zero — the Void.
`"-1"` is minus one, `"+f"` is plus fifteen, `"1z"` is 73. No leading
zeros. Every value has exactly one string.

## Rust

```rust
use libb38::{add, parse, display};
assert_eq!(add("f", "g"), Some("+v".to_string()));
let sum = parse("f").unwrap().checked_add(&parse("g").unwrap());
assert_eq!(display(&sum), "+v");
```

Build the C libraries:

```
cargo build -p libb38           # target/debug/liblibb38.so, .a
```

## C

`include/b38.h` (see `examples/smoke.c`):

```c
char *s = b38_add("f", "g");   /* "+v" */
b38_free(s);
```

The full arithmetic lane is behind the key — the Lean certificate covers
the model, the C ABI is tested:

| door | meaning | refuses when |
|---|---|---|
| `char *b38_add(a, b)` | exact sum | bad input |
| `char *b38_sub(a, b)` | exact difference | bad input |
| `char *b38_mul(a, b)` | exact product | bad input, a product beyond the i128 shore |
| `char *b38_neg(a)` | exact negation | bad input |
| `int b38_div_rem(a, b, &q, &r)` | Euclidean quotient + remainder (`0..|b|`) | bad input, the Void divisor, beyond-shore |
| `int b38_to_i128(a, &v)` | the integer a string names | bad input, beyond-shore string |
| `int b38_from_i128(v, &s)` | the canonical string of an integer | only allocation failure (the value never refuses) |
| `int b38_cmp(a, b)` | order, like `strcmp` | bad input (`B38_CMP_REFUSAL`) |
| `char *b38_ratio_add(a, b)` | exact fraction sum | bad input, beyond-shore |
| `char *b38_ratio_sub(a, b)` | exact fraction difference | bad input, beyond-shore |
| `char *b38_ratio_mul(a, b)` | exact fraction product | bad input, beyond-shore |
| `char *b38_ratio_div(a, b)` | exact fraction quotient | bad input, the Void divisor, beyond-shore |
| `char *b38_ratio_neg(a)` | exact fraction negation | bad input |
| `int b38_ratio_cmp(a, b)` | order fractions exactly | bad input, a beyond-shore cross-product |
| `char *b38_ratio_to_radix(a)` | the base-38 expansion, `(…)` for the repeating block | bad input, the 2^16-digit horizon, a beyond-shore `38·r` product |
| `char *b38_ratio_from_radix(a)` | a radix view back into the fraction store | bad input, a closed form past the shore |

String-returning doors return NULL on refusal; the integer doors return
`B38_REFUSAL` (-1) and leave their outputs untouched. Never a wrapped
value. The caller owns every returned string and must free it with
`b38_free`. The i128 doors use `__int128` (GCC/Clang). `b38_version()`
identifies the ABI (v3 — the surface grew from `b38_add` alone to the
full lane and the rational layer).

## The fraction and the view

A fraction string is storage: `"p/q"` over the same alphabet, ALWAYS
reduced, denominator positive, the sign on the numerator —
`"6/8"` normalizes to `"+3/+4"`, a bare integer rides as `n/1`, zero is
`"0"`. The radix string is a VIEW, never the storage: `"0.(cp)"` is a
third, `"0.sj"` is three quarters, `"0.1"` is a thirty-eighth. The
Euclidean floor split puts the sign on the integer part — `"-1.j"` is
minus one half. A base-38 lookalike like `"0.75"` is NOT decimal
(`'7'` and `'5'` are just digits — it reads as 7/38 + 5/38² ≈ 0.191):
only the fraction door means what a human means.

## Python

```
cd python && python3 setup.py build_py && pip install .   # or
export LIBB38_SKIP_BUILD=1 && pip install .               # reuse existing .so
python3 - <<'EOF'
import libb38
print(libb38.add("f", "g"))   # '+v'
EOF
```

The wheel bundles the native library; the consumer needs no compiler.

## Man page

`man b38_add` once `dist/b38_add.1` is installed (see `docs/b38_add.1`).

## The line

> Build it. Hand it to one stranger. Watch it work.

It computes with balanced base-38 strings exactly — add, sub, mul,
div_rem, neg, cmp, and the honest i128 doors — and nothing else. Let
everything else wrap it.

## License

MIT — see [LICENSE](LICENSE). Copyright © Daniel Doyle & dsR1.