# balanced38

[![verify](https://github.com/dsr2812/balanced38/actions/workflows/verify.yml/badge.svg)](https://github.com/dsr2812/balanced38/actions/workflows/verify.yml)

Public mirror of the published crates:

- [`balanced38` 1.2.0](https://crates.io/crates/balanced38/1.2.0)
- [`libb38` 0.3.1](https://crates.io/crates/libb38/0.3.1)

An exact, honest, balanced signed base-38 integer lane, with an exact
rational layer and a C-ABI key.

## Where the releases live

The published releases are on crates.io:

- [`balanced38` 1.2.0](https://crates.io/crates/balanced38/1.2.0)
- [`libb38` 0.3.1](https://crates.io/crates/libb38/0.3.1)

This GitHub repository is the source mirror. Rust packages live on
crates.io; no GitHub Packages are published here.

## What is proved, and what is tested

The algebraic laws of the balanced base-38 lane and the signed-i128
refusal contract are proved in Lean 4:

- **177 theorems** (159 core + 18 shore)
- **3,340 lines**
- core-only (`import Init`, no Mathlib)
- **0 errors, 0 sorries**

The Rust implementation is a separate implementation. It is tested against
those laws — exhaustive unit sweeps, an independent Python oracle, and the
i128 shore edges — but there is **no refinement proof** linking the Rust
code to the Lean functions. The proof is of the lane and its contract; the
tests are of the crate.

## Build and verify

From the repository root:

```sh
cargo build --workspace
cargo test --workspace
```

Lean model:

```sh
cd crates/balanced38
sh verify/verify.sh
```

Full Lean + Rust check:

```sh
cd crates/balanced38
sh verify/verify_all.sh
```

C-ABI smoke test:

```sh
cargo build -p libb38
cc crates/libb38/examples/smoke.c -I crates/libb38/include \
   -L target/debug -Wl,-rpath,$PWD/target/debug -llibb38 -o smoke
./smoke
```

Expected:

```text
libb38 version 3
ALL SMOKE CHECKS PASS
```

## What this is not

- Not a claim that the Rust or C code is formally refined.
- Not a promise that the public API will grow without a version bump.

## Provenance

This repository is generated from the published `.crate` tarballs. See
[`PROVENANCE.md`](PROVENANCE.md) for the checksums and the exact omissions.
No private git history is included.

## License

MIT — see [`LICENSE`](LICENSE). Copyright © Daniel Doyle & dsR1.
