# Provenance

This repository is a clean public mirror, not the private workshop.

## Source tarballs

| crate | version | crates.io checksum |
|---|---|---|
| `balanced38` | 1.2.0 | `6a4cdc2908e9f2704e780751bfc3a148cc8f1670fe4c6eda97bda6c6bd75466a` |
| `libb38` | 0.3.1 | `cf152d1a481d50a0852ba07221a484a3289d524d59bb6891045f3f30ba3eb5b4` |

## What was omitted

- `.cargo_vcs_info.json` — packaging metadata that carries a private git
  commit hash and the path inside the private tree.
- `Cargo.toml.orig` — Cargo packaging artifact; the normalized
  `Cargo.toml` is the published manifest.
- Per-crate `Cargo.lock` — the workspace has one `Cargo.lock`.

## What was added

- A workspace `Cargo.toml` so both crates build together.
- This README, `LICENSE`, `SECURITY.md`, `CONTRIBUTING.md`, and
  `PROVENANCE.md`.

The source files under `crates/` are the published 1.2.0 / 0.3.1 files.
No private history, no old 1.1.0 / 0.3.0 records, and no private documents
are included.

## Check

```sh
cargo test --workspace
```

The Lean certificate is checked from `crates/balanced38`:

```sh
sh verify/verify.sh
```
