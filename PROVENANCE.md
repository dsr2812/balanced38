# Provenance

This repository is a clean public mirror, not the private workshop.

## Source tarballs

| crate | version | crates.io checksum |
|---|---|---|
| `balanced38` | 1.2.1 | `36fb38d0b54036c75c5de0dd6c5d729ea296b60e0b385036da777226d0bbe18a` |
| `libb38` | 0.3.2 | `10b713d6fd0b6b1aaa29a71945d6bbe8ac5b612db03414db4d8a13c815fbef72` |

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
