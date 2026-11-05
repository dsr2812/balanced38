#!/usr/bin/env sh
# THE WHOLE DOOR — the Lean certificate AND the Rust crate.
#
# `verify.sh` proves the Lean model. This script also runs the Rust
# implementation in debug and release, because the shipped crate is a
# separate object: the bridge is tested, not formally refined.
#
# Usage:  sh verify/verify_all.sh

set -eu

cd "$(dirname "$0")/.."   # the crate root

echo "==> cargo test (debug)"
cargo test --quiet

echo "==> cargo test (release)"
cargo test --release --quiet

echo "==> Lean certificate (the mathematical lane)"
sh verify/verify.sh

echo "STATUS: PASS — Rust tests (debug + release) and the Lean certificate"
