#!/usr/bin/env sh
# THE REPRODUCTION SCRIPT — the balanced38 Lean certificate.
#
# Verifies, for a STRANGER, in one command:
#   1. The theorem file elaborates and compiles with ZERO errors.
#   2. The runtime smoke test reports FAILURES: 0.
#
# Needs only a Lean 4 toolchain (elan). No Mathlib, no network package
# fetch, nothing but the pinned toolchain itself. No lake required —
# the harness uses the plain `lean` driver, the path the certificate
# was validated with.
#
# Usage:  sh verify.sh

set -eu

cd "$(dirname "$0")"

if ! command -v lean >/dev/null 2>&1; then
    echo "lean not found. Install the Lean 4 toolchain with elan:"
    echo "  curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh"
    echo "then re-run:  sh verify.sh"
    exit 1
fi

echo "==> elaborating + compiling Balanced38.lean (theorems; expect 0 errors)"
out="$(lean -o Balanced38/Balanced38.olean Balanced38/Balanced38.lean 2>&1)" || {
    echo "STATUS: FAIL — the theorem file did not elaborate (errors above)"
    exit 1
}
printf '%s\n' "$out" | grep -v '^Balanced38/Balanced38.lean.*warning:' | tail -n 5
if printf '%s\n' "$out" | grep -q 'error'; then
    echo "STATUS: FAIL — errors reported"
    exit 1
fi

echo "==> elaborating Shore.lean (the i128 refusal contract; expect 0 errors)"
out="$(LEAN_PATH=. lean Balanced38/Shore.lean 2>&1)" || {
    echo "STATUS: FAIL — the shore contract did not elaborate (errors above)"
    exit 1
}
printf '%s\n' "$out" | grep -v '^Balanced38/Shore.lean.*warning:' | tail -n 3
if printf '%s\n' "$out" | grep -q 'error'; then
    echo "STATUS: FAIL — errors reported in Shore.lean"
    exit 1
fi

echo "==> running SmokeTest.lean (expect FAILURES: 0)"
out="$(LEAN_PATH=. lean Balanced38/SmokeTest.lean 2>&1)" || {
    echo "STATUS: FAIL — the smoke test did not run (errors above)"
    exit 1
}
printf '%s\n' "$out" | tail -n 4
if printf '%s\n' "$out" | grep -q 'FAILURES: 0'; then
    echo "STATUS: PASS — 0 errors and FAILURES: 0 (Lean $(lean --version 2>/dev/null | grep -o 'version [0-9.]*' | awk '{print $2}'))"
else
    echo "STATUS: FAIL — the certificate did not verify"
    exit 1
fi