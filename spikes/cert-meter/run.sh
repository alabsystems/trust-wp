#!/usr/bin/env bash
# Build and test the cert-meter crate with the Trust toolchain's cargo, targo
# ($CARGO when set), through its explicit unverified lane: this run makes no
# Trust proof claim. Self-contained on purpose: this crate ships in the public
# snapshot and ../trust-runner.sh does not, so `trust_exec` is spelled here,
# the same as the shared runner's.
set -euo pipefail
cd "$(dirname "$0")"
CARGO="${CARGO:-$(command -v targo 2>/dev/null || true)}"
if [ -z "$CARGO" ]; then
  echo "run.sh: targo (the Trust toolchain's cargo) is not on PATH; install the Trust toolchain or set CARGO" >&2
  exit 127
fi
trust_exec() {
  exec env RUSTC_WRAPPER= "$CARGO" --unverified "$@"
}
trust_exec "${1:-test}" --release --locked "${@:2}"
