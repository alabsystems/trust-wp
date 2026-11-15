#!/usr/bin/env bash
# Build and test the INTERFACE-v1 reference crate with the Trust toolchain's
# cargo, targo ($CARGO when set), through its explicit unverified lane: this
# run makes no Trust proof claim. trust-wp's rustc_private wrapper is not
# meant for this crate (see ../.cargo/config.toml).
set -euo pipefail
cd "$(dirname "$0")"
CARGO="${CARGO:-$(command -v targo 2>/dev/null || true)}"
if [ -z "$CARGO" ]; then
  echo "run.sh: targo (the Trust toolchain's cargo) is not on PATH; install the Trust toolchain or set CARGO" >&2
  exit 127
fi
exec env RUSTC_WRAPPER= "$CARGO" --unverified "${1:-test}" --release --locked "${@:2}"
