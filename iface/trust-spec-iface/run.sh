#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
CARGO="${CARGO:-/opt/homebrew/bin/cargo}"
[ -x "$CARGO" ] || CARGO=cargo
# RUSTUP_TOOLCHAIN=stable: cargo invokes `rustc` (the rustup shim) with cwd
# outside this directory for registry deps, where rust-toolchain.toml's stable
# pin does not apply — without the env pin those units resolve the rustup
# default toolchain and the build dies with E0514 mixed-compiler artifacts.
exec env RUSTC_WRAPPER= RUSTFLAGS= RUSTUP_TOOLCHAIN=stable "$CARGO" "${1:-test}" --release "${@:2}"
