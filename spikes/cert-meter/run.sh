#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
source "$(dirname "$0")/../trust-runner.sh"
trust_exec "${1:-test}" --release --locked "${@:2}"
