#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# A guided, self-checking tour of trust-wp as a standalone command-line tool.
#
#   ./demo/run.sh              full tour, including crate mode
#   ./demo/run.sh --quick      skip the crate-mode step (which compiles a crate)
#
# Every step asserts the exit code and a piece of the output, so this doubles as
# a regression test for the CLI's user-visible contract. It exits non-zero if
# anything drifts.

set -u -o pipefail

DEMO_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$DEMO_DIR")"
QUICK=0
[[ "${1:-}" == "--quick" ]] && QUICK=1

# ---------------------------------------------------------------------------
# Presentation
# ---------------------------------------------------------------------------

if [[ -t 1 ]]; then
    B=$'\033[1m'; DIM=$'\033[2m'; GREEN=$'\033[32m'; RED=$'\033[31m'; OFF=$'\033[0m'
else
    B=''; DIM=''; GREEN=''; RED=''; OFF=''
fi

STEP=0
PASSED=0
FAILED=0
FAILURES=()

say() { printf '\n%s%s%s\n' "$B" "$1" "$OFF"; }
note() { printf '%s%s%s\n' "$DIM" "$1" "$OFF"; }

# check <title> <expected-exit> <expected-substring> -- <command...>
#
# Runs the command, shows it and its output, then asserts. `expected-substring`
# may be empty to assert on the exit code alone.
check() {
    local title="$1" want_code="$2" want_text="$3"; shift 4   # drop the `--`
    STEP=$((STEP + 1))
    say "[$STEP] $title"
    printf '%s$ %s%s\n' "$DIM" "$*" "$OFF"

    local output status
    output="$("$@" 2>&1)"
    status=$?
    printf '%s\n' "$output" | sed 's/^/    /'

    local problem=""
    if [[ "$status" != "$want_code" ]]; then
        problem="expected exit $want_code, got $status"
    elif [[ -n "$want_text" && "$output" != *"$want_text"* ]]; then
        problem="expected output to contain: $want_text"
    fi

    if [[ -n "$problem" ]]; then
        FAILED=$((FAILED + 1))
        FAILURES+=("[$STEP] $title — $problem")
        printf '%s    ✗ %s%s\n' "$RED" "$problem" "$OFF"
    else
        PASSED=$((PASSED + 1))
        printf '%s    ✓ exit %s as expected%s\n' "$GREEN" "$status" "$OFF"
    fi
}

# ---------------------------------------------------------------------------
# Find the binary
# ---------------------------------------------------------------------------

find_trust_wp() {
    if [[ -n "${TRUST_WP_BIN:-}" ]]; then printf '%s\n' "$TRUST_WP_BIN"; return; fi
    for candidate in "$REPO_ROOT/target/release/trust-wp" "$REPO_ROOT/target/debug/trust-wp"; do
        [[ -x "$candidate" ]] && { printf '%s\n' "$candidate"; return; }
    done
    command -v trust-wp 2>/dev/null && return
    return 1
}

if ! TRUST_WP="$(find_trust_wp)"; then
    cat >&2 <<'MISSING'
error: no `trust-wp` binary found.

Build one first (from the repo root):

    targo --unverified build -p trust-wp-cli -p trust-wp-driver -p targo-trust-wp -p trust-wp -p creusot-contracts

or point at an existing one:

    TRUST_WP_BIN=/path/to/trust-wp ./demo/run.sh
MISSING
    exit 2
fi

if ! WORK="$(mktemp -d "${TMPDIR:-/tmp}/trust-wp-demo.XXXXXX")" || [[ -z "$WORK" ]]; then
    echo "error: cannot create a scratch directory" >&2
    exit 2
fi
trap 'rm -rf "$WORK"' EXIT

cat <<BANNER
${B}trust-wp — a guided tour${OFF}
${DIM}binary:   $TRUST_WP
scratch:  $WORK${OFF}

trust-wp proves the contracts you write into Rust source. It reads post-borrowck
MIR, turns each contract into a verification condition with a Dijkstra-style
weakest-precondition transformation, and discharges it on the ay SMT solver.
Nothing here runs your program.
BANNER

# ---------------------------------------------------------------------------
# 1. It works with nothing installed and nothing configured
# ---------------------------------------------------------------------------

note "
--- Part 1: is anything even installed? -------------------------------------"

check "The tool reports its own version — no toolchain, no solver, no project" \
    0 "trust-wp " -- "$TRUST_WP" --version

check "'doctor' says what is present and, for anything missing, how to get it" \
    0 "ready" -- "$TRUST_WP" doctor

# ---------------------------------------------------------------------------
# 2. Zero-config first run
# ---------------------------------------------------------------------------

note "
--- Part 2: the first run ---------------------------------------------------
'trust-wp example' writes a small contracted file, and single-file mode
verifies it with no Cargo project, no manifest and no configuration."

check "Write a sample to verify" \
    0 "wrote" -- "$TRUST_WP" example -o "$WORK/demo.rs"

check "Verify it" \
    0 "2 verified, 0 failed, 0 errors" -- "$TRUST_WP" "$WORK/demo.rs"

# ---------------------------------------------------------------------------
# 3. Contracts
# ---------------------------------------------------------------------------

note "
--- Part 3: what a contract buys you ----------------------------------------
#[requires] is the caller's obligation, #[ensures] is what trust-wp proves in
return — for every input, not for the inputs a test happened to try."

check "Three contracted functions, all proved" \
    0 "3 verified, 0 failed, 0 errors" -- "$TRUST_WP" "$DEMO_DIR/01_contracts.rs"

check "Narrow a run to one function with --filter" \
    0 "1 verified" -- "$TRUST_WP" --filter midpoint "$DEMO_DIR/01_contracts.rs"

# ---------------------------------------------------------------------------
# 4. Failure is the interesting case
# ---------------------------------------------------------------------------

note "
--- Part 4: when the contract is false --------------------------------------
The answer is not 'no'. It is the concrete input that breaks the contract, the
clause it breaks, and the line it breaks on. Exit code 1."

check "A false postcondition yields a counterexample" \
    1 "counterexample" -- "$TRUST_WP" "$DEMO_DIR/02_counterexample.rs"

# ---------------------------------------------------------------------------
# 5. Loops
# ---------------------------------------------------------------------------

note "
--- Part 5: loops, without unrolling ----------------------------------------
trust-wp is a deductive verifier, so a loop takes an #[invariant] (the induction
hypothesis) and an optional #[variant] (the termination measure) rather than an
unwind bound. The proof then holds for every number of iterations."

check "Invariant + variant, both proved" \
    0 "2 verified, 0 failed, 0 errors" -- "$TRUST_WP" "$DEMO_DIR/03_loops.rs"

check "An unwind bound is refused, and the alternative is named" \
    3 "#[invariant" -- "$TRUST_WP" --unwind 5 "$DEMO_DIR/03_loops.rs"

# ---------------------------------------------------------------------------
# 6. Show your work
# ---------------------------------------------------------------------------

note "
--- Part 6: the proof obligation itself -------------------------------------
--emit-smt prints the SMT-LIB2 query. It is self-contained: every symbol it
mentions is declared, so you can pipe it straight into a solver. 'unsat' means
the negated postcondition has no model — i.e. the contract holds."

check "Emit the verification condition" \
    0 "(check-sat)" -- "$TRUST_WP" --emit-smt --filter increment "$DEMO_DIR/01_contracts.rs"

# The solver's own comment lines mention the word: "writing Alethe proof to
# ... on unsat". Checking the raw output for "unsat" would therefore pass on a
# `sat` answer too — the exact opposite result. Reduce it to the verdict first.
ay_verdict() {
    ay "$1" 2>/dev/null | grep -v '^c ' | head -1
}

if command -v ay >/dev/null 2>&1; then
    "$TRUST_WP" --emit-smt --filter increment "$DEMO_DIR/01_contracts.rs" 2>/dev/null > "$WORK/vc.smt2"
    check "Hand that query to the solver directly (ay <query>, verdict only)" \
        0 "unsat" -- ay_verdict "$WORK/vc.smt2"
else
    note "(skipping the solver round-trip: no 'ay' on PATH)"
fi

check "--dry-run prints the exact engine command instead of running it" \
    0 "TRUST_WP_ARGS=" -- "$TRUST_WP" --dry-run "$DEMO_DIR/01_contracts.rs"

# ---------------------------------------------------------------------------
# 7. Honesty
# ---------------------------------------------------------------------------

note "
--- Part 7: what it refuses to claim ----------------------------------------
A verifier that says 'fine' when it proved nothing is worse than no verifier.
trust-wp fails closed: a run that examined no obligation is an error, not a
pass — including a --filter that matched nothing."

check "A --filter that matches nothing is an error, not a green run" \
    2 "nothing was verified" -- "$TRUST_WP" --filter no_such_function "$DEMO_DIR/01_contracts.rs"

check "An unknown option is refused rather than ignored" \
    3 "not a trust-wp option" -- "$TRUST_WP" --solver z3 "$DEMO_DIR/01_contracts.rs"

# ---------------------------------------------------------------------------
# 8. Creusot compatibility
# ---------------------------------------------------------------------------

note "
--- Part 8: Creusot-compatible attributes -----------------------------------
The same file written against the creusot_contracts surface verifies unchanged."

check "creusot_contracts attributes, verified by trust-wp" \
    0 "2 verified, 0 failed, 0 errors" -- "$TRUST_WP" "$DEMO_DIR/04_creusot_compat.rs"

# ---------------------------------------------------------------------------
# 9. Crate mode
# ---------------------------------------------------------------------------

if [[ "$QUICK" == "1" ]]; then
    note "
--- Part 9: crate mode (skipped by --quick) ---------------------------------"
else
    note "
--- Part 9: a whole crate ---------------------------------------------------
Run trust-wp with no file inside a Cargo project and it verifies the package,
driving targo with the trust-wp driver as the RUSTC wrapper. This compiles the
contract crates first, so it is the slow step."
    # No subshell: `check` keeps its tallies in this shell's variables.
    HERE="$PWD"
    cd "$REPO_ROOT/examples/verified_math" || exit 2
    check "Verify the verified_math example crate" \
        0 "6 verified, 0 failed, 0 errors" -- "$TRUST_WP"
    cd "$HERE" || exit 2
fi

# ---------------------------------------------------------------------------
# Verdict
# ---------------------------------------------------------------------------

printf '\n%s%s%s\n' "$B" "----------------------------------------------------------------------" "$OFF"
if [[ "$FAILED" == "0" ]]; then
    printf '%sdemo: %d checks, all as expected%s\n' "$GREEN" "$PASSED" "$OFF"
    printf '\nNext:  %s --help   ·   contract-syntax.md for the full grammar\n' "trust-wp"
    exit 0
fi

printf '%sdemo: %d ok, %d unexpected%s\n' "$RED" "$PASSED" "$FAILED" "$OFF"
for failure in "${FAILURES[@]}"; do
    printf '  %s\n' "$failure"
done
exit 1
