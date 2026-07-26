<!-- Copyright 2026 Andrew Yates -->
<!-- Author: Andrew Yates <andrewyates.name@gmail.com> -->
<!-- Licensed under the Apache License, Version 2.0 -->

# Creusot Compatibility Test Harness

Test harness for measuring trust-wp's compatibility with Creusot's test suite.

## Purpose

This harness runs trust-wp verification against Creusot's test suite to measure
progress toward Creusot feature parity. It supports three canonical test lanes:

- **should_succeed** (default) — tests that Creusot verifies successfully
- **should_fail** — tests that Creusot correctly rejects
- **examples** — standalone Creusot examples under `reference/creusot/examples`

It:

1. Transforms Creusot test syntax to trust-wp syntax (best-effort)
2. Runs `cargo trust-wp` on each test
3. Classifies results as pass/fail/skip/error
4. Outputs results to the selected lane's canonical JSON baseline

## Prerequisites

- Creusot reference at `reference/creusot/` (gitignored)
- Built `cargo-trust-wp` binary: `cargo build --locked -p cargo-trust-wp`
- Python 3.10+

## Usage

### Canonical (full) runs

Full default-lane runs write to the canonical `results.json` baseline. The
canonical refresh script updates all three baseline files used for parity
planning:

- `tests/creusot_compat/results.json` (`should_succeed`)
- `tests/creusot_compat/results-should-fail.json` (`should_fail`)
- `tests/creusot_compat/results-examples.json` (`examples`)

```bash
# Refresh every canonical lane and then run the freshness check
./scripts/refresh-baselines.sh

# Run the default should_succeed lane — writes to results.json
python3 tests/creusot_compat/harness.py

# Same, with verbose output
python3 tests/creusot_compat/harness.py --verbose

# Baseline collection mode (exit 0 regardless of failures)
python3 tests/creusot_compat/harness.py --baseline

# Full auditable baseline refresh set
python3 tests/creusot_compat/harness.py --baseline -v
python3 tests/creusot_compat/harness.py --baseline --lane should_fail --output tests/creusot_compat/results-should-fail.json -v
python3 tests/creusot_compat/harness.py --baseline --lane examples --output tests/creusot_compat/results-examples.json -v
```

### Non-default lanes

The `--lane` option selects which test lane to run. Non-default lanes require
`--output` to prevent accidentally overwriting the canonical baseline.

```bash
# Run should_fail tests
python3 tests/creusot_compat/harness.py --lane should_fail --output tests/creusot_compat/results-should-fail.json

# Run examples
python3 tests/creusot_compat/harness.py --lane examples --output tests/creusot_compat/results-examples.json

# Run all lanes together
python3 tests/creusot_compat/harness.py --lane all --output results-all.json
```

For should_fail tests, classification is inverted:
- trust-wp **rejects** the code (fail/error) -> **pass** (correctly rejected)
- trust-wp **verifies** the code -> **fail** (should have been rejected)
- Unsupported features -> **skip** (same as should_succeed)

### Exploratory (partial) runs

Partial runs use `--filter` and/or `--limit` and **require** an explicit
`--output` path to avoid accidentally overwriting the canonical baseline.

```bash
# Filter tests by pattern (must specify --output)
python3 tests/creusot_compat/harness.py --filter "bug/" --output results-bug.json

# Limit number of tests (must specify --output)
python3 tests/creusot_compat/harness.py --limit 20 --output results-20.json

# Both filter and limit
python3 tests/creusot_compat/harness.py --filter "bug/" --limit 5 --output results-partial.json
```

Omitting `--output` on a partial or non-default-lane run exits with code 3.

By default, partial runs are also **zero-drift**: if `HEAD` advances at all
while a filtered or limited run is executing, or if the harness cannot evaluate
the final drift, the harness exits with code `4` and records
`metadata.routing_safe = false` in the output JSON.

`--baseline` does not waive this partial-run safety gate; it only suppresses
ordinary test failures after the zero-drift policy passes.

To keep a mixed-commit exploratory partial run, pass `--allow-head-drift`.
Those runs stay available for local debugging, but they are explicitly
provisional and must not be used for routing claims, root-cause claims, or
pass/fail movement.

**Verification guidance:** When using partial harness commands in `## Verified`
sections of commits or issue comments, always include `--output` so the command
is directly reproducible. Omitting it produces exit code 3 rather than test
results (#1022).

### Lane-pair freshness signal

When a full canonical lane file is updated (`results.json` or
`results-should-fail.json`), the harness compares commit-age drift between the
two canonical lanes and records `metadata.lane_pair_freshness` commit anchors:

- `current_age_commits` / `paired_age_commits` (lane anchor age vs current HEAD)
- `age_gap_commits` and `max_age_gap_commits`
- `evaluated_against_head` (HEAD used when ages were computed)

Status words are intentionally not persisted in artifacts because they become
stale after HEAD advances. Recompute freshness status against current HEAD with
`--check-baseline-freshness` (or freshness helpers in `harness.py`).

This prevents parity triage from silently mixing fresh should_succeed data with
stale should_fail data.

The `examples` lane is not part of the should_succeed/should_fail pair drift
calculation, but it is part of the absolute canonical freshness check. A missing
or stale `tests/creusot_compat/results-examples.json` makes
`--check-baseline-freshness` fail.

### Run-level HEAD drift policy

Long baseline runs can finish on a different branch tip than they started. The
harness now pins `metadata.git_commit` at run start and compares end-of-run
drift against a policy threshold:

- Full runs keep the existing thresholded policy:
  - `--max-head-drift-commits N` - warn/fail only when drift exceeds `N`
    (default: `10`)
  - `--fail-on-head-drift` - return exit code `4` when drift exceeds the
    policy threshold
- Partial (`--filter` / `--limit`) runs default to a stricter routing-safe
  policy:
  - effective `--max-head-drift-commits 0`
  - effective fail-closed exit code `4` on any non-zero or indeterminate drift
  - `metadata.routing_safe = true` only when drift is confirmed zero
- `--allow-head-drift` opts partial runs back into exploratory mixed-commit
  mode. The output is marked provisional and must not be used for routing-safe
  evidence.

This lets teams keep a stable commit anchor for parity analysis while still
detecting when a run was overtaken by incoming commits.

### Exit codes

| Code | Meaning |
|------|---------|
| 0 | All tests passed or were skipped (no fail/error), or `--baseline` mode |
| 1 | At least one test failed or errored |
| 3 | Usage error (e.g. partial run without `--output`) |
| 4 | HEAD-drift policy violation (`--fail-on-head-drift` on full runs, or any non-zero/indeterminate drift on partial runs unless `--allow-head-drift`) |

## Result Classification

### should_succeed lane (default)

| Status | Meaning |
|--------|---------|
| pass | trust-wp classified the crate as a success: verified obligations, or a clean no-contract / logic-only / proof_assert-only / non-verifiable-contract run |
| fail | Verification reported a concrete failure (`FAILED`, ghost validation failure, or proof-assert failure) |
| unknown | Verification reached an inconclusive `unknown` result without a compiler/driver error |
| skip | Test is outside current verifier coverage, or contracts were found but none were verifiable |
| error | Compilation, driver, or infrastructure failure prevented a meaningful verification result |

**No-contract tests:** Tests with no contract annotations are classified as
`pass` when trust-wp processes the crate without error. Logic-only tests
(containing only `#[logic]` functions) are also classified as `pass` on clean
runs, or `error` if trust-wp fails. Classification-only skips are the narrower
cases where user-written contracts exist but the run produces no verifiable
obligations; those appear as `skip` with reason `no contracts verified`.
`proof_assert!`-only tests follow the proof-assert summary: all assertions
verified is `pass`, while any proof-assert failure is `fail`.

**Strict-rejection passes (#874):** When trust-wp intentionally rejects code
that Creusot accepts (e.g., stricter termination checking), the test is
classified as `pass` because the rejection is correct verifier behavior.
These are included in the `pass` count and separately reported as
`strict_pass` in the summary so metrics consumers can distinguish verifier
improvements from classification policy changes.

**Known spurious proof-assert counterexamples:** A short, documented table
(`_KNOWN_SPURIOUS_PA_COUNTEREXAMPLE_TESTS` in `harness_classify_succeed.py`)
covers should_succeed tests whose every `proof_assert!` is semantically TRUE
under RustHorn/Creusot prophecy semantics, so no genuine refuting model
exists — a reported counterexample refutes the (incomplete) encoding, not
the program. For these tests only, a wire line showing clean function-level
results with proof_assert-only failures classifies as `unknown` (with the
table's justification as the reason) instead of `fail`, matching the LRA
spurious-SAT guard (#2674). This deliberately does not restore the
pre-hardening #2700 `pass` credit: the 2026-04-18/19 baselines passed
`closures/09_fnonce_resolve.rs` while the driver emitted four proof-assert
counterexamples, a false parity credit the wire-line hardening removed.
Entries are removed when the underlying encoding gap is fixed (the table is
consulted only while the proof-assert-only failure signature persists, so a
stale entry cannot mask a fixed test).

### should_fail lane

| Status | Meaning |
|--------|---------|
| pass | trust-wp correctly rejected the code (fail/error from trust-wp) |
| fail | trust-wp unexpectedly verified code that should have been rejected |
| skip | Test uses unsupported Creusot features |

### Skip Reasons

`skip_reason` values come from the harness classifier. They include unsupported
feature reasons and classification-only reasons used to keep parity metrics
actionable.

Unsupported feature reasons include (non-exhaustive), along with a few
harness-policy categories where the classifier is still stricter than the core
parser/verifier:
- `loop invariants` - `#[invariant(...)]` syntax not implemented
- `terminates` - `#[terminates]` attribute not implemented
- `trait specs` - trait contract specifications
- `closures` - Closure verification
- `type invariants` - `impl Invariant for ...` patterns not yet supported
- `prophetic logic` - **REMOVED** (#2683): `#[logic(prophetic)]` is now
  supported. The Resolve trait has `resolve_coherence`, the blanket impl was
  removed, and prophetic functions compile and verify natively
- `bitwise proofs` - `#[bitwise_proof]` not yet supported
- `snapshot module` - `snapshot::...` module patterns not yet supported
- `open functions` - the skip reason refers to Creusot's standalone `#[open]`
  attribute. trust-wp already supports open-body logic through
  `#[logic(open)]`, `#[logic(open(self))]`, and the accepted
  `open(crate)` / `open(super)` forms, which currently normalize to open
  behavior
- `impl blocks` - impl-level verification forms not yet supported
- `derive macros` - derive-related verification forms not yet supported
- ~~`dyn Trait`~~ - removed (#2685): trust-wp correctly rejects unsound dyn usage
- ~~`or-patterns`~~ - removed (#2685): rustc desugars or-patterns before MIR

Classification-only reasons include:
- `no contracts` - legacy reason that may still appear in older committed
  artifacts; the current classifier promotes clean no-contract crates to `pass`
- `no contracts verified` - contracts discovered, but no obligations verified

### Pass-Rate Denominators

Compatibility reporting uses two related pass-rate denominators:

- `raw pass rate = pass / total`
- `actionable pass rate = pass / (total - classification-only skips)`

For the actionable denominator, classification-only skips are skip reasons that
do not represent a verifier capability gap: currently `no contracts` and
`no contracts verified`. Feature skips such as `terminates` or `bitwise proofs`
stay in the actionable denominator because they are real missing-coverage
buckets, not measurement noise. Note: `prophetic logic` was removed as a skip
reason in #2683 -- prophetic tests are now executed and classified by output.

Example (values are illustrative — see the committed baseline artifact in
`tests/creusot_compat/results.json` or `tests/creusot_compat/baseline-*.json`
for the current numbers):

- `raw should_succeed rate = pass / total`
- `actionable should_succeed rate = pass / (total - classification-only skips)`
- `classification-only skips` = count of entries flagged only by the
  classifier (typically `no contracts verified`)

If you also want the broader executed/non-skip rate (`pass / (total - skip)`),
report it separately as an executed/effective metric rather than replacing the
actionable headline.

`pearlite!` tests are attempted and classified based on observed
verification/compile outcomes instead of pre-skip heuristics.

## Output Format

`results.json`:

```json
{
  "metadata": {
    "timestamp": "2026-02-07T23:00:00+00:00",
    "git_commit": "a1b4dad",
    "command": "tests/creusot_compat/harness.py --verbose",
    "is_partial": false,
    "lane": "should_succeed",
    "filter": null,
    "limit": null,
    "discovered_tests": 273,
    "executed_tests": 273,
    "lane_pair_freshness": {
      "current_lane": "should_succeed",
      "current_output": "tests/creusot_compat/results.json",
      "current_git_commit": "131a1c98",
      "current_age_commits": 24,
      "paired_lane": "should_fail",
      "paired_output": "tests/creusot_compat/results-should-fail.json",
      "paired_git_commit": "03da9d02",
      "paired_age_commits": 143,
      "max_age_gap_commits": 20,
      "age_gap_commits": 119,
      "evaluated_against_head": "131a1c98"
    },
    "baseline_freshness": {
      "max_age_commits": 50,
      "lanes": {
        "should_succeed": {
          "path": "tests/creusot_compat/results.json",
          "git_commit": "131a1c98",
          "age_commits": 24
        },
        "should_fail": {
          "path": "tests/creusot_compat/results-should-fail.json",
          "git_commit": "03da9d02",
          "age_commits": 143
        },
        "examples": {
          "path": "tests/creusot_compat/results-examples.json",
          "git_commit": "131a1c98",
          "age_commits": 24
        }
      },
      "evaluated_against_head": "131a1c98"
    }
  },
  "summary": {
    "total": 273,
    "pass": 15,
    "fail": 2,
    "skip": 200,
    "error": 56,
    "skip_reasons": {
      "loop invariants": 80,
      "no contracts": 60
    },
    "parse_failures": {
      "contract_clauses": 0,
      "assertion": 7,
      "ghost_block": 2,
      "logic_function_body": 4
    },
    "should_succeed": {
      "total": 273,
      "pass": 15,
      "fail": 2,
      "skip": 200,
      "error": 56
    }
  },
  "results": [
    {
      "name": "tests/should_succeed/100doors.rs",
      "status": "skip",
      "message": "...",
      "duration_ms": 5000,
      "skip_reason": "loop invariants"
    }
  ]
}
```

The `metadata` section allows consumers to distinguish canonical baselines
(`is_partial: false`) from exploratory runs, and to trace results back to
the exact commit and command that produced them.

The `summary.parse_failures` counters provide message-level tracking for parser
diagnostics (including contract clauses), independent of pass/fail/skip/error.

## Tracking Progress

As trust-wp implements more features, the pass rate should increase:

```bash
# Compare against baseline
diff -u baseline.json results.json | grep '"pass"'
```

For #352 parity updates, compare baselines by their pinned metadata commit
(`metadata.git_commit`) rather than against whatever `HEAD` is at comment time.
Use commit-anchored pairs such as:

```bash
jq -r '.metadata.git_commit' tests/creusot_compat/results.json
jq -r '.metadata.git_commit' tests/creusot_compat/results-should-fail.json
jq -r '.metadata.git_commit' tests/creusot_compat/results-examples.json
```

## Freshness Reporting Contract (#1012)

All parity-status comments on #352 must include a canonical freshness snapshot
to prevent conflicting freshness claims. The required template:

```
### Freshness
--check-baseline-freshness output:
  should_succeed: <fresh/stale/missing/invalid> at <git_commit> (<N> commits behind HEAD)
  should_fail: <fresh/stale/missing/invalid> at <git_commit> (<N> commits behind HEAD)
  examples: <fresh/stale/missing/invalid> at <git_commit> (<N> commits behind HEAD)
Timestamp: <UTC ISO 8601>
```

Run `python3 tests/creusot_compat/harness.py --check-baseline-freshness` to
generate the canonical freshness data. Do not manually claim "fresh" or "stale"
without running this command.

## Related Issues

- #352 - Creusot feature parity tracking
- #1012 - Freshness signaling contract
- L3 - Initial harness implementation
