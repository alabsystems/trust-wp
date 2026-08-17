#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Runner for the trust-wp adversarial negative corpus.

The Creusot ``should_fail`` lane is trust-wp's only automated false-accept
detector, and it is a REFERENCE corpus we must keep pristine (compat
accounting depends on it).  It therefore has blind spots that no local change
may close — most prominently, zero ``should_fail`` test exercises an
enum-embedded ``&mut`` (``Option<&mut T>``), the exact shape of the
adjudicated ``take_first_mut`` false accept.

This corpus is trust-wp-OWNED and adversarial by construction: every
``expect: reject`` case is a program whose contract is FALSE and which is
provable ONLY IF a specific, root-caused encoder/driver defect is present.
An ACCEPT here is a false accept, full stop.

Each case additionally has a near-identical CONTROL whose contract is TRUE,
so the suite also detects over-refusal (false rejects).

Usage:
    python3 tests/adversarial/run_adversarial.py [-v] [--filter PATTERN]
                                                 [--timeout SECONDS]
                                                 [--json OUT.json]

Exit codes:
    0  every case behaved as declared
    1  at least one adversarial case was ACCEPTED (a false accept), or a
       non-xfail control was rejected
    2  runner/setup failure
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

CASES_DIRNAME = "cases"

# The compat harness owns the fixture scaffolding (reviewed-lock derivation,
# toolchain pinning, stable wrapper bin dir, shared-target locking and cache
# invalidation).  This corpus reuses it verbatim rather than forking it; it
# does NOT reuse the Creusot lane discovery, classification tables, or
# baselines, and it never reads reference/creusot.
_HERE = Path(__file__).resolve().parent
_COMPAT_DIR = _HERE.parent / "creusot_compat"
sys.path.insert(0, str(_COMPAT_DIR))

import harness  # noqa: E402  (path setup must precede the import)
import harness_runner  # noqa: E402


# ---------------------------------------------------------------------------
# Case declarations
# ---------------------------------------------------------------------------
#
# Every case file carries a directive header:
#
#   //@ expect: reject          -- adversarial: a clean ACCEPT is a false accept
#   //@ expect: verify          -- control: must verify cleanly today
#   //@ xfail: <reason>         -- (controls only) known not to verify today
#   //@ mechanism: <text>
#   //@ fixed-by: <commit>
#   //@ accept-means: <text>    -- what a clean accept would prove is broken
#   //@ teeth: <text>           -- how the case was shown to have teeth
#   //@ timeout: <seconds>      -- optional per-case budget override

_DIRECTIVE_RE = re.compile(r"^\s*//@\s*([a-z-]+)\s*:\s*(.*?)\s*$")

_REQUIRED_DIRECTIVES = ("expect", "mechanism")
_VALID_EXPECT = ("reject", "verify")


@dataclass
class Case:
    path: Path
    name: str
    directives: dict[str, str] = field(default_factory=dict)

    @property
    def expect(self) -> str:
        return self.directives["expect"]

    @property
    def xfail(self) -> str | None:
        return self.directives.get("xfail")

    @property
    def timeout(self) -> int | None:
        raw = self.directives.get("timeout")
        return int(raw) if raw else None


def parse_directives(source: str) -> dict[str, str]:
    """Parse ``//@ key: value`` directives from a case file header."""
    directives: dict[str, str] = {}
    for line in source.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        match = _DIRECTIVE_RE.match(line)
        if match:
            directives[match.group(1)] = match.group(2)
            continue
        if stripped.startswith("//"):
            continue
        # Directives live in the header block only; stop at the first item of
        # real Rust so a `//@` inside the body cannot silently retune a case.
        break
    return directives


def load_cases(cases_dir: Path, filter_pattern: str | None) -> list[Case]:
    """Discover and validate every case in ``cases_dir``."""
    if not cases_dir.is_dir():
        raise RuntimeError(f"adversarial cases directory not found: {cases_dir}")

    pattern = re.compile(filter_pattern, re.IGNORECASE) if filter_pattern else None
    cases: list[Case] = []
    for path in sorted(cases_dir.rglob("*.rs")):
        directives = parse_directives(path.read_text(encoding="utf-8"))
        missing = [key for key in _REQUIRED_DIRECTIVES if key not in directives]
        if missing:
            raise RuntimeError(
                f"{path}: missing required directive(s): {', '.join(missing)}"
            )
        if directives["expect"] not in _VALID_EXPECT:
            raise RuntimeError(
                f"{path}: expect must be one of {_VALID_EXPECT}, "
                f"got {directives['expect']!r}"
            )
        if directives.get("xfail") and directives["expect"] != "verify":
            raise RuntimeError(
                f"{path}: xfail is only meaningful on `expect: verify` controls "
                "— an adversarial case may never be excused from rejecting"
            )
        case = Case(path=path, name=path.stem, directives=directives)
        if pattern and not pattern.search(case.name):
            continue
        cases.append(case)

    if not cases:
        raise RuntimeError(
            f"no adversarial cases matched (dir={cases_dir}, filter={filter_pattern!r})"
        )
    return cases


# ---------------------------------------------------------------------------
# Verdicts
# ---------------------------------------------------------------------------

# ACCEPTED is the only verdict that can be a false accept: it is the compat
# harness's own definition of a clean verification run (exit 0, at least one
# verified contract, no failed/unknown/dropped obligation).  Everything else
# is a rejection of some flavour, and for an adversarial case every flavour of
# rejection is a pass — a false contract that errors out is not proved.
ACCEPTED = "ACCEPTED"
FAILED = "failed"
UNKNOWN = "unknown"
ERROR = "error"
TIMEOUT = "timeout"


def classify(success: bool, output: str, exit_code: int | None) -> str:
    """Reduce a run to ACCEPTED or a rejection flavour."""
    if success:
        return ACCEPTED
    if "Timeout after" in output:
        return TIMEOUT
    counts = harness._last_verification_summary_counts(output)
    pa_counts = harness._last_proof_assert_summary_counts(output)
    failed = (counts[1] if counts else 0) + (pa_counts[1] if pa_counts else 0)
    errored = (counts[2] if counts else 0) + (pa_counts[2] if pa_counts else 0)
    if failed:
        return FAILED
    if errored:
        return UNKNOWN
    if exit_code == 0 and harness._has_verification_failures(output):
        # Verdict-bearing run with no clean accept and no counted obligation:
        # dropped obligations, counterexamples, or a bare `unknown (...)`.
        return UNKNOWN
    return ERROR


@dataclass
class Outcome:
    case: Case
    verdict: str
    duration_ms: int
    ok: bool
    note: str
    output: str


def evaluate(case: Case, verdict: str) -> tuple[bool, str]:
    """Return (ok, note) for a verdict against the case's declared expectation."""
    if case.expect == "reject":
        if verdict == ACCEPTED:
            return False, "FALSE ACCEPT — the defect this case targets is live"
        return True, f"rejected ({verdict})"
    # expect: verify
    if verdict == ACCEPTED:
        if case.xfail:
            return True, "XPASS — xfail control now verifies; retire the xfail"
        return True, "verified"
    if case.xfail:
        return True, f"xfail ({verdict}): {case.xfail}"
    return False, f"OVER-REFUSAL — control did not verify ({verdict})"


# ---------------------------------------------------------------------------
# Execution
# ---------------------------------------------------------------------------


def run_case(
    workspace: Path,
    case: Case,
    shared_target: Path,
    timeout_sec: int,
    verbose: bool,
) -> Outcome:
    temp_dir = Path(tempfile.mkdtemp(prefix="trust_wp_adversarial_"))
    try:
        success, output, duration_ms, exit_code = harness_runner._run_project_with_retry(
            harness._current_facade(),
            workspace,
            case.path,
            temp_dir,
            case.timeout or timeout_sec,
            shared_target,
            verbose,
        )
    finally:
        shutil.rmtree(temp_dir, ignore_errors=True)

    verdict = classify(success, output, exit_code)
    ok, note = evaluate(case, verdict)
    return Outcome(
        case=case,
        verdict=verdict,
        duration_ms=duration_ms,
        ok=ok,
        note=note,
        output=output,
    )


def print_summary(outcomes: list[Outcome]) -> int:
    adversarial = [o for o in outcomes if o.case.expect == "reject"]
    controls = [o for o in outcomes if o.case.expect == "verify"]

    accepted = [o for o in adversarial if o.verdict == ACCEPTED]
    rejected = [o for o in adversarial if o.verdict != ACCEPTED]
    verified_controls = [o for o in controls if o.verdict == ACCEPTED]
    xfail_controls = [o for o in controls if o.verdict != ACCEPTED and o.case.xfail]
    broken_controls = [o for o in controls if not o.ok]
    xpass_controls = [o for o in verified_controls if o.case.xfail]

    print()
    print("Summary (lane: adversarial):")
    print(f"  Total:    {len(adversarial)}")
    print(f"  Rejected: {len(rejected)}")
    print(f"  ACCEPTED: {len(accepted)} (false accepts)")
    print()
    print("  controls:")
    print(f"    Total:    {len(controls)}")
    print(f"    Verified: {len(verified_controls)}")
    print(f"    Xfail:    {len(xfail_controls)}")
    print(f"    Xpass:    {len(xpass_controls)}")
    print(f"    Broken:   {len(broken_controls)} (over-refusals)")

    if accepted:
        print()
        print("FALSE ACCEPTS — trust-wp proved a contract that is FALSE:")
        for outcome in accepted:
            print(f"  {outcome.case.name}")
            print(f"    mechanism:    {outcome.case.directives.get('mechanism', '?')}")
            print(f"    fixed-by:     {outcome.case.directives.get('fixed-by', '?')}")
            print(f"    accept-means: {outcome.case.directives.get('accept-means', '?')}")
    if broken_controls:
        print()
        print("OVER-REFUSALS — a TRUE contract stopped verifying:")
        for outcome in broken_controls:
            print(f"  {outcome.case.name}: {outcome.note}")
    if xpass_controls:
        print()
        print("XPASS — retire the xfail directive:")
        for outcome in xpass_controls:
            print(f"  {outcome.case.name}")

    return 1 if (accepted or broken_controls) else 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run the trust-wp adversarial negative corpus."
    )
    parser.add_argument("-v", "--verbose", action="store_true")
    parser.add_argument("--filter", help="regex over case names")
    parser.add_argument(
        "--timeout",
        type=int,
        default=int(os.environ.get("TRUST_WP_ADVERSARIAL_TIMEOUT", "120")),
        help="per-case budget in seconds (also the driver solver timeout)",
    )
    parser.add_argument("--json", help="write machine-readable results here")
    parser.add_argument(
        "--keep-output",
        action="store_true",
        help="print each case's full trust-wp output",
    )
    args = parser.parse_args()

    workspace = harness.find_workspace_root()
    cases = load_cases(_HERE / CASES_DIRNAME, args.filter)
    harness.ensure_harness_binaries(workspace, args.verbose)

    env_target = os.environ.get("TRUST_WP_HARNESS_TARGET_DIR")
    owns_target = env_target is None
    shared_target = (
        Path(env_target)
        if env_target
        else Path(tempfile.mkdtemp(prefix="trust_wp_adversarial_target_"))
    )
    shared_target.mkdir(parents=True, exist_ok=True)

    outcomes: list[Outcome] = []
    try:
        harness_runner._warmup_shared_target(
            harness._current_facade(),
            workspace,
            [case.path for case in cases],
            shared_target,
            args.verbose,
        )
        for index, case in enumerate(cases, start=1):
            label = f"[{index}/{len(cases)}] {case.name} (expect {case.expect})"
            print(f"{label} ... ", end="", flush=True)
            outcome = run_case(
                workspace, case, shared_target, args.timeout, args.verbose
            )
            outcomes.append(outcome)
            marker = "ok" if outcome.ok else "FAIL"
            print(f"{outcome.verdict} [{marker}] ({outcome.duration_ms}ms)")
            if not outcome.ok or args.keep_output:
                print(f"    {outcome.note}")
            if args.keep_output:
                print(outcome.output)
    finally:
        if owns_target:
            shutil.rmtree(shared_target, ignore_errors=True)

    exit_code = print_summary(outcomes)

    if args.json:
        Path(args.json).write_text(
            json.dumps(
                {
                    "results": [
                        {
                            "name": o.case.name,
                            "expect": o.case.expect,
                            "verdict": o.verdict,
                            "ok": o.ok,
                            "note": o.note,
                            "duration_ms": o.duration_ms,
                            "directives": o.case.directives,
                        }
                        for o in outcomes
                    ],
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )

    return exit_code


if __name__ == "__main__":
    try:
        sys.exit(main())
    except RuntimeError as error:
        print(f"adversarial runner error: {error}", file=sys.stderr)
        sys.exit(2)
