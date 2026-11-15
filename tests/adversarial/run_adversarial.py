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
                                                 [--jobs N]
                                                 [--changed-since REV]

Crediting an ``expect: reject`` case (teeth policy, wp-s47 v2)
-------------------------------------------------------------
A rejection is credited ONLY when trust-wp itself delivered it:

1. the verifier refuted the contract -- verdict ``failed`` / ``unknown`` /
   ``timeout`` -- AND the run carries a parseable ``TRUST_WP_RESULT`` wire
   line (the driver reached its verdict phase); or
2. trust-wp REFUSED the crate up front (verdict ``error``) AND the case
   declares ``//@ verdict: error`` plus ``//@ refused-with: <text>`` AND
   ``<text>`` occurs on one of trust-wp's own output lines
   (``trust-wp: ...`` / ``error: trust-wp: ...``), again with a wire line.

Everything else is TEETH LOST, never ok: a rustc/cargo compile error (no wire
line: the driver never ran its analysis), a run killed by the harness budget
without a wire line, an undeclared ``error`` verdict, or a driver panic / ICE
(``panics>0`` on the wire, ``panicked at``, ``internal compiler error``,
exit status 101) -- a crash is not a verdict. Before this policy ANY
rejection flavour was ok, so a fixture that stopped compiling (edition 2024:
``extern blocks must be unsafe``) silently kept its [ok].

Per-function credits in an ``expect: reject`` case
--------------------------------------------------
The process verdict is a whole-crate summary: one refuted function makes the run a
rejection while another verdict in the same crate stands on a claim that is false.
So a reject case also passes only when every positive verdict it carries is one it
DECLARES true: ``//@ also-verified:`` for a function's credit and
``//@ also-verified-assertion:`` for each ``proof_assert!`` reported verified. A
function credit beside an assertion of its own that did not prove is flagged even
when declared, whatever word reported the assertion unproved (see
``unproved_assertion_functions``).

Exit codes:
    0  every case behaved as declared
    1  at least one adversarial case was ACCEPTED (a false accept), or a
       non-xfail control was rejected
    2  runner/setup failure
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import queue
import re
import shutil
import subprocess
import sys
import tempfile
from collections import Counter
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
#   //@ xfail-verdict: <flavour> -- (xfail controls) the control's rejection
#                                  MUST be this flavour. A TRUE program an
#                                  xfail excuses from verifying is still never
#                                  excused into a refutation it has not got:
#                                  `unknown` here makes a `FAILED` a failure.
#   //@ mechanism: <text>
#   //@ fixed-by: <commit>
#   //@ accept-means: <text>    -- what a clean accept would prove is broken
#   //@ teeth: <text>           -- how the case was shown to have teeth
#   //@ timeout: <seconds>      -- optional per-case budget override
#   //@ verdict: <flavour>      -- (reject cases) the rejection MUST be this
#                                  flavour (failed/unknown/error/timeout)
#   //@ fn-failed: <name>       -- (reject cases) `trust-wp: <name> FAILED`
#                                  must be reported
#   //@ refused-with: <text>    -- (reject cases) one of trust-wp's OWN output
#                                  lines (`trust-wp: ...` / `error: trust-wp:
#                                  ...`) must contain <text> verbatim (a named
#                                  up-front refusal, so that an unrelated
#                                  error -- in particular a rustc compile
#                                  error -- cannot stand in). REQUIRED together
#                                  with `verdict: error`: an `error` verdict is
#                                  credited only as a named trust-wp refusal.
#   //@ also-verified: <names>  -- (reject cases) the comma-separated functions
#                                  this case EXPECTS to be reported
#                                  `trust-wp: <name> verified`, each spelled
#                                  exactly as that line prints it -- a trait
#                                  impl method is `<S as Inc>::inc`. Any other
#                                  function reported verified is a false accept
#                                  on that function. Absent means "none": a
#                                  reject case credits no verification by
#                                  default.
#   //@ also-verified-assertion: <names>
#                               -- (reject cases) the proof_asserts this case
#                                  EXPECTS to be reported `trust-wp: proof_assert
#                                  in <name> verified`, one entry per assertion:
#                                  <name> is the function the assertion sits in,
#                                  spelled as that line prints it, crate first
#                                  (`creusot_test::k`), and a function with two
#                                  proved assertions is named twice. The line
#                                  names the function, not the assertion, so the
#                                  count is what stops a second, false assertion
#                                  riding on the first one's declaration. An
#                                  assertion credit is its own claim about the
#                                  program, so it is declared apart from the
#                                  function's credit and neither declares the
#                                  other. Absent means "none".
#   //@ ay-not-unsat: <name>    -- (reject cases) ay must have been asked
#                                  about <name> (a TRUST_WP_DIAGNOSTIC line with
#                                  def_path=<name> exists) and must NOT have
#                                  answered unsat. A false contract that ay
#                                  proves unsat is a live encoding defect even
#                                  when a later certificate gate demotes it, so
#                                  that gate cannot mask a regression here.

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


# A repeated key continues a long value, as the README documents -- but only
# for the prose directives. A repeated key that STEERS the verdict is ambiguous
# (which value wins?), so it is refused rather than silently resolved: a case
# that retunes its own gate is exactly what the header block exists to prevent.
_SINGLE_VALUE_DIRECTIVES = frozenset(
    {
        "expect",
        "timeout",
        "verdict",
        "xfail-verdict",
        "fn-failed",
        "refused-with",
        "ay-not-unsat",
        "also-verified",
        "xfail-verdict",
        "also-verified-assertion",
    }
)


def parse_directives(source: str) -> dict[str, str]:
    """Parse ``//@ key: value`` directives from a case file header."""
    directives: dict[str, str] = {}
    for line in source.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        match = _DIRECTIVE_RE.match(line)
        if match:
            key, value = match.group(1), match.group(2)
            if key in directives:
                if key in _SINGLE_VALUE_DIRECTIVES:
                    raise RuntimeError(
                        f"directive {key!r} is repeated; it steers the verdict, "
                        f"so it must appear once ({directives[key]!r} vs {value!r})"
                    )
                directives[key] = f"{directives[key]} {value}".strip()
            else:
                directives[key] = value
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
        teeth = [
            k
            for k in (
                "verdict",
                "fn-failed",
                "ay-not-unsat",
                "refused-with",
                "also-verified",
                "also-verified-assertion",
            )
            if k in directives
        ]
        if teeth and directives["expect"] != "reject":
            raise RuntimeError(f"{path}: {', '.join(teeth)} only apply to `expect: reject`")
        declared: dict[str, list[str]] = {}
        for key in ("also-verified", "also-verified-assertion"):
            try:
                declared[key] = parse_def_path_list(directives.get(key, ""))
            except ValueError as error:
                raise RuntimeError(f"{path}: {key}: {error}") from error
        unqualified = [
            name for name in declared["also-verified-assertion"]
            if not _CRATE_PREFIX_RE.match(name)
        ]
        if unqualified:
            raise RuntimeError(
                f"{path}: also-verified-assertion: {', '.join(unqualified)} can never match: "
                "an assertion line names its function crate first (`creusot_test::k`)"
            )
        if directives.get("verdict") == ERROR and not directives.get("refused-with"):
            raise RuntimeError(
                f"{path}: `verdict: error` requires `refused-with:` naming trust-wp's own "
                "refusal text -- an unnamed error could be a rustc compile error"
            )
        if directives.get("xfail") and directives["expect"] != "verify":
            raise RuntimeError(
                f"{path}: xfail is only meaningful on `expect: verify` controls "
                "— an adversarial case may never be excused from rejecting"
            )
        if "xfail-verdict" in directives:
            if not directives.get("xfail"):
                raise RuntimeError(f"{path}: xfail-verdict pins an `xfail:` control's rejection")
            if directives["xfail-verdict"] not in (FAILED, UNKNOWN, ERROR, TIMEOUT):
                raise RuntimeError(
                    f"{path}: xfail-verdict must be one of failed/unknown/error/timeout, "
                    f"got {directives['xfail-verdict']!r}"
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
# is a rejection of some flavour -- but a rejection only earns credit for an
# adversarial case when trust-wp itself delivered it (see the module header
# and `reject_credit_violations`): a false contract that merely fails to
# COMPILE was never examined.
ACCEPTED = "ACCEPTED"
FAILED = "failed"
UNKNOWN = "unknown"
ERROR = "error"
TIMEOUT = "timeout"


def wire_telemetry(output: str):
    """The run's TRUST_WP_RESULT telemetry, or None (absent or unparseable)."""
    return harness_runner._extract_telemetry(output)


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
    telemetry = wire_telemetry(output)
    if telemetry is not None:
        # The driver prints no `proof_assert: N verified, N failed, N errors`
        # summary for inconclusive proof_asserts, so read its own counters: a
        # proof_assert the verifier could not discharge is a verifier verdict,
        # not an up-front refusal.  (Function-level `errors` is NOT read here:
        # up-front refusals such as the reserved-root backstop count there.)
        if telemetry.proof_assert_failed:
            return FAILED
        if telemetry.proof_assert_inconclusive or telemetry.proof_assert_errors:
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


_DIAGNOSTIC_RE = re.compile(r"^TRUST_WP_DIAGNOSTIC:v1 (.*)$", re.MULTILINE)


def diagnostic_ay_results(output: str, def_path: str) -> list[str]:
    """``ay_result`` of every TRUST_WP_DIAGNOSTIC line about ``def_path``."""
    results: list[str] = []
    for match in _DIAGNOSTIC_RE.finditer(output):
        fields = dict(
            item.split("=", 1) for item in match.group(1).split() if "=" in item
        )
        if fields.get("def_path") == def_path:
            results.append(fields.get("ay_result", "<missing>"))
    return results


# trust-wp's own human output: `trust-wp: ...`, `trust-wp: error: ...`, and
# driver diagnostics rendered through rustc's emitter as `error: trust-wp: ...`.
_TRUST_WP_LINE_RE = re.compile(r"^\s*(?:(?:error|warning): )?trust-wp: ")
# A rustc/cargo error headline that is not trust-wp's (cargo's trailing
# `could not compile` / rustc's `aborting due to` accompany ANY error).
_FOREIGN_ERROR_RE = re.compile(
    r"^\s*error(?:\[E\d+\])?: (?!trust-wp: |could not compile|aborting due to)"
)
_CRASH_RE = re.compile(
    r"panicked at|internal compiler error|exit status: 101|RUST_BACKTRACE=1", re.IGNORECASE
)


def trust_wp_lines(output: str) -> list[str]:
    """trust-wp's own output lines (never rustc's or cargo's)."""
    return [line.strip() for line in output.splitlines() if _TRUST_WP_LINE_RE.match(line)]


# The name on a verdict line is `tcx.def_path_str`: `inc`, `m::inc`, `S::new`, and for a
# trait impl `<S as Inc>::inc`, `m::<impl Tr for S>::f`, `<(u8, u16) as Tr>::m`,
# `<fn(u8) -> u8 as Tr>::m`. Its spaces and commas sit only inside brackets, so the name
# ends at the first space outside them. A name read as "everything up to a space" stopped
# at `<S`, and every trait impl's credit was invisible to both credit checks.
_OPENERS = "<(["
_CLOSERS = ">)]"


def _top_level_positions(text: str):
    """Indices of the characters of `text` outside every bracket, then `len(text)`.

    The final `len(text)` comes only when the brackets balance; a closer with no opener
    ends the scan there. The `->` of a fn-pointer type closes nothing.
    """
    depth = 0
    i = 0
    while i < len(text):
        if depth and text.startswith("->", i):
            i += 2
            continue
        ch = text[i]
        if ch in _OPENERS:
            depth += 1
        elif ch in _CLOSERS:
            if not depth:
                return
            depth -= 1
        elif not depth:
            yield i
        i += 1
    if not depth:
        yield len(text)


def _leading_def_path(text: str) -> tuple[str, str] | None:
    """Split `text` into (def path, rest) at the first space outside brackets.

    None when `text` does not open with a def path: it starts with a space, or a
    bracket in the name does not balance before the line ends.
    """
    for i in _top_level_positions(text):
        if i == len(text) or text[i].isspace():
            return (text[:i], text[i:]) if i else None
    return None


def parse_def_path_list(value: str) -> list[str]:
    """The comma-separated def paths of an `also-verified:` value.

    Only a comma outside brackets separates two names (`<(u8, u16) as Tr>::m` is one),
    and a space outside brackets is refused: before names could hold spaces a space
    separated them too, so `a b` is a missing comma, never one function.
    """
    names: list[str] = []
    start = 0
    ended = False
    for i in _top_level_positions(value):
        if i == len(value) or value[i] == ",":
            names.append(value[start:i].strip())
            start = i + 1
            ended = i == len(value)
    if not ended:
        raise ValueError(f"unbalanced brackets in {value!r}")
    for name in names:
        if name and _leading_def_path(name) != (name, ""):
            raise ValueError(
                f"{name!r} is not one def path: separate names with commas "
                "(a space may appear only inside brackets, as in `<S as Tr>::m`)"
            )
    return [name for name in names if name]


_TRUST_WP_BODY_RE = re.compile(r"^trust-wp: (.*)$", re.MULTILINE)


def _named_lines(output: str, head: str = ""):
    """(def path, rest) for every `trust-wp: <head><def path><rest>` line, in order."""
    for match in _TRUST_WP_BODY_RE.finditer(output):
        body = match.group(1)
        if body.startswith(head):
            split = _leading_def_path(body[len(head):])
            if split is not None:
                yield split


def _names_where(output: str, rest_re: re.Pattern[str], head: str = "") -> list[str]:
    seen: dict[str, None] = {}
    for name, rest in _named_lines(output, head):
        if rest_re.match(rest):
            seen.setdefault(name, None)
    return list(seen)


# A positive verdict on the name before it: `verified ✓` or `verified*`, whatever
# follows. The run summary (`3 verified, 1 failed`) has no tick after `verified`, and
# the refinement, loop-progress and `proof_assert in X` lines put a word between the
# name and `verified`, so none of them reads as a credit here. The lane spellings DO
# read as one: a lane report says nothing about the function's CONTRACT (see
# `_LANE_ONLY`), but it is still a `verified` line on the function, and no such line
# may stand beside an assertion of the function's own that was not proved.
_TICK = r" verified(?:\*|\s*\u2713)"
_ANY_CREDIT_RE = re.compile(_TICK)

# A CONTRACT credit, not a lane report. `verified ✓ (termination)` and
# `verified ✓ (loop invariant)` name the lane that passed and make no claim about the
# function's contract, which is why a function can carry one of those and still be
# refuted by its own obligations in the same run. `verified*` IS a contract credit --
# it says the proof leans on an unverified axiom, which is the credit at its most
# dangerous, never at its least.
_LANE_ONLY = r"(?! \((?:termination|loop invariant))"
_VERIFIED_FN_RE = re.compile(_TICK + _LANE_ONLY)


# A credit the driver took back at the end of the run. The `verified` line was printed
# when the function finished and cannot be unprinted, so this line is the only record
# that the credit no longer stands.
_WITHDRAWN_FN_RE = re.compile(r" error: verdict withdrawn\b")


def withdrawn_functions(output: str) -> list[str]:
    """Every function whose credit trust-wp withdrew, in output order."""
    return _names_where(output, _WITHDRAWN_FN_RE)


def verified_functions(output: str) -> list[str]:
    """Every function trust-wp reported as verified and did not withdraw, in output order.

    Covers the decorated spellings too (`verified*` for a run resting on an
    unverified axiom, and the vacuous-`requires(false)` note), because a credit
    is a credit whatever it is qualified with. A withdrawn credit is not one: the
    run's summary no longer counts it, and neither does this.
    """
    withdrawn = set(withdrawn_functions(output))
    return [name for name in _names_where(output, _VERIFIED_FN_RE) if name not in withdrawn]


# ---------------------------------------------------------------------------
# Assertion outcomes
# ---------------------------------------------------------------------------
#
# A `proof_assert!` has a verdict line of its own, `proof_assert in <crate>::<def path>
# <outcome>`, and it is PROVED on exactly two spellings of that line: `verified ✓`, and
# `verified ✓ (vacuous: explicit #[requires(false)])` in a function its author made
# uncallable. Every other outcome leaves it unproved, whatever the word: `FAILED ✗`,
# `unknown (..)`, `error: ..` (an encoding error or a refused field binding),
# `assumed (..) — counted as error`, `inconclusive (..) — function has no contracts`,
# `evidence gap (..)` (a certificate that did not replay) and `has no expression text`.
# So does a spelling this list has never met: reading an unfamiliar word as a proof is
# how a credit escapes, reading it as no proof costs one look.
_ASSERTION_HEAD = "proof_assert in "
_ASSERTION_PROVED_RE = re.compile(
    r" verified \u2713(?: \(vacuous: explicit #\[requires\(false\)\]\))?\s*$"
)
# `#[trusted] proof_assert!` is an assumption its author chose, not a goal: the driver
# skips it by design and the verdict of its function does not wait on it.
_ASSERTION_NOT_A_GOAL_RE = re.compile(
    r" (?:trusted \(skipped\)|proved, not credited: the function's postcondition is not proved)\s*$"
)
# The same outcome without the `proof_assert in` head. A snapshot the driver could not
# build is `error: proof_assert in <crate>::<path> missing MIR location`; the rest name
# the function by its plain def path, as its credit line does: the crate budget ran out
# (`proof_assert skipped (..)`), the assertion pass panicked, or the function's own
# verdict says an assertion of its own did not prove.
_SNAPSHOT_ERROR_HEAD = "error: proof_assert in "
_FN_ASSERTION_NOT_PROVED_RE = re.compile(
    r" (?:proof_assert skipped \("
    r"|(?:ay solver panic|panicked) during (?:standalone )?proof_assert: "
    r"|FAILED \u2717 \(proof_assert\)"
    r"|unknown \(proof_assert not proved\)"
    r"|error: verdict withdrawn - its own proof_assert was not proved)"
)
# An assertion refused before the line could name its function: the text did not
# parse, or it is not a `bool`. Whose verdict it withholds cannot be read off the line.
# A logic body refused because one of its own assertions did not parse names its
# function after "for", not at the head of the line.
_LOGIC_BODY_ASSERTION_REFUSED_RE = re.compile(
    r"^trust-wp: error: logic function body for (\S+) parsed without one of its proof_assert",
    re.MULTILINE,
)
_UNNAMED_ASSERTION_NOT_PROVED_RE = re.compile(
    r"(?:error: failed to parse proof_assert '"
    r"|frontend diagnostic: mismatched types in proof_assert ')"
)
_CRATE_PREFIX_RE = re.compile(r"^\w+::")


def _assertion_line(rest: str) -> tuple[str, str] | None:
    """(function path, outcome) of what follows the name `proof_assert`, or None."""
    return _leading_def_path(rest[len(" in "):]) if rest.startswith(" in ") else None


def assertion_credits(output: str) -> list[str]:
    """The function of every PROVED `proof_assert in <path>` line: one entry per line.

    A function with two proved assertions appears twice. The line names the function
    and not the assertion, so the count is the only thing that tells a second
    assertion's credit from the first's.
    """
    return [
        path for path, rest in _named_lines(output, _ASSERTION_HEAD)
        if _ASSERTION_PROVED_RE.match(rest)
    ]


# A trait-contract withdrawal takes back every credit its item banked, the item's
# proof_assert credits among them (D-94); its blame text is
# `trait_credit::render_withdrawal`. The own-assertion withdrawal takes back only the
# function's credit, so it is not read here.
_TRAIT_WITHDRAWN_FN_RE = re.compile(
    r" error: verdict withdrawn - (?:through |it assumed |it reaches )"
)


def standing_assertion_credits(output: str) -> list[str]:
    """`assertion_credits` less those of a function a trait withdrawal took back.

    The withdrawal line names the function by `def_path_str`, without the crate the
    assertion line puts in front, so both spellings are matched. The driver counts
    what it took back and this reads it by name; `reject_teeth_violations` holds the
    two to the same number, so a misread withdrawal cannot hide a standing credit.
    """
    withdrawn = set(_names_where(output, _TRAIT_WITHDRAWN_FN_RE))
    return [
        path for path in assertion_credits(output)
        if path not in withdrawn and _CRATE_PREFIX_RE.sub("", path) not in withdrawn
    ]


def unproved_assertion_functions(output: str) -> set[str]:
    """Every function with an assertion of its own that the run reported unproved.

    An assertion line prints the crate in front of `def_path_str`, so its path is
    recorded both as printed and with that one leading segment removed.
    """
    unproved: set[str] = set()
    for path, rest in _named_lines(output, _ASSERTION_HEAD):
        if not (_ASSERTION_PROVED_RE.match(rest) or _ASSERTION_NOT_A_GOAL_RE.match(rest)):
            unproved |= {path, _CRATE_PREFIX_RE.sub("", path)}
    for path, _rest in _named_lines(output, _SNAPSHOT_ERROR_HEAD):
        unproved |= {path, _CRATE_PREFIX_RE.sub("", path)}
    unproved.update(_names_where(output, _FN_ASSERTION_NOT_PROVED_RE))
    for path in _LOGIC_BODY_ASSERTION_REFUSED_RE.findall(output):
        unproved |= {path, _CRATE_PREFIX_RE.sub("", path)}
    return unproved


def unnamed_unproved_assertion_lines(output: str) -> list[str]:
    """Unproved-assertion lines that name no function."""
    return [
        match.group(1).strip()
        for match in _TRUST_WP_BODY_RE.finditer(output)
        if _UNNAMED_ASSERTION_NOT_PROVED_RE.match(match.group(1))
    ]


# The line shapes that carry a tick and are not a verdict on the name that opens them.
# Anything else with a tick that is not a credit is a spelling this gate does not know,
# and it is reported rather than skipped: an unread credit is how impl methods escaped.
def _is_known_non_credit(name: str, rest: str) -> bool:
    if name.isdigit():
        return rest.startswith(" verified, ")  # the run summary
    if name == "proof_assert":
        # A credit on the ASSERTION, read by `assertion_credits` -- but only in a
        # spelling that reader knows, or its credit would be read by nobody.
        line = _assertion_line(rest)
        return line is not None and bool(_ASSERTION_PROVED_RE.match(line[1]))
    return rest.startswith(
        (" refinement verified ", " loop invariant", " loop induction verified ")
    )


def unattributed_credit_lines(output: str) -> list[str]:
    """`trust-wp:` lines with a tick that are neither a credit nor a known non-credit."""
    lines: list[str] = []
    for match in _TRUST_WP_BODY_RE.finditer(output):
        body = match.group(1)
        if not re.search(_TICK, body):
            continue
        split = _leading_def_path(body)
        if split is None:
            lines.append(body.strip())
            continue
        name, rest = split
        if not _ANY_CREDIT_RE.match(rest) and not _is_known_non_credit(name, rest):
            lines.append(body.strip())
    return lines


def contradicted_credits(output: str) -> list[str]:
    """Functions credited `verified` whose own `proof_assert!` was not proved.

    A `proof_assert!` is a goal of the function it sits in -- Creusot puts it in that
    function's VC -- so a function with an assertion the run did not prove is not
    verified, whatever its (often empty) contract says, and whichever lane printed the
    credit: the loop-invariant and termination lanes own a function's verdict exactly
    as the function-level VC does. Such a credit is flagged even when a case declares
    the function: a declaration says which credits are TRUE, and this one is not.

    The credit is matched to the assertion by the whole qualified name, not its last
    segment: `inc` and `<T as Inc>::inc` are other functions. A logic function's credit
    line prints the crate (`creusot_test::one verified ✓`) as its assertion line does,
    which is why the assertion path is kept as printed too.
    """
    unproved = unproved_assertion_functions(output)
    return [name for name in _names_where(output, _ANY_CREDIT_RE) if name in unproved]


def foreign_error_lines(output: str) -> list[str]:
    """rustc/cargo error headlines that trust-wp did not emit."""
    return [line.strip() for line in output.splitlines() if _FOREIGN_ERROR_RE.match(line)]


def reject_credit_violations(
    case: Case, verdict: str, output: str, exit_code: int | None = None
) -> list[str]:
    """Why a (non-ACCEPTED) rejection is NOT trust-wp's own verdict, if it is not.

    Empty list = the rejection was delivered by trust-wp and may be credited.
    """
    problems: list[str] = []
    telemetry = wire_telemetry(output)
    crash = _CRASH_RE.search(output)
    if crash or exit_code == 101 or (telemetry is not None and telemetry.panics):
        evidence = crash.group(0) if crash else (
            "exit code 101" if exit_code == 101 else f"panics={telemetry.panics}"
        )
        problems.append(f"CRASH ({evidence}) — a driver panic is not a verdict")
    if telemetry is None:
        foreign = foreign_error_lines(output)
        why = f"; first foreign error: {foreign[0][:160]!r}" if foreign else ""
        problems.append(
            "no TRUST_WP_RESULT line — trust-wp delivered no verdict "
            f"(compile error, killed run or missing driver){why}"
        )
    if verdict == ERROR and not (
        case.directives.get("verdict") == ERROR and case.directives.get("refused-with")
    ):
        foreign = foreign_error_lines(output)
        why = f" (first foreign error: {foreign[0][:160]!r})" if foreign else ""
        problems.append(
            "verdict 'error' is credited only as a named trust-wp refusal "
            "(`//@ verdict: error` + `//@ refused-with:`)" + why
        )
    return problems


def reject_teeth_violations(case: Case, verdict: str, output: str) -> list[str]:
    """Violations of a reject case's optional teeth directives."""
    problems: list[str] = []
    wanted = case.directives.get("verdict")
    if wanted and verdict != wanted:
        problems.append(f"verdict {verdict!r}, required {wanted!r}")
    fn_failed = case.directives.get("fn-failed")
    if fn_failed and not re.search(
        rf"^trust-wp: {re.escape(fn_failed)} FAILED", output, re.MULTILINE
    ):
        problems.append(f"`trust-wp: {fn_failed} FAILED` not reported")
    refused_with = case.directives.get("refused-with")
    if refused_with and not any(refused_with in line for line in trust_wp_lines(output)):
        problems.append(
            f"refusal {refused_with!r} not reported by trust-wp itself "
            "(rustc/cargo output does not count)"
        )
    # The process-level verdict is a whole-crate summary: one function FAILING is
    # enough to make the run a rejection, so a SECOND function in the same crate can
    # be credited `verified` on a contract that is false and the case still passes.
    # 477 of the reject corpus carried no per-function teeth at all when this was
    # added. A reject case therefore credits no verification unless it says which.
    declared = set(parse_def_path_list(case.directives.get("also-verified", "")))
    contradicted = contradicted_credits(output)
    if contradicted:
        problems.append(
            "credited `verified` while its own proof_assert is not proved: "
            + ", ".join(contradicted)
        )
    undeclared = [
        n for n in verified_functions(output) if n not in declared and n not in contradicted
    ]
    if undeclared:
        problems.append(
            "verified on a case whose contract is false, and not declared by "
            f"`//@ also-verified:`: {', '.join(undeclared)}"
        )
    unnamed = unnamed_unproved_assertion_lines(output)
    credited = _names_where(output, _ANY_CREDIT_RE)
    if unnamed and credited:
        # The driver withholds the credit of the function this assertion sits in; the
        # gate cannot tell which one that is, so it cannot clear any of them.
        problems.append(
            f"a proof_assert went unproved on a line that names no function "
            f"({unnamed[0][:120]!r}), so no credit beside it can be shown uncontradicted: "
            + ", ".join(credited)
        )
    # An assertion credit is a claim about the program at one point, and a reject case
    # holds a false claim somewhere: the case says which of its assertions are TRUE.
    standing = standing_assertion_credits(output)
    telemetry = wire_telemetry(output)
    if telemetry is not None and len(standing) != telemetry.proof_assert_verified:
        problems.append(
            f"the driver counts {telemetry.proof_assert_verified} proof_assert credit(s) "
            f"standing and this gate reads {len(standing)}: a credit line it cannot read, "
            "or a withdrawal it misread"
        )
    declared_assertions = Counter(
        parse_def_path_list(case.directives.get("also-verified-assertion", ""))
    )
    excess = [
        f"{path} ({count} verified, {declared_assertions[path]} declared)"
        for path, count in Counter(standing).items()
        if count > declared_assertions[path]
    ]
    if excess:
        problems.append(
            "proof_assert verified on a case whose contract is false, and not declared by "
            f"`//@ also-verified-assertion:`: {', '.join(excess)}"
        )
    unattributed = unattributed_credit_lines(output)
    if unattributed:
        problems.append(
            "a `verified` line this gate cannot attribute to a function (teach "
            f"`_is_known_non_credit` or the def-path reader): {' | '.join(unattributed)}"
        )

    not_unsat = case.directives.get("ay-not-unsat")
    if not_unsat:
        ay_results = diagnostic_ay_results(output, not_unsat)
        if not ay_results:
            problems.append(f"no TRUST_WP_DIAGNOSTIC line for {not_unsat} (never reached ay)")
        elif "unsat" in ay_results:
            problems.append(
                f"ay answered unsat on the FALSE contract of {not_unsat} ({ay_results})"
            )
    return problems


def evaluate(
    case: Case, verdict: str, output: str = "", exit_code: int | None = None
) -> tuple[bool, str]:
    """Return (ok, note) for a verdict against the case's declared expectation."""
    if case.expect == "reject":
        if verdict == ACCEPTED:
            return False, "FALSE ACCEPT — the defect this case targets is live"
        problems = reject_credit_violations(case, verdict, output, exit_code)
        problems += reject_teeth_violations(case, verdict, output)
        if problems:
            return False, "TEETH LOST — " + "; ".join(problems)
        return True, f"rejected ({verdict})"
    # expect: verify
    if verdict == ACCEPTED:
        if case.xfail:
            return True, "XPASS — xfail control now verifies; retire the xfail"
        return True, "verified"
    if case.xfail:
        pinned = case.directives.get("xfail-verdict")
        if pinned and verdict != pinned:
            return False, (
                f"OVER-REFUSAL — xfail control rejected as {verdict!r}, "
                f"declared `xfail-verdict: {pinned}`"
            )
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
    ok, note = evaluate(case, verdict, output, exit_code)
    return Outcome(
        case=case,
        verdict=verdict,
        duration_ms=duration_ms,
        ok=ok,
        note=note,
        output=output,
    )


# ---------------------------------------------------------------------------
# Parallel execution
# ---------------------------------------------------------------------------
#
# Every case compiles as the SAME crate (`creusot_test` v0.1.0) and the compat
# harness deletes that crate's fingerprints out of the target dir before each
# run, so two cases sharing one target dir would delete each other's artifacts
# mid-compile.  That is why `_run_project_with_retry` holds an exclusive
# advisory lock on the target dir for the whole run: a shared target dir is not
# a hot cache under concurrency, it is a mutex.  Concurrency therefore has to
# come from giving each WORKER its own target dir, cloned from the warm seed so
# the expensive dependency stack is still compiled exactly once.  Everything
# else a case touches (its synthesized project, its temp dir) is already
# per-case, and the two module-level caches the harness keeps (the stable
# harness bin dir, the derived child lockfile) are populated by warmup before
# any worker starts and read-only afterwards.


def default_jobs() -> int:
    """Concurrency that leaves the box responsive and the solver un-starved.

    Each case is a cargo build plus a driver+solver run, so workers are mostly
    CPU-bound.  Headroom is not politeness: a case whose solver sits near its
    budget can flip verdict when the box is saturated, and a verdict that
    depends on load is worthless as a false-accept detector.
    """
    cpus = os.cpu_count() or 4
    return max(1, min(8, cpus - 6))


def clone_target_dir(seed: Path, dest: Path) -> None:
    """Copy the warm target dir, preferring an APFS clone (near-free, CoW).

    Each fallback starts from a clean ``dest``: a half-written directory would
    make the next ``cp`` copy the tree INTO it instead of onto it, and a worker
    would then compile against a target dir that is missing its warm deps.

    The seed is resolved through symlinks first. A target dir is routinely a
    ``<name> -> <name>.noindex`` symlink, and ``cp -R`` copies the LINK, which
    then dangles at the destination because its target is relative. The clone
    is verified for the same reason: a dangling symlink at ``dest`` is not an
    error for ``cp``, but every worker handed one dies on its first case, and
    a runner that dies mid-suite reports no verdicts at all.
    """
    seed = Path(os.path.realpath(seed))
    if not seed.is_dir():
        raise RuntimeError(f"seed target dir is not a directory: {seed}")
    for argv in (["cp", "-Rc"], ["cp", "-R"]):
        shutil.rmtree(dest, ignore_errors=True)
        if dest.is_symlink():
            dest.unlink()
        result = subprocess.run(
            [*argv, str(seed), str(dest)], capture_output=True, text=True
        )
        if result.returncode == 0 and dest.is_dir() and not dest.is_symlink():
            return
    shutil.rmtree(dest, ignore_errors=True)
    if dest.is_symlink():
        dest.unlink()
    shutil.copytree(seed, dest, symlinks=False)
    if not dest.is_dir():
        raise RuntimeError(f"failed to clone worker target dir at {dest}")


def run_cases_parallel(
    workspace: Path,
    cases: list[Case],
    seed_target: Path,
    timeout_sec: int,
    verbose: bool,
    keep_output: bool,
    jobs: int,
) -> list[Outcome]:
    """Run every case, printing results in `cases` order whatever finishes first.

    The printed order is the case order, not the completion order, so a log
    from a parallel run still diffs against a log from a sequential one.
    """
    # No point cloning a target dir no case will ever be scheduled onto.
    jobs = max(1, min(jobs, len(cases)))
    worker_targets: list[Path] = []
    clones_root: Path | None = None
    if jobs > 1:
        clones_root = Path(tempfile.mkdtemp(prefix="trust_wp_adversarial_workers_"))
        for index in range(jobs):
            dest = clones_root / f"w{index}"
            clone_target_dir(seed_target, dest)
            worker_targets.append(dest)
    else:
        worker_targets.append(seed_target)

    available: queue.Queue[Path] = queue.Queue()
    for target in worker_targets:
        available.put(target)

    def task(case: Case) -> Outcome:
        target = available.get()
        try:
            return run_case(workspace, case, target, timeout_sec, verbose)
        finally:
            available.put(target)

    outcomes: list[Outcome] = []
    try:
        pool = concurrent.futures.ThreadPoolExecutor(max_workers=jobs)
        futures: list[concurrent.futures.Future[Outcome]] = []
        try:
            futures = [pool.submit(task, case) for case in cases]
            for index, (case, future) in enumerate(zip(cases, futures), start=1):
                outcome = future.result()
                outcomes.append(outcome)
                marker = "ok" if outcome.ok else "FAIL"
                print(
                    f"[{index}/{len(cases)}] {case.name} (expect {case.expect}) ... "
                    f"{outcome.verdict} [{marker}] ({outcome.duration_ms}ms)",
                    flush=True,
                )
                if not outcome.ok or keep_output:
                    print(f"    {outcome.note}")
                if keep_output:
                    print(outcome.output)
        except BaseException:
            for future in futures:
                future.cancel()
            raise
        finally:
            pool.shutdown(wait=True)
    finally:
        if clones_root is not None:
            shutil.rmtree(clones_root, ignore_errors=True)
    return outcomes


# ---------------------------------------------------------------------------
# Partial selection (iteration only)
# ---------------------------------------------------------------------------


def changed_case_names(cases_dir: Path, rev: str) -> set[str]:
    """Stems of case files added or modified since ``rev``, including untracked."""
    names: set[str] = set()
    for argv in (
        ["git", "diff", "--name-only", rev, "--", str(cases_dir)],
        ["git", "ls-files", "--others", "--exclude-standard", "--", str(cases_dir)],
    ):
        result = subprocess.run(argv, cwd=cases_dir, capture_output=True, text=True)
        if result.returncode != 0:
            raise RuntimeError(
                f"--changed-since {rev!r}: {' '.join(argv)} failed: "
                f"{(result.stderr or '').strip()}"
            )
        for line in result.stdout.splitlines():
            path = Path(line.strip())
            if path.suffix == ".rs":
                names.add(path.stem)
    return names


def print_summary(outcomes: list[Outcome]) -> int:
    adversarial = [o for o in outcomes if o.case.expect == "reject"]
    controls = [o for o in outcomes if o.case.expect == "verify"]

    accepted = [o for o in adversarial if o.verdict == ACCEPTED]
    toothless = [o for o in adversarial if o.verdict != ACCEPTED and not o.ok]
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
    print(f"  Teeth lost: {len(toothless)}")
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
    if toothless:
        print()
        print("TEETH LOST — rejected, but not for the declared reason:")
        for outcome in toothless:
            print(f"  {outcome.case.name}: {outcome.note}")
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

    return 1 if (accepted or toothless or broken_controls) else 0


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
    parser.add_argument(
        "--jobs",
        "-j",
        type=int,
        default=int(os.environ.get("TRUST_WP_ADVERSARIAL_JOBS", "0")) or default_jobs(),
        help="cases to run concurrently, each with its own cloned target dir "
        f"(default {default_jobs()} here)",
    )
    parser.add_argument(
        "--cases-dir",
        metavar="DIR",
        help="PROBE RUN, for iteration only: read cases from DIR instead of the "
        "owned corpus. A run over any other directory is never the gate.",
    )
    parser.add_argument(
        "--changed-since",
        metavar="REV",
        help="PARTIAL RUN, for iteration only: run only cases added or modified "
        "since REV (plus untracked ones). Never a gate.",
    )
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")

    workspace = harness.find_workspace_root()
    gate_cases_dir = _HERE / CASES_DIRNAME
    cases_dir = Path(args.cases_dir).resolve() if args.cases_dir else gate_cases_dir
    if cases_dir != gate_cases_dir:
        # A probe corpus answers a question about one mechanism; only the owned
        # corpus carries the teeth accounting the exit code is credited against.
        banner = (
            f"PROBE RUN — cases from {cases_dir}, NOT the owned corpus. "
            "This is not the adversarial gate."
        )
        for stream in (sys.stdout, sys.stderr):
            print("!" * len(banner), file=stream)
            print(banner, file=stream)
            print("!" * len(banner), file=stream, flush=True)
    cases = load_cases(cases_dir, args.filter)
    total_cases = len(cases)
    if args.changed_since:
        changed = changed_case_names(cases_dir, args.changed_since)
        cases = [case for case in cases if case.name in changed]
        banner = (
            f"PARTIAL RUN — only {len(cases)} of {total_cases} cases "
            f"(changed since {args.changed_since}). This is NOT the adversarial "
            "gate; a green partial run certifies nothing."
        )
        for stream in (sys.stdout, sys.stderr):
            print("!" * len(banner), file=stream)
            print(banner, file=stream)
            print("!" * len(banner), file=stream, flush=True)
        if not cases:
            print("no case files changed; nothing to run.")
            return 0

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
        # Materialize the harness's stable bin dir (and its one-time provenance
        # banner) on this thread, so workers find it warm instead of racing to
        # build it and printing into each other's output.
        try:
            _cargo_trust_wp = harness_runner.resolve_harness_binary(
                workspace, "cargo-trust-wp"
            )
            if _cargo_trust_wp.exists():
                harness_runner._stable_harness_bin_dir(
                    workspace, _cargo_trust_wp, harness._current_facade()
                )
        except (OSError, AttributeError):
            pass
        workers = max(1, min(args.jobs, len(cases)))
        if workers > 1:
            print(f"Running {len(cases)} cases across {workers} workers.", flush=True)
        outcomes = run_cases_parallel(
            workspace,
            cases,
            shared_target,
            args.timeout,
            args.verbose,
            args.keep_output,
            args.jobs,
        )
    finally:
        if owns_target:
            shutil.rmtree(shared_target, ignore_errors=True)

    exit_code = print_summary(outcomes)
    if args.changed_since:
        print()
        print(
            f"  ^ PARTIAL: {len(cases)}/{total_cases} cases (changed since "
            f"{args.changed_since}). Not the gate.",
            flush=True,
        )

    if args.json:
        partial = (
            {"partial": {"changed_since": args.changed_since, "of_total": total_cases}}
            if args.changed_since
            else {}
        )
        Path(args.json).write_text(
            json.dumps(
                {
                    **partial,
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
