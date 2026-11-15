#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Semantic verification tier classification for compat harness results.

Classifies each should_succeed test result into a ``VerificationTier`` from
legacy display shape (status, message, source text). New runner records and
the final review gate use ``recompute_record_grade``: typed counters, raw
report lines, and the current oracle inventory determine their proof grade.
The text-only API remains for consumers of historical result messages.

The boundary is the ordered precedence list in the docstring of
``classify_verification_tier``. In outline: tier2 is a clean positive proof,
including a NO_REPLAY pass trust-wp itself verified; tier2-source-trusted a
tier2 whose only trusted items are ones the corpus source itself declares
``#[trusted]``; tier1 a pass whose only evidence is the strict-rejection
marker or a verification surface in the source; legacy_unknown a
blank-message pass over source with a verification surface; tier0 a pass over
source with no verification surface; tier0-no-obligation a pass on a test
whose Creusot translation carries no goal (D-19); tier3 every non-pass result
(fail, unknown, error) and every pass that rests on trusted, skipped, assumed
or unverified-axiom facts, a mixed result, or a parse-only NO_REPLAY pass --
fail-closed for true-100 accounting (#2510). Skip results and the should_fail
lane are out of scope (``None``).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import Literal

_SCRIPTS_DIR = Path(__file__).resolve().parents[2] / "scripts"
if str(_SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS_DIR))
from trusted_source_scan import (  # noqa: E402
    extract_trusted_def_paths,
    resolve_trusted_def_path,
    unresolved_trusted_def_paths,
)
from creusot_goal_coverage import (  # noqa: E402
    compute_goal_coverage,
    creusot_emitted_nothing,
    driver_report_lines,
    goal_inventory,
)

from verification_grade import recompute_record_grade  # noqa: E402

VerificationTier = Literal[
    "tier0",
    "tier1",
    "tier2",
    "tier3",
    "legacy_unknown",
    "tier2-source-trusted",
    "tier0-no-obligation",
]

# A clean proof pass whose ONLY non-verifying items are ones the corpus source
# itself declares ``#[trusted]`` (Creusot's own axioms). Distinct from tier2 so
# the trust base stays visible in every summary; see trusted_source_scan.py.
SOURCE_TRUSTED_TIER = "tier2-source-trusted"

# A pass on a test whose Creusot translation carries NO obligation at all: the
# reference .coma exists and its goal inventory is EMPTY, so there is nothing
# any verifier could discharge and nothing trust-wp's own verdict can be
# evidence OF. Such a crate is never graded at a proof-grade tier (D-19): it
# is deliberately NOT tier1 and NOT tier2, so the headline tier counts never
# mix "proved everything Creusot proves" with "there was nothing to prove".
# The gate may still count it clean, but only through zero-goal parity (D-88),
# which re-reads the oracle and trust-wp's own record and does not rely on
# this label.
#
# It is NOT a claim that the row is uninteresting: trust-wp may well have
# printed `verified ✓` for an item here. It is the claim that the item verified
# is not a Creusot goal, so the row cannot carry proof-grade credit for the
# corpus. Applied only when the inventory EXISTS and is empty -- a missing
# .coma proves nothing about obligations and keeps its old tier.
NO_OBLIGATION_TIER = "tier0-no-obligation"

# Prefixes used by legacy harness classifier policy results.
_NO_REPLAY_PASS_PREFIX = "Parse-only (NO_REPLAY):"
_STRICT_PASS_PREFIX = "Correctly rejected (strict):"
_NO_REPLAY_VERIFIED_PREFIX = "Verified (NO_REPLAY):"


def source_has_verification_surface(source: str) -> bool:
    """Return True when the source contains explicit proof-bearing surface.

    Broader than ``_source_has_user_contracts()`` in harness_classify_succeed —
    this also recognizes ``#[logic]``, ``#[trusted]``, and ``proof_assert!``
    as verification-relevant author intent.
    """
    if re.search(r"#\s*\[\s*(requires|ensures|invariant|variant)\s*\(", source):
        return True
    if re.search(r"#\s*\[\s*logic", source):
        return True
    if re.search(r"#\s*\[\s*trusted", source):
        return True
    if "proof_assert!" in source:
        return True
    return False


def classify_verification_tier(
    test_name: str,
    status: str,
    message: str,
    skip_reason: str | None,
    source: str,
    trusted_def_paths: list[str] | None = None,
) -> VerificationTier | None:
    """Classify a single test result into a semantic verification tier.

    Rule 4b (source-trusted parity): a pass carrying trusted items is graded
    ``tier2-source-trusted`` iff every trusted item (``trusted_def_paths``, or
    the ``trusted (skipped)`` lines of ``message``) resolves to an item the
    source declares ``#[trusted]``, the named items account for the whole
    ``trusted=`` counter, and the message with exactly those trusted markers
    removed would be tier2. Anything else keeps the fail-closed tier3.

    Returns ``None`` for should_fail lane entries (they use a different
    success policy and should not contaminate the pass-rate summary).

    Precedence rules (applied in order):

    1. should_fail lane -> None
    2. non-pass should_succeed result -> tier3
    3. pass with mixed success (verified + proof_assert errors) -> tier3
    4. legacy NO_REPLAY_PASS_PREFIX pass -> tier3
    5. trusted/skipped or unverified axiom markers -> tier3
    5b. NO_REPLAY_VERIFIED_PREFIX (verified NO_REPLAY) -> tier2
    6. STRICT_PASS_PREFIX -> tier1
    7. clean verified success -> tier2
    8. empty/whitespace message + verification surface in source -> legacy_unknown
    9. remaining pass + verification surface -> tier1
    10. remaining pass -> tier0

    Rule 3 and Rule 5 must precede the tier1 and tier2 checks so trusted,
    skipped, and unverified axiom results fail closed for true-100 accounting.
    """
    # Rule 1: should_fail lane is out of scope.
    if test_name.startswith("tests/should_fail/"):
        return None

    msg = message or ""

    # Rule 2: non-pass verification-relevant should_succeed result.
    if status != "pass":
        if status in ("fail", "unknown", "error"):
            return "tier3"
        # skip results are not verification-relevant — return None so they
        # don't pollute tier counts.
        return None

    # --- From here on, status == "pass" ---

    msg_lower = msg.lower()

    # Rule 3: pass with mixed success (proof_assert errors override tier1
    # markers). Must precede the tier1 marker check — a pass with
    # proof_assert errors is tier3 regardless of axiom/trusted markers.
    if "verified" in msg_lower and _has_unresolved_proof_assert(msg):
        return "tier3"

    # Rule 4: legacy NO_REPLAY parse-only passes are strict failures.
    if msg.startswith(_NO_REPLAY_PASS_PREFIX):
        return "tier3"

    # Rule 4b: source-declared #[trusted] items only (Creusot's own axioms).
    source_trusted = _source_trusted_sanitized_message(msg, source, trusted_def_paths)
    if source_trusted is not None:
        inner = classify_verification_tier(
            test_name, status, source_trusted, skip_reason, source, trusted_def_paths=[]
        )
        return SOURCE_TRUSTED_TIER if inner == "tier2" else inner

    # Rule 5: non-verifying markers are not proof passes. Keep status parsing
    # unchanged, but count these as incomplete for strict/tier accounting.
    if _has_fail_closed_trust_or_axiom_marker(msg):
        return "tier3"

    # Rule 5c (D-19): Creusot's own translation carries no obligation. Placed
    # after every fail-closed tier3 rule (a zero-obligation row that still
    # carries trusted/axiom/proof_assert-error markers stays tier3, the more
    # conservative answer) and before every credit-granting rule, so no
    # zero-obligation row can reach tier1 or tier2.
    if _creusot_inventory_is_empty(test_name):
        return NO_OBLIGATION_TIER

    # Rule 5b: a NO_REPLAY test that trust-wp VERIFIED is a real proof. The
    # stored message is fixed text, so the soundness evidence lives in
    # classify_no_replay_result_with_mode: mode "verified" requires clean wire
    # telemetry, zero exit, verified>0 AND zero trusted/skipped/assumed/
    # vacuous/axiom/evidence-gap counters. Rules 3 and 5 still see the wire
    # counters the runner appends to the tier message.
    if msg.startswith(_NO_REPLAY_VERIFIED_PREFIX):
        return "tier2"

    # Rule 6: strict policy-pass marker.
    if msg.startswith(_STRICT_PASS_PREFIX):
        return "tier1"

    # Rule 7: clean verified success.
    if msg == "Verification succeeded":
        return "tier2"
    # Also recognize pass results with explicit positive verification evidence
    # plus no failures/errors.
    if _has_positive_verified_success(msg) and _has_no_unresolved_failures(msg):
        return "tier2"

    # Rule 8: empty/whitespace message with verification surface.
    if not msg.strip():
        if source_has_verification_surface(source):
            return "legacy_unknown"
        # Genuine compile-only blank pass -> tier0 (rule 9 fallthrough).
        return "tier0"

    # Rule 9: remaining pass with verification surface in source.
    if source_has_verification_surface(source):
        return "tier1"

    # Rule 10: remaining pass -> tier0 (compile-only / synthesized-only).
    return "tier0"



def _creusot_inventory_is_empty(test_name: str) -> bool:
    """True iff Creusot's reference .coma for ``test_name`` EXISTS and carries
    no goal-bearing item, or Creusot translated the test to nothing
    (``creusot_emitted_nothing``: its ui runner reads the absent file as empty
    output).

    Fail-closed in both failure modes: any other missing .coma
    (``goal_inventory`` returns ``None``) and any inventory crash answer False,
    so the row keeps whatever tier the remaining rules give it.

    Deliberately the bare inventory, not ``zero_goal_oracle_refusals``: an
    empty inventory over a ``.coma`` whose goals the inventory does not count
    (closures/01_basic) must still land here. Any tier the later rules gave it
    would be graded by goal coverage over that same empty inventory, which
    asks for nothing; here zero-goal parity refuses it instead (D-89)."""
    try:
        items = goal_inventory(test_name)
        if items is None:
            return creusot_emitted_nothing(test_name)
    except Exception:  # pragma: no cover - an inventory crash never grants a tier
        return False
    return len(items) == 0


def _has_no_unresolved_failures(msg: str) -> bool:
    """Check that a message with 'verified' has no unresolved failures/errors."""
    msg_lower = msg.lower()
    if "FAILED" in msg:
        return False
    if re.search(r"(?<![=])\b[1-9]\d*\s+failed\b", msg_lower):
        return False
    if re.search(r"\b(?:failed|proof_assert_failed)=[1-9]\d*\b", msg_lower):
        return False
    if re.search(r"(?<![=])\b[1-9]\d*\s+errors?\b", msg_lower):
        return False
    if re.search(r"\b(?:errors|proof_assert_errors|panics)=[1-9]\d*\b", msg_lower):
        return False
    if "trust-wp: error:" in msg_lower:
        return False
    if "unknown (" in msg_lower:
        return False
    return True


def _has_positive_verified_success(msg: str) -> bool:
    """Return True when output shows at least one verified obligation."""
    msg_lower = msg.lower()
    if "verified \u2713" in msg:
        return True
    if re.search(r"(?<![=])\b[1-9]\d*\s+verified\b", msg_lower):
        return True
    if re.search(r"\bverified=[1-9]\d*\b", msg_lower):
        return True
    return False


def _has_unresolved_proof_assert(msg: str) -> bool:
    """Check whether message indicates proof_assert failures alongside verified."""
    msg_lower = msg.lower()
    # ``inconclusive`` is an unproved assertion (solver unknown/incomplete).
    if re.search(r"\bproof_assert_(?:failed|errors|inconclusive)=[1-9]\d*\b", msg_lower):
        return True
    for line in msg_lower.split("\n"):
        if "proof_assert" not in line:
            continue
        if re.search(r"(?<![=])\b[1-9]\d*\s+(?:failed|errors?|inconclusive)\b", line):
            return True
        if re.search(r"\b(?:failed|errors?)=[1-9]\d*\b", line):
            return True
    return False


def _has_fail_closed_trust_or_axiom_marker(msg: str) -> bool:
    """Return True for accepted output that still depends on unverified facts."""
    msg_lower = msg.lower()
    marker_fragments = (
        "trusted (skipped)",
        "axiomatized, not verified",
        "assumed (axiom-only function",
        "postcondition unverified",
        # Named explicitly so tier3 does not depend on the separate
        # ``unverified axiom(s)`` summary line surviving message truncation.
        "postcondition failed (logic",
        "law postcondition unverified",
        "unverified axiom",
        "unverified fallback",
        "vacuous (",
        "vacuous proof",
        "unproven axiom deps",
        "evidence gap",
        "evidence-gap",
    )
    if any(fragment in msg_lower for fragment in marker_fragments):
        return True

    # Recognize positive structured counters when a stored message contains the
    # TRUST_WP_RESULT wire line or a textual verification summary.
    if re.search(
        r"\b(?:trusted|skipped|assumed|verified_with_axiom_deps|unverified_axioms|vacuous|evidence_gaps)=[1-9]\d*\b",
        msg_lower,
    ):
        return True
    if re.search(
        r"\b[1-9]\d*\s+(?:trusted|skipped|assumed|vacuous|unverified axiom)s?\b",
        msg_lower,
    ):
        return True
    if re.search(r"\b[1-9]\d*\s+verified\*\s*\(unproven axiom deps\)", msg_lower):
        return True
    return False


_TRUSTED_COUNTER_RE = re.compile(r"\btrusted=(\d+)\b")
_TRUSTED_SUMMARY_RE = re.compile(r"\b(\d+)\s+trusted\b")


def _message_trusted_count(msg: str) -> int:
    counters = _TRUSTED_COUNTER_RE.findall(msg)
    if counters:
        return int(counters[-1])
    summaries = _TRUSTED_SUMMARY_RE.findall(msg)
    return max((int(v) for v in summaries), default=0)


def _source_trusted_sanitized_message(
    msg: str, source: str, trusted_def_paths: list[str] | None
) -> str | None:
    """The message with source-declared trusted markers removed, else None.

    Returns None (no rule 4b) when the pass carries no trusted item, or when
    ANY trusted item fails to resolve against ``#[trusted]`` in ``source``.
    """
    if trusted_def_paths is not None and not trusted_def_paths:
        # ``[]`` is the recursion sentinel: the message is already sanitized.
        return None
    paths = list(trusted_def_paths) if trusted_def_paths else extract_trusted_def_paths(msg)
    count = _message_trusted_count(msg)
    if not paths and count == 0:
        return None
    if unresolved_trusted_def_paths(paths, source, count):
        return None
    lines = []
    for line in msg.split("\n"):
        stripped = line.strip()
        if extract_trusted_def_paths(stripped):
            continue
        if re.fullmatch(r"trust-wp:\s*\(\d+ trusted, skipped\)", stripped):
            continue
        line = re.sub(r",\s*\d+\s+trusted\b", "", line)
        line = _TRUSTED_COUNTER_RE.sub("trusted=0", line)
        lines.append(line)
    sanitized = "\n".join(lines)
    if "trusted (skipped)" in sanitized or _message_trusted_count(sanitized):
        return None
    return sanitized
