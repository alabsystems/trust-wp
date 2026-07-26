#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Semantic verification tier classification for compat harness results.

Classifies each should_succeed test result into one of five tiers based on
the stored result shape (status, message, source text). This is the sole
authority for the Tier 0 / Tier 1 / Tier 2 / Tier 3 boundary — do not
reconstruct tiers from ad hoc jq rules or message heuristics elsewhere.

See designs/2026-03-19-2510-semantic-verification-tier-reporting.md for the
full design rationale.
"""

from __future__ import annotations

import re
from typing import Literal

VerificationTier = Literal[
    "tier0",
    "tier1",
    "tier2",
    "tier3",
    "legacy_unknown",
]

# Prefixes used by legacy harness classifier policy results.
_NO_REPLAY_PASS_PREFIX = "Parse-only (NO_REPLAY):"
_STRICT_PASS_PREFIX = "Correctly rejected (strict):"


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
) -> VerificationTier | None:
    """Classify a single test result into a semantic verification tier.

    Returns ``None`` for should_fail lane entries (they use a different
    success policy and should not contaminate the pass-rate summary).

    Precedence rules (applied in order):

    1. should_fail lane -> None
    2. non-pass should_succeed result -> tier3
    3. pass with mixed success (verified + proof_assert errors) -> tier3
    4. legacy NO_REPLAY_PASS_PREFIX pass -> tier3
    5. trusted/skipped or unverified axiom markers -> tier3
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

    # Rule 5: non-verifying markers are not proof passes. Keep status parsing
    # unchanged, but count these as incomplete for strict/tier accounting.
    if _has_fail_closed_trust_or_axiom_marker(msg):
        return "tier3"

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
    if re.search(r"\bproof_assert_(?:failed|errors)=[1-9]\d*\b", msg_lower):
        return True
    for line in msg_lower.split("\n"):
        if "proof_assert" not in line:
            continue
        if re.search(r"(?<![=])\b[1-9]\d*\s+(?:failed|errors?)\b", line):
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
