#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Shared data model and constant authority for the Creusot harness."""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Literal


# Wire line prefix emitted by cargo-trust-wp for structured telemetry (#1690, #2641).
WIRE_PREFIX = "TRUST_WP_RESULT:v1"


@dataclass
class VerificationTelemetry:
    """Structured verification counters from the trust-wp result protocol (#2641).

    Mirrors ``trust_wp_core::result_protocol::StructuredVerificationResult``.
    Populated when cargo-trust-wp re-emits the aggregated wire line.
    """

    verified: int = 0
    failed: int = 0
    errors: int = 0
    warnings: int = 0
    assumed: int = 0
    trusted: int = 0
    skipped: int = 0
    verified_with_axiom_deps: int = 0
    unverified_axioms: int = 0
    vacuous: int = 0
    proof_assert_failed: int = 0
    proof_assert_errors: int = 0
    evidence_gaps: int = 0
    panics: int = 0
    demoted: int = 0
    parse_errors: int = 0
    termination_errors: int = 0
    logic_recursion_errors: int = 0
    erasure_errors: int = 0
    base_exit_code: int = 0

    def to_dict(self) -> dict[str, int]:
        """Serialize to a plain dict for JSON output."""
        return {
            "verified": self.verified,
            "failed": self.failed,
            "errors": self.errors,
            "warnings": self.warnings,
            "assumed": self.assumed,
            "trusted": self.trusted,
            "skipped": self.skipped,
            "verified_with_axiom_deps": self.verified_with_axiom_deps,
            "unverified_axioms": self.unverified_axioms,
            "vacuous": self.vacuous,
            "proof_assert_failed": self.proof_assert_failed,
            "proof_assert_errors": self.proof_assert_errors,
            "evidence_gaps": self.evidence_gaps,
            "panics": self.panics,
            "demoted": self.demoted,
            "parse_errors": self.parse_errors,
            "termination_errors": self.termination_errors,
            "logic_recursion_errors": self.logic_recursion_errors,
            "erasure_errors": self.erasure_errors,
            "base_exit_code": self.base_exit_code,
        }

    @classmethod
    def from_dict(cls, d: dict[str, int]) -> VerificationTelemetry:
        """Deserialize from a plain dict (JSON round-trip)."""
        return cls(**{k: d.get(k, 0) for k in cls.__dataclass_fields__})


TELEMETRY_FIELD_NAMES = tuple(VerificationTelemetry.__dataclass_fields__)


def parse_wire_line(line: str) -> VerificationTelemetry | None:
    """Parse a ``TRUST_WP_RESULT:v1`` wire line into telemetry.

    Returns ``None`` if the line does not match the expected format.
    """
    if not line.startswith(WIRE_PREFIX):
        return None
    rest = line[len(WIRE_PREFIX):].strip()
    if not rest:
        return None
    pairs: dict[str, int] = {}
    for token in rest.split():
        if "=" not in token:
            return None
        key, _, raw_value = token.partition("=")
        if key in pairs:
            return None
        try:
            value = int(raw_value)
        except ValueError:
            return None
        if value < 0:
            return None
        pairs[key] = value
    required = set(TELEMETRY_FIELD_NAMES)
    if set(pairs) != required:
        return None
    return VerificationTelemetry(**{key: pairs[key] for key in TELEMETRY_FIELD_NAMES})


@dataclass
class TestResult:
    """Result of running a single Creusot test."""

    name: str
    status: Literal["pass", "fail", "unknown", "skip", "error"]
    message: str
    duration_ms: int
    # Reason for skip (feature not yet supported, etc.)
    skip_reason: str | None = None
    # Sub-classification for error results (#2208). None for non-error statuses.
    error_category: str | None = None
    # True when the stored message was shortened for JSON output.
    message_truncated: bool = False
    # Semantic verification tier (None for should_fail / skip results).
    verification_tier: str | None = None
    # Structured verification telemetry from the result protocol (#2641).
    # None when the wire line was not present in cargo-trust-wp output.
    telemetry: VerificationTelemetry | None = None


PARSE_FAILURE_PATTERNS: dict[str, re.Pattern[str]] = {
    # #504 acceptance gates explicitly track contract clause parser stability.
    "contract_clauses": re.compile(
        r"failed to parse (contract|requires|ensures)\b", re.IGNORECASE
    ),
    "assertion": re.compile(r"failed to parse assertion\b", re.IGNORECASE),
    "ghost_block": re.compile(r"failed to parse ghost block\b", re.IGNORECASE),
    "logic_function_body": re.compile(
        r"failed to parse logic function body\b", re.IGNORECASE
    ),
}


VALID_LANES = ("should_succeed", "should_fail", "examples", "all")

DISK_WARNING_THRESHOLD_PERCENT = 80
STALE_HARNESS_TEMP_MAX_AGE_HOURS = 12
HARNESS_TEMP_TARGET_PREFIX = "trust_wp_harness_target_"

_AI_ROLES = frozenset({"WORKER", "PROVER", "RESEARCHER", "MANAGER", "SYNCER"})
_SKIP_PREBUILD_ENV = "TRUST_WP_HARNESS_SKIP_PREBUILD"
_TRUTHY_ENV_VALUES = frozenset({"1", "true", "yes", "on"})
_TARGET_ROLE_NAME_RE = re.compile(
    r"^(worker|prover|researcher|manager|syncer|user)(?:_(\d+))?$"
)
_ROOT_PID_NAME_RE = re.compile(
    r"^\.pid_(worker|prover|researcher|manager|syncer|user)(?:_(\d+))?$"
)
_AIT_PID_NAME_RE = re.compile(
    r"^(worker|prover|researcher|manager|syncer|user)(?:_(\d+))?$"
)


# Default output path for canonical (full, unfiltered) runs.
CANONICAL_OUTPUT = "tests/creusot_compat/results.json"
CANONICAL_SHOULD_FAIL_OUTPUT = "tests/creusot_compat/results-should-fail.json"
CANONICAL_EXAMPLES_OUTPUT = "tests/creusot_compat/results-examples.json"

# Large lane-age gaps indicate parity triage is mixing non-comparable baselines.
LANE_PAIR_MAX_AGE_GAP_COMMITS = 20

# Full baseline runs can take long enough for HEAD to move substantially.
# Beyond this policy threshold we warn (or fail with --fail-on-head-drift).
HEAD_DRIFT_MAX_COMMITS_DEFAULT = 10
HEAD_DRIFT_POLICY_EXIT_CODE = 4

# Absolute canonical baseline age limit (#722). When either canonical file
# is more than this many commits behind HEAD, --check-baseline-freshness
# reports "stale" and the harness can optionally fail (exit 5).
BASELINE_MAX_AGE_COMMITS_DEFAULT = 50
BASELINE_FRESHNESS_EXIT_CODE = 5
