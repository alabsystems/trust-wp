#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Output normalization, truncation, and summary helpers for the Creusot harness.

Patch-sensitive helpers route through a harness facade so existing monkeypatch
targets on ``harness.py`` continue to work after extraction.
"""

from __future__ import annotations

import re
from pathlib import Path

try:
    from tests.creusot_compat.harness_facade import (
        OUTPUT_REQUIRED_ATTRS,
        resolve_harness_facade,
    )
except ModuleNotFoundError:
    from harness_facade import OUTPUT_REQUIRED_ATTRS, resolve_harness_facade

TRUNCATED_OUTPUT_MARKER = "... [truncated] ..."
TRUNCATED_OUTPUT_SENTINEL = f"\n{TRUNCATED_OUTPUT_MARKER}\n"
TRUNCATED_OUTPUT_MAX_LEN = 30000
TRUNCATED_OUTPUT_HEAD_LEN = 5000


def _resolve_harness_facade(facade: object | None) -> object:
    return resolve_harness_facade(
        facade, OUTPUT_REQUIRED_ATTRS, context="output"
    )


def _normalize_output_for_storage(
    output: str,
    workspace: Path,
    facade: object | None = None,
) -> str:
    """Normalize unstable paths to keep baseline diffs reviewable."""
    _ = facade
    normalized = output.replace(str(workspace), "<WORKSPACE>")

    temp_path_patterns = [
        # macOS temp dirs (tempfile.TemporaryDirectory).
        r"/private/var/folders/[^\s\"')]+/T/tmp[^\s/\"')]+",
        r"/var/folders/[^\s\"')]+/T/tmp[^\s/\"')]+",
        # Linux temp dirs.
        r"/tmp/tmp[^\s/\"')]+",
    ]
    for pattern in temp_path_patterns:
        normalized = re.sub(pattern, "<TMPDIR>", normalized)

    # Build lock holder details (session IDs, role names, iteration numbers,
    # timestamps) are non-deterministic and create noisy diffs across runs.
    normalized = re.sub(
        r"^\[cargo-lock\] Waiting for build lock on trust-wp "
        r"\(held by slot \d+: .*?\)\.\.\.$",
        "[cargo-lock] Waiting for build lock on trust-wp (<LOCK_HELD>)...",
        normalized,
        flags=re.MULTILINE,
    )

    # Cargo wrapper lockless-mode banner is infrastructure noise (#1346).
    normalized = re.sub(
        r"^\[cargo\] Lockless mode \(AIT_ALLOW_LOCKLESS_CARGO=1\)\n",
        "",
        normalized,
        flags=re.MULTILINE,
    )

    # rustc ICE attachments encode wall-clock timestamps and PIDs.
    normalized = re.sub(
        r"rustc-ice-\d{4}-\d{2}-\d{2}T\d{2}_\d{2}_\d{2}-\d+\.txt",
        "rustc-ice-<TIMESTAMP>.txt",
        normalized,
    )
    return normalized


def _truncate_output_with_flag(
    output: str,
    workspace: Path,
    facade: object | None = None,
) -> tuple[str, bool]:
    """Normalize and optionally truncate build output for storage."""
    harness = _resolve_harness_facade(facade)
    normalized = harness._normalize_output_for_storage(output, workspace)
    if len(normalized) > TRUNCATED_OUTPUT_MAX_LEN:
        head = normalized[:TRUNCATED_OUTPUT_HEAD_LEN]
        tail = normalized[-(
            TRUNCATED_OUTPUT_MAX_LEN
            - TRUNCATED_OUTPUT_HEAD_LEN
            - len(TRUNCATED_OUTPUT_SENTINEL)
        ):]
        return head + TRUNCATED_OUTPUT_SENTINEL + tail, True
    return normalized, False


def _truncate_output(
    output: str,
    workspace: Path,
    facade: object | None = None,
) -> str:
    """Normalize and optionally truncate build output for storage."""
    return _truncate_output_with_flag(output, workspace, facade=facade)[0]


def _count_parse_failures(
    results: list[object],
    facade: object | None = None,
) -> dict[str, int]:
    """Count parse-failure signatures across non-skip results."""
    harness = _resolve_harness_facade(facade)
    counts = {key: 0 for key in harness.PARSE_FAILURE_PATTERNS}
    for result in results:
        if getattr(result, "skip_reason", None) is not None:
            continue
        message = getattr(result, "message", "") or ""
        for key, pattern in harness.PARSE_FAILURE_PATTERNS.items():
            if pattern.search(message):
                counts[key] += 1
    return counts


def _summarize_subset(
    results: list[object],
    facade: object | None = None,
) -> dict[str, object]:
    """Build summary counts for a list of TestResult-like objects."""
    harness = _resolve_harness_facade(facade)
    strict_pass = sum(
        1
        for result in results
        if getattr(result, "status", None) == "pass"
        and str(getattr(result, "message", "")).startswith(harness.STRICT_PASS_PREFIX)
    )
    no_replay_pass = sum(
        1
        for result in results
        if getattr(result, "status", None) == "pass"
        and str(getattr(result, "message", "")).startswith(harness.NO_REPLAY_PASS_PREFIX)
    )
    backend_superseded_pass = sum(
        1
        for result in results
        if getattr(result, "status", None) == "pass"
        and str(getattr(result, "message", "")).startswith(harness.BACKEND_PASS_PREFIX)
    )
    summary: dict[str, object] = {
        "total": len(results),
        "pass": sum(1 for result in results if getattr(result, "status", None) == "pass"),
        "fail": sum(1 for result in results if getattr(result, "status", None) == "fail"),
        "unknown": sum(
            1 for result in results if getattr(result, "status", None) == "unknown"
        ),
        "skip": sum(1 for result in results if getattr(result, "status", None) == "skip"),
        "error": sum(1 for result in results if getattr(result, "status", None) == "error"),
        "strict_pass": strict_pass,
        "no_replay_pass": no_replay_pass,
        "backend_superseded_pass": backend_superseded_pass,
    }

    skip_reasons: dict[str, int] = {}
    for result in results:
        skip_reason = getattr(result, "skip_reason", None)
        if skip_reason:
            skip_reasons[skip_reason] = skip_reasons.get(skip_reason, 0) + 1

    error_categories: dict[str, int] = {}
    unknown_categories: dict[str, int] = {}
    for result in results:
        error_cat = getattr(result, "error_category", None)
        if error_cat is not None:
            status = getattr(result, "status", None)
            if status == "unknown":
                unknown_categories[error_cat] = unknown_categories.get(error_cat, 0) + 1
            else:
                error_categories[error_cat] = error_categories.get(error_cat, 0) + 1

    summary["skip_reasons"] = skip_reasons
    if error_categories:
        summary["error_categories"] = error_categories
    if unknown_categories:
        summary["unknown_categories"] = unknown_categories
    summary["parse_failures"] = harness._count_parse_failures(results)

    # Tier-aware metrics (#2510).
    tier_counts: dict[str, int] = {
        "tier0": 0, "tier1": 0, "tier2": 0, "tier3": 0, "legacy_unknown": 0,
    }
    for result in results:
        vtier = getattr(result, "verification_tier", None)
        if vtier is not None and vtier in tier_counts:
            tier_counts[vtier] += 1
    summary["verification_tiers"] = tier_counts
    summary["tier2_verified"] = tier_counts["tier2"]
    tier2_plus_tier3 = tier_counts["tier2"] + tier_counts["tier3"]
    summary["tier2_rate"] = (
        round(tier_counts["tier2"] / tier2_plus_tier3, 4)
        if tier2_plus_tier3 > 0
        else None
    )

    return summary


def _result_lane(harness: object, result: object) -> str:
    """Derive the canonical harness lane for a result name."""
    name = str(getattr(result, "name", ""))
    if harness._is_should_fail_test(name):
        return "should_fail"
    if name.startswith("examples/"):
        return "examples"
    return "should_succeed"


def summarize_results(
    results: list[object],
    facade: object | None = None,
) -> dict[str, object]:
    """Summarize test results, with per-lane breakdowns for each result lane."""
    harness = _resolve_harness_facade(facade)
    lane_results: dict[str, list[object]] = {
        "should_succeed": [],
        "should_fail": [],
        "examples": [],
    }
    for result in results:
        lane_results[_result_lane(harness, result)].append(result)

    summary = harness._summarize_subset(results)

    for lane_name in ("should_succeed", "should_fail", "examples"):
        lane_subset = lane_results[lane_name]
        if not lane_subset:
            continue
        summary[lane_name] = harness._summarize_subset(lane_subset)
        if lane_name == "should_fail":
            _add_false_accept_count(summary[lane_name], lane_subset)

    return summary


def _add_false_accept_count(
    lane_summary: dict[str, object],
    fail_results: list[object],
) -> None:
    """Add false_accept_count to the should_fail lane summary (#2690).

    False-accepts are should-fail tests where trust-wp incorrectly verified
    code that should have been rejected.  They appear as ``status=fail``
    in the should_fail lane — either because trust-wp verified (success=True)
    or because they are known false-accepts from ``_KNOWN_FALSE_ACCEPT_TESTS``
    (reclassified from skip to fail in #2690).

    This count documents the known unsoundness gaps for tracking.
    """
    lane_summary["false_accept_count"] = sum(
        1 for result in fail_results
        if getattr(result, "status", None) == "fail"
    )
