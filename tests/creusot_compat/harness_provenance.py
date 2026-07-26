#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Git provenance, dirty-tree tracking, and baseline freshness helpers.

Patch-sensitive helpers route through a harness facade so existing monkeypatch
targets on ``harness.py`` continue to work after extraction.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import shlex
import subprocess
import sys
from pathlib import Path

try:
    from tests.creusot_compat.harness_facade import (
        PROVENANCE_REQUIRED_ATTRS,
        resolve_harness_facade,
    )
except ModuleNotFoundError:
    from harness_facade import PROVENANCE_REQUIRED_ATTRS, resolve_harness_facade


def _resolve_harness_facade(facade: object | None) -> object:
    return resolve_harness_facade(
        facade, PROVENANCE_REQUIRED_ATTRS, context="provenance"
    )


def _get_dirty_files(
    workspace: Path,
    facade: object | None = None,
) -> list[str]:
    """Return dirty file paths, or an empty list if the tree is clean."""
    _ = facade
    try:
        result = subprocess.run(
            ["git", "status", "--porcelain", "--untracked-files=normal"],
            cwd=workspace,
            capture_output=True,
            text=True,
            timeout=5,
        )
        if result.returncode == 0 and result.stdout.strip():
            return [line[3:] for line in result.stdout.splitlines() if len(line) > 3]
    except (subprocess.TimeoutExpired, FileNotFoundError):
        pass
    return []


_OUTPUT_ARTIFACT_PREFIXES = ("reports/",)
_OUTPUT_ARTIFACT_CANONICAL_FILES = (
    "tests/creusot_compat/results.json",
    "tests/creusot_compat/results-should-fail.json",
    "tests/creusot_compat/results-examples.json",
)
_OUTPUT_ARTIFACT_EXACT_FILES = (
    ".test_state.json.lock",
    ".ownership_conflicts.log.lock",
)
_OUTPUT_ARTIFACT_RESULTS_PATTERN = re.compile(
    r"^tests/creusot_compat/results-[^/]+\.json$"
)
_OUTPUT_ARTIFACT_BINARY_PATTERNS = (
    # Top-level rustc/cargo artifacts from ad-hoc harness debugging.
    re.compile(r"^lib[^/]+\.rlib$"),
    re.compile(r"^test_[^/.]+$"),
    # Fixture-local compiled artifacts (not checked-in source).
    re.compile(r"^tests/fixtures/[^/]+/lib[^/]+\.rlib$"),
    re.compile(r"^tests/fixtures/[^/]+/test_[^/.]+$"),
)


def _is_output_artifact_path(
    path: str,
    facade: object | None = None,
) -> bool:
    """Return True when *path* is a harness output artifact."""
    harness = _resolve_harness_facade(facade)
    canonical_outputs = (
        harness.CANONICAL_OUTPUT,
        harness.CANONICAL_SHOULD_FAIL_OUTPUT,
        harness.CANONICAL_EXAMPLES_OUTPUT,
        *_OUTPUT_ARTIFACT_CANONICAL_FILES,
    )
    if any(path.startswith(prefix) for prefix in _OUTPUT_ARTIFACT_PREFIXES):
        return True
    if any(harness._is_same_rel_path(path, canonical) for canonical in canonical_outputs):
        return True
    if path in _OUTPUT_ARTIFACT_EXACT_FILES:
        return True
    if _OUTPUT_ARTIFACT_RESULTS_PATTERN.match(path) is not None:
        return True
    return any(pattern.match(path) is not None for pattern in _OUTPUT_ARTIFACT_BINARY_PATTERNS)


def _filter_source_dirty_files(
    dirty_files: list[str],
    facade: object | None = None,
) -> list[str]:
    """Filter out output artifacts, returning only source-relevant dirty files."""
    harness = _resolve_harness_facade(facade)
    return [path for path in dirty_files if not harness._is_output_artifact_path(path)]


def _get_git_commit(
    workspace: Path,
    dirty_files: list[str] | None = None,
    facade: object | None = None,
) -> str | None:
    """Get the current git commit hash, or None if not in a git repo."""
    _ = dirty_files
    _ = facade
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            cwd=workspace,
            capture_output=True,
            text=True,
            timeout=5,
        )
        if result.returncode == 0:
            return result.stdout.strip()
    except (subprocess.TimeoutExpired, FileNotFoundError):
        pass
    return None


def build_run_metadata(
    args: argparse.Namespace,
    workspace: Path,
    discovered_count: int,
    executed_count: int,
    dirty_files: list[str] | None = None,
    pinned_commit: str | None = None,
    head_drift_commits: int | None = None,
    head_drift_max_commits: int | None = None,
    facade: object | None = None,
) -> dict[str, object]:
    """Build run metadata dict for harness output JSON."""
    harness = _resolve_harness_facade(facade)
    is_partial = args.filter is not None or args.limit is not None
    lane = getattr(args, "lane", "should_succeed")
    git_commit = pinned_commit or harness._get_git_commit(
        workspace, dirty_files=dirty_files
    )
    meta: dict[str, object] = {
        "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "git_commit": git_commit,
        "command": shlex.join(sys.argv),
        "is_partial": is_partial,
        "lane": lane,
        "filter": args.filter,
        "limit": args.limit,
        "discovered_tests": discovered_count,
        "executed_tests": executed_count,
    }
    if dirty_files:
        meta["dirty_file_count"] = len(dirty_files)
        meta["dirty_files"] = dirty_files
    if head_drift_max_commits is not None:
        meta["head_drift_max_commits"] = head_drift_max_commits
    if head_drift_commits is not None:
        if head_drift_commits > 0:
            meta["head_drift_commits"] = head_drift_commits
        if head_drift_max_commits is not None:
            meta["head_drift_exceeded"] = (
                head_drift_commits > head_drift_max_commits
            )
    return meta


def _is_same_rel_path(
    path_a: str,
    path_b: str,
    facade: object | None = None,
) -> bool:
    """Return True when two relative paths resolve to the same location."""
    _ = facade
    return os.path.normpath(path_a) == os.path.normpath(path_b)


def _strip_dirty_suffix(
    commit: str | None,
    facade: object | None = None,
) -> str | None:
    """Normalize metadata git commit values for git rev-list queries."""
    _ = facade
    if commit is None:
        return None
    return commit.removesuffix("-dirty")


def _load_results_git_commit(
    results_path: Path,
    facade: object | None = None,
) -> str | None:
    """Read metadata.git_commit from a harness output file."""
    _ = facade
    try:
        payload = json.loads(results_path.read_text())
    except (FileNotFoundError, OSError, json.JSONDecodeError):
        return None

    metadata = payload.get("metadata")
    if not isinstance(metadata, dict):
        return None

    commit = metadata.get("git_commit")
    if isinstance(commit, str) and commit:
        return commit
    return None


def _commit_distance_to_head(
    workspace: Path,
    commit: str | None,
    facade: object | None = None,
) -> int | None:
    """Return `git rev-list --count <commit>..HEAD`, or None on failure."""
    harness = _resolve_harness_facade(facade)
    normalized = harness._strip_dirty_suffix(commit)
    if not normalized:
        return None

    try:
        result = subprocess.run(
            ["git", "rev-list", "--count", f"{normalized}..HEAD"],
            cwd=workspace,
            capture_output=True,
            text=True,
            timeout=5,
        )
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return None

    if result.returncode != 0:
        return None

    try:
        return int(result.stdout.strip())
    except ValueError:
        return None


def compute_lane_pair_freshness(
    *,
    workspace: Path,
    lane: str,
    output_rel: str,
    is_partial: bool,
    current_git_commit: str | None,
    max_age_gap_commits: int | None = None,
    facade: object | None = None,
) -> dict[str, object] | None:
    """Compute freshness status for canonical should_succeed/should_fail pair."""
    harness = _resolve_harness_facade(facade)
    if max_age_gap_commits is None:
        max_age_gap_commits = harness.LANE_PAIR_MAX_AGE_GAP_COMMITS

    if is_partial:
        return None

    if lane == "should_succeed" and harness._is_same_rel_path(
        output_rel, harness.CANONICAL_OUTPUT
    ):
        current_lane = "should_succeed"
        current_output = harness.CANONICAL_OUTPUT
        paired_lane = "should_fail"
        paired_output = harness.CANONICAL_SHOULD_FAIL_OUTPUT
    elif lane == "should_fail" and harness._is_same_rel_path(
        output_rel, harness.CANONICAL_SHOULD_FAIL_OUTPUT
    ):
        current_lane = "should_fail"
        current_output = harness.CANONICAL_SHOULD_FAIL_OUTPUT
        paired_lane = "should_succeed"
        paired_output = harness.CANONICAL_OUTPUT
    else:
        return None

    paired_git_commit = harness._load_results_git_commit(workspace / paired_output)
    current_age = harness._commit_distance_to_head(workspace, current_git_commit)
    paired_age = harness._commit_distance_to_head(workspace, paired_git_commit)

    freshness: dict[str, object] = {
        "status": "unknown",
        "current_lane": current_lane,
        "current_output": current_output,
        "current_git_commit": current_git_commit,
        "current_age_commits": current_age,
        "paired_lane": paired_lane,
        "paired_output": paired_output,
        "paired_git_commit": paired_git_commit,
        "paired_age_commits": paired_age,
        "max_age_gap_commits": max_age_gap_commits,
        "age_gap_commits": None,
    }

    if current_age is None:
        freshness["reason"] = "current metadata git_commit missing or not reachable"
        return freshness
    if paired_git_commit is None:
        freshness["reason"] = (
            f"paired lane metadata missing at {paired_output}; refresh paired lane baseline"
        )
        return freshness
    if paired_age is None:
        freshness["reason"] = "paired lane git_commit missing or not reachable"
        return freshness

    age_gap = abs(current_age - paired_age)
    freshness["age_gap_commits"] = age_gap
    freshness["status"] = "stale" if age_gap > max_age_gap_commits else "ok"
    return freshness


def check_baseline_freshness(
    workspace: Path,
    max_age_commits: int | None = None,
    commit_overrides: dict[str, str] | None = None,
    facade: object | None = None,
) -> dict[str, object]:
    """Check absolute freshness of both canonical baseline files."""
    harness = _resolve_harness_facade(facade)
    if max_age_commits is None:
        max_age_commits = harness.BASELINE_MAX_AGE_COMMITS_DEFAULT

    # Severity ordering: higher = worse.
    status_severity: dict[str, int] = {
        "fresh": 0,
        "stale": 1,
        "invalid": 2,
        "missing": 3,
    }

    def _escalate(current: str, candidate: str) -> str:
        if status_severity.get(candidate, 0) > status_severity.get(current, 0):
            return candidate
        return current

    lanes = {
        "should_succeed": harness.CANONICAL_OUTPUT,
        "should_fail": harness.CANONICAL_SHOULD_FAIL_OUTPUT,
        "examples": harness.CANONICAL_EXAMPLES_OUTPUT,
    }
    result: dict[str, object] = {
        "status": "fresh",
        "max_age_commits": max_age_commits,
        "lanes": {},
    }

    # The examples lane is a demonstrative, known-degraded corpus (rustc ICE /
    # never-green since inception). Its freshness is reported for visibility but
    # is ADVISORY: it must not escalate the overall status, so a stale/invalid
    # examples baseline can never fail the canonical should_succeed/should_fail
    # freshness gate. See refresh-baselines.sh (examples is best-effort publish).
    advisory_lanes = {"examples"}

    for lane_name, canonical_path in lanes.items():
        full_path = workspace / canonical_path
        lane_info: dict[str, object] = {"path": canonical_path}
        advisory = lane_name in advisory_lanes

        def _apply(status: str) -> None:
            lane_info["status"] = status
            if not advisory:
                result["status"] = _escalate(str(result["status"]), status)

        commit = None
        if commit_overrides is not None:
            commit = commit_overrides.get(lane_name)
        if commit is None:
            if not full_path.exists():
                _apply("missing")
                result["lanes"][lane_name] = lane_info
                continue
            commit = harness._load_results_git_commit(full_path)
        lane_info["git_commit"] = commit

        if commit is None:
            _apply("invalid")
            result["lanes"][lane_name] = lane_info
            continue

        if commit.endswith("-dirty"):
            lane_info["age_commits"] = None
            _apply("dirty" if advisory else "stale")
            result["lanes"][lane_name] = lane_info
            continue

        age = harness._commit_distance_to_head(workspace, commit)
        lane_info["age_commits"] = age

        if age is None:
            _apply("invalid")
        elif age > max_age_commits:
            _apply("stale")
        else:
            lane_info["status"] = "fresh"

        result["lanes"][lane_name] = lane_info

    return result


def _drop_status_fields(
    value: object,
    facade: object | None = None,
) -> object:
    """Recursively remove ``status`` keys from nested dict/list structures."""
    _ = facade
    if isinstance(value, dict):
        return {
            key: _drop_status_fields(item)
            for key, item in value.items()
            if key != "status"
        }
    if isinstance(value, list):
        return [_drop_status_fields(item) for item in value]
    return value


def _snapshot_freshness_for_metadata(
    freshness: dict[str, object],
    *,
    evaluated_against_head: str | None,
    facade: object | None = None,
) -> dict[str, object]:
    """Prepare freshness payload for artifact metadata."""
    harness = _resolve_harness_facade(facade)
    snapshot = harness._drop_status_fields(freshness)
    if isinstance(snapshot, dict):
        snapshot["evaluated_against_head"] = evaluated_against_head
    return snapshot
