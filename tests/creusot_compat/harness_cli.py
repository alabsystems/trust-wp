#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""CLI entry helpers for the Creusot compatibility harness."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Any

try:
    from tests.creusot_compat.harness_facade import (
        CLI_REQUIRED_ATTRS,
        resolve_harness_facade,
    )
    from tests.creusot_compat.harness_reporting import (
        _determine_exit_code,
        _print_policy_notes,
        _print_summary,
        _write_results_file,
    )
except ModuleNotFoundError:
    # Running as a script (`python3 tests/creusot_compat/harness.py`) puts this
    # directory on sys.path, so import sibling modules directly.
    from harness_facade import CLI_REQUIRED_ATTRS, resolve_harness_facade
    from harness_reporting import (  # type: ignore[no-redef]
        _determine_exit_code,
        _print_policy_notes,
        _print_summary,
        _write_results_file,
    )


def _resolve_harness_facade(facade: object | None) -> object:
    return resolve_harness_facade(facade, CLI_REQUIRED_ATTRS, context="cli")


def _build_parser(harness: object) -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run Creusot compatibility tests against trust-wp"
    )
    parser.add_argument("-v", "--verbose", action="store_true", help="Verbose output")
    parser.add_argument("-f", "--filter", type=str, help="Filter tests by pattern")
    parser.add_argument("-n", "--limit", type=int, help="Limit number of tests")
    parser.add_argument(
        "-t",
        "--timeout",
        type=int,
        default=120,
        help="Per-test process timeout in seconds (default: 120)",
    )
    parser.add_argument(
        "-o",
        "--output",
        type=str,
        default=None,
        help="Output JSON file (required for partial runs)",
    )
    parser.add_argument("--baseline", action="store_true", help="Baseline collection mode: exit 0 regardless of failures")
    parser.add_argument(
        "--lane",
        type=str,
        choices=list(harness.VALID_LANES),
        default="should_succeed",
        help="Test lane to run (default: should_succeed)",
    )
    parser.add_argument("--allow-dirty", action="store_true", help="Allow canonical baseline writes on a dirty working tree")
    parser.add_argument(
        "--max-head-drift-commits",
        type=int,
        default=harness.HEAD_DRIFT_MAX_COMMITS_DEFAULT,
        help=(
            "Warn/fail when HEAD advances by more than this many commits during a run "
            f"(default: {harness.HEAD_DRIFT_MAX_COMMITS_DEFAULT})"
        ),
    )
    parser.add_argument(
        "--fail-on-head-drift",
        action="store_true",
        help=(
            "Exit non-zero when head drift exceeds --max-head-drift-commits "
            f"(exit {harness.HEAD_DRIFT_POLICY_EXIT_CODE})"
        ),
    )
    parser.add_argument(
        "--allow-head-drift",
        action="store_true",
        help="Allow mixed-commit drift on partial runs; output stays provisional",
    )
    parser.add_argument(
        "--check-baseline-freshness",
        action="store_true",
        help=(
            "Check absolute age of canonical baseline files and exit without "
            "running tests. Exit 0 = fresh, exit "
            f"{harness.BASELINE_FRESHNESS_EXIT_CODE} = stale/missing/invalid."
        ),
    )
    parser.add_argument(
        "--max-baseline-age-commits",
        type=int,
        default=harness.BASELINE_MAX_AGE_COMMITS_DEFAULT,
        help=(
            "Maximum commits a canonical baseline may lag behind HEAD before "
            "being considered stale "
            f"(default: {harness.BASELINE_MAX_AGE_COMMITS_DEFAULT})"
        ),
    )
    return parser


def _validate_args(args: argparse.Namespace) -> int | None:
    if args.max_head_drift_commits < 0:
        print("ERROR: --max-head-drift-commits must be >= 0", file=sys.stderr)
        return 3
    if args.max_baseline_age_commits < 0:
        print("ERROR: --max-baseline-age-commits must be >= 0", file=sys.stderr)
        return 3
    return None


def _resolve_head_drift_policy(
    args: argparse.Namespace, *, is_partial: bool
) -> dict[str, Any]:
    return (
        {"max_commits": 0, "fail_on_exceeded": True}
        if is_partial and not args.allow_head_drift
        else {
            "max_commits": args.max_head_drift_commits,
            "fail_on_exceeded": args.fail_on_head_drift,
        }
    )


def _partial_run_routing_safe(head_drift: int | None) -> bool:
    """Partial runs are routing-safe only when drift is confirmed zero."""
    return head_drift == 0


def _print_baseline_freshness_report(
    freshness: dict[str, Any], max_age_commits: int
) -> None:
    status = freshness["status"]
    print(f"Baseline freshness: {status} (max age: {max_age_commits} commits)")
    for lane_name, info in freshness.get("lanes", {}).items():
        age = info.get("age_commits")
        commit = info.get("git_commit", "?")
        lane_status = info.get("status", "?")
        age_str = f"{age} commits behind HEAD" if age is not None else "unknown"
        print(f"  {lane_name}: {lane_status} — {info.get('path')} @ {commit} ({age_str})")


def _maybe_check_baseline_freshness(
    harness: object, args: argparse.Namespace
) -> int | None:
    if not args.check_baseline_freshness:
        return None

    workspace = harness.find_workspace_root()
    freshness = harness.check_baseline_freshness(
        workspace, max_age_commits=args.max_baseline_age_commits
    )
    _print_baseline_freshness_report(
        freshness, max_age_commits=args.max_baseline_age_commits
    )

    if freshness["status"] != "fresh":
        print(
            "\nRemediation: refresh all canonical baselines with:"
            "\n  ./scripts/refresh-baselines.sh"
            "\n\nInspect options and prerequisites with:"
            "\n  ./scripts/refresh-baselines.sh --help"
        )
        return harness.BASELINE_FRESHNESS_EXIT_CODE

    return 0


def _resolve_output_path(
    harness: object,
    args: argparse.Namespace,
    *,
    lane: str,
    is_partial: bool,
) -> str | None:
    needs_explicit_output = is_partial or lane != "should_succeed"
    if args.output is not None:
        return args.output

    if not needs_explicit_output:
        return harness.CANONICAL_OUTPUT

    if is_partial:
        reason = "Partial runs (--filter/--limit)"
        example = "--output /tmp/results-filtered.json"
    else:
        reason = f"Non-default lanes (--lane {lane})"
        lane_output_examples = {
            "should_fail": harness.CANONICAL_SHOULD_FAIL_OUTPUT,
            "examples": harness.CANONICAL_EXAMPLES_OUTPUT,
        }
        suggested_output = lane_output_examples.get(
            lane, f"tests/creusot_compat/results-{lane}.json"
        )
        example = f"--output {suggested_output}"

    print(
        f"ERROR: {reason} require an explicit --output path\n"
        "       to avoid overwriting the canonical baseline results.json.\n"
        f"       Example: {example}",
        file=sys.stderr,
    )
    return None


def _load_dirty_state(
    harness: object,
    args: argparse.Namespace,
    *,
    workspace: Path,
    is_partial: bool,
    output_rel: str,
) -> tuple[list[str], list[str], int | None]:
    is_canonical = not is_partial and (
        harness._is_same_rel_path(output_rel, harness.CANONICAL_OUTPUT)
        or harness._is_same_rel_path(output_rel, harness.CANONICAL_SHOULD_FAIL_OUTPUT)
        or harness._is_same_rel_path(output_rel, harness.CANONICAL_EXAMPLES_OUTPUT)
    )
    dirty_files = harness._get_dirty_files(workspace)
    dirty_files_source = harness._filter_source_dirty_files(dirty_files)

    if is_canonical and dirty_files_source and not args.allow_dirty:
        print(
            "ERROR: Working tree is dirty — canonical baseline would be non-reproducible.\n"
            f"       {len(dirty_files_source)} dirty source file(s): "
            + ", ".join(dirty_files_source[:5])
            + (
                f" (+{len(dirty_files_source) - 5} more)"
                if len(dirty_files_source) > 5
                else ""
            )
            + "\n\n"
            "       Options:\n"
            "         1. Commit or stash changes, then re-run.\n"
            "         2. Pass --allow-dirty to write anyway (metadata will include dirty file list).\n"
            "         3. Use --output <path> for a non-canonical exploratory run.",
            file=sys.stderr,
        )
        return dirty_files, dirty_files_source, 3

    return dirty_files, dirty_files_source, None


def _build_metadata_bundle(
    harness: object,
    args: argparse.Namespace,
    *,
    workspace: Path,
    lane: str,
    output_rel: str,
    dirty_files: list[str],
    dirty_files_source: list[str],
    head_drift_policy: dict[str, Any],
) -> dict[str, Any]:
    all_tests = harness.find_creusot_tests(workspace, lane=lane)
    discovered_count = len(all_tests)

    start_commit = harness._get_git_commit(workspace, dirty_files=dirty_files_source)
    results = harness.run_harness(
        verbose=args.verbose,
        filter_pattern=args.filter,
        limit=args.limit,
        lane=lane,
        timeout_sec=args.timeout,
    )
    executed_count = len(results)

    head_drift = harness._commit_distance_to_head(workspace, start_commit)
    head_drift_exceeded_policy = head_drift is not None and head_drift > head_drift_policy["max_commits"]

    summary = harness.summarize_results(results)
    metadata = harness.build_run_metadata(
        args,
        workspace,
        discovered_count,
        executed_count,
        dirty_files=dirty_files,
        pinned_commit=start_commit,
        head_drift_commits=head_drift,
        head_drift_max_commits=head_drift_policy["max_commits"],
    )
    if metadata["is_partial"]:
        routing_safe = _partial_run_routing_safe(head_drift)
        metadata["routing_safe"] = routing_safe
        if not routing_safe:
            metadata["provisional_reason"] = (
                "head_drift" if head_drift is not None else "head_drift_unavailable"
            )

    lane_pair_freshness, baseline_freshness = _compute_freshness_bundle(
        harness,
        args,
        workspace=workspace,
        lane=lane,
        output_rel=output_rel,
        metadata=metadata,
    )

    return {
        "baseline_freshness": baseline_freshness,
        "discovered_count": discovered_count,
        "executed_count": executed_count,
        "head_drift": head_drift,
        "head_drift_exceeded_policy": head_drift_exceeded_policy,
        "lane_pair_freshness": lane_pair_freshness,
        "metadata": metadata,
        "results": results,
        "start_commit": start_commit,
        "summary": summary,
    }


def _compute_baseline_commit_overrides(
    harness: object, *, lane: str, output_rel: str, metadata: dict[str, Any]
) -> dict[str, str]:
    baseline_commit_overrides: dict[str, str] = {}
    if lane == "should_succeed" and harness._is_same_rel_path(
        output_rel, harness.CANONICAL_OUTPUT
    ):
        baseline_commit_overrides["should_succeed"] = str(metadata["git_commit"])
    elif lane == "should_fail" and harness._is_same_rel_path(
        output_rel, harness.CANONICAL_SHOULD_FAIL_OUTPUT
    ):
        baseline_commit_overrides["should_fail"] = str(metadata["git_commit"])
    elif lane == "examples" and harness._is_same_rel_path(
        output_rel, harness.CANONICAL_EXAMPLES_OUTPUT
    ):
        baseline_commit_overrides["examples"] = str(metadata["git_commit"])
    return baseline_commit_overrides


def _compute_freshness_bundle(
    harness: object,
    args: argparse.Namespace,
    *,
    workspace: Path,
    lane: str,
    output_rel: str,
    metadata: dict[str, Any],
) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    lane_pair_freshness = harness.compute_lane_pair_freshness(
        workspace=workspace,
        lane=lane,
        output_rel=output_rel,
        is_partial=metadata["is_partial"],
        current_git_commit=metadata["git_commit"],
    )
    freshness_eval_head = harness._get_git_commit(workspace)
    if lane_pair_freshness is not None:
        metadata["lane_pair_freshness"] = harness._snapshot_freshness_for_metadata(
            lane_pair_freshness,
            evaluated_against_head=freshness_eval_head,
        )

    baseline_commit_overrides = _compute_baseline_commit_overrides(
        harness, lane=lane, output_rel=output_rel, metadata=metadata
    )
    baseline_freshness = harness.check_baseline_freshness(
        workspace,
        max_age_commits=args.max_baseline_age_commits,
        commit_overrides=baseline_commit_overrides or None,
    )
    metadata["baseline_freshness"] = harness._snapshot_freshness_for_metadata(
        baseline_freshness,
        evaluated_against_head=freshness_eval_head,
    )
    return lane_pair_freshness, baseline_freshness


def main(*, facade: object | None = None) -> int:
    harness = _resolve_harness_facade(facade)
    parser = _build_parser(harness)
    args = parser.parse_args()

    arg_error = _validate_args(args)
    if arg_error is not None:
        return arg_error

    freshness_status = _maybe_check_baseline_freshness(harness, args)
    if freshness_status is not None:
        return freshness_status

    lane = args.lane
    is_partial = args.filter is not None or args.limit is not None
    head_drift_policy = _resolve_head_drift_policy(args, is_partial=is_partial)
    output_rel = _resolve_output_path(harness, args, lane=lane, is_partial=is_partial)
    if output_rel is None:
        return 3

    workspace = harness.find_workspace_root()
    dirty_files, dirty_files_source, dirty_gate_error = _load_dirty_state(
        harness,
        args,
        workspace=workspace,
        is_partial=is_partial,
        output_rel=output_rel,
    )
    if dirty_gate_error is not None:
        return dirty_gate_error

    print("Creusot Compatibility Test Harness")
    print("=" * 40)

    bundle = _build_metadata_bundle(
        harness,
        args,
        workspace=workspace,
        lane=lane,
        output_rel=output_rel,
        dirty_files=dirty_files,
        dirty_files_source=dirty_files_source,
        head_drift_policy=head_drift_policy,
    )

    _print_summary(lane, bundle["summary"])
    _print_policy_notes(args, bundle)

    _write_results_file(
        workspace,
        output_rel,
        metadata=bundle["metadata"],
        summary=bundle["summary"],
        results=bundle["results"],
    )

    return _determine_exit_code(
        harness,
        args,
        bundle["summary"],
        is_partial=is_partial,
        head_drift_exceeded_policy=bundle["head_drift_exceeded_policy"],
        fail_on_head_drift=head_drift_policy["fail_on_exceeded"],
        routing_safe=bundle["metadata"].get("routing_safe"),
    )
