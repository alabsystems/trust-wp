#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Reporting/output helpers for the Creusot compatibility harness CLI."""

from __future__ import annotations

import datetime
import json
from pathlib import Path
from typing import Any


def _print_summary(lane: str, summary: dict[str, Any]) -> None:
    print()
    print(f"Summary (lane: {lane}):")
    print(f"  Total:   {summary['total']}")
    print(f"  Pass:    {summary['pass']}")
    print(f"  Fail:    {summary['fail']}")
    print(f"  Unknown: {summary['unknown']}")
    print(f"  Skip:    {summary['skip']}")
    print(f"  Error:   {summary['error']}")

    for lane_key in ("should_succeed", "should_fail", "examples"):
        if lane_key not in summary:
            continue
        lane_summary = summary[lane_key]
        print(f"\n  {lane_key}:")
        print(f"    Total:   {lane_summary['total']}")
        print(f"    Pass:    {lane_summary['pass']}")
        print(f"    Fail:    {lane_summary['fail']}")
        print(f"    Unknown: {lane_summary['unknown']}")
        print(f"    Skip:    {lane_summary['skip']}")
        print(f"    Error:   {lane_summary['error']}")
        # Show false-accept count for should_fail lane (#2690)
        fa_count = lane_summary.get("false_accept_count")
        if fa_count is not None:
            print(f"    False-accepts: {fa_count} (known unsoundness gaps)")
        # Show backend-superseded pass count for should_fail lane (#2686)
        bs_count = lane_summary.get("backend_superseded_pass")
        if bs_count is not None and bs_count > 0:
            print(f"    Backend-superseded: {bs_count} (trust-wp handles code Why3 cannot)")

    # Show error categories if present (#2690)
    error_cats = summary.get("error_categories", {})
    if error_cats:
        print()
        print("Error categories:")
        for cat, count in sorted(error_cats.items(), key=lambda item: -item[1]):
            print(f"  {cat}: {count}")

    # Show unknown sub-categories if present (#2690)
    unknown_cats = summary.get("unknown_categories", {})
    if unknown_cats:
        print()
        print("Unknown categories:")
        for cat, count in sorted(unknown_cats.items(), key=lambda item: -item[1]):
            print(f"  {cat}: {count}")

    if summary["skip_reasons"]:
        print()
        print("Skip reasons:")
        for reason, count in sorted(
            summary["skip_reasons"].items(), key=lambda item: -item[1]
        ):
            print(f"  {reason}: {count}")


def _print_partial_run_notes(
    args: Any,
    bundle: dict[str, Any],
    head_drift: int | None,
) -> None:
    if not bundle["metadata"]["is_partial"]:
        return

    print(
        f"\n  [PARTIAL RUN] {bundle['executed_count']}/{bundle['discovered_count']} "
        "tests executed"
    )
    if args.allow_head_drift and bundle["metadata"].get("routing_safe") is False:
        if head_drift is None:
            print(
                "\n[PROVISIONAL PARTIAL RUN] HEAD drift could not be evaluated; "
                "do not use for routing claims."
            )
        else:
            print(
                "\n[PROVISIONAL PARTIAL RUN] HEAD drift detected; do not use for routing claims."
            )
    if bundle["metadata"].get("routing_safe") is False and head_drift is None:
        print(
            "\n[HEAD DRIFT WARNING] Unable to evaluate HEAD drift during run."
            "\n  Policy requires confirmed zero drift for routing-safe partial runs."
        )


def _print_policy_notes(
    args: Any,
    bundle: dict[str, Any],
) -> None:
    head_drift = bundle["head_drift"]
    _print_partial_run_notes(args, bundle, head_drift)

    policy_max_commits = bundle["metadata"].get(
        "head_drift_max_commits", args.max_head_drift_commits
    )
    if bundle["head_drift_exceeded_policy"]:
        print(
            f"\n[HEAD DRIFT WARNING] HEAD advanced {head_drift} commit(s) during run"
            f" (policy max: {policy_max_commits})."
            f"\n  Baseline pinned to start commit: {bundle['start_commit']}"
            "\n  Results may not reflect code at current HEAD."
        )
    elif head_drift is not None and head_drift > 0 and args.verbose:
        print(
            f"\n[HEAD DRIFT NOTE] HEAD advanced {head_drift} commit(s) during run"
            f" (within policy max: {policy_max_commits})."
            f"\n  Baseline pinned to start commit: {bundle['start_commit']}"
        )

    lane_pair_freshness = bundle["lane_pair_freshness"]
    if lane_pair_freshness is not None:
        status = lane_pair_freshness.get("status")
        if status == "stale":
            print(
                "\n[LANE FRESHNESS WARNING] "
                f"{lane_pair_freshness['current_lane']} age="
                f"{lane_pair_freshness['current_age_commits']} commits, "
                f"{lane_pair_freshness['paired_lane']} age="
                f"{lane_pair_freshness['paired_age_commits']} commits, "
                f"gap={lane_pair_freshness['age_gap_commits']} "
                f"(max={lane_pair_freshness['max_age_gap_commits']})."
            )
            print(
                "  Refresh paired canonical lane baseline: "
                f"{lane_pair_freshness['paired_output']}"
            )
        elif status == "unknown":
            print(
                "\n[LANE FRESHNESS CHECK] unable to evaluate canonical lane pair: "
                f"{lane_pair_freshness.get('reason', 'unknown reason')}"
            )

    baseline_freshness = bundle["baseline_freshness"]
    baseline_status = baseline_freshness.get("status")
    if baseline_status and baseline_status != "fresh":
        print(
            f"\n[BASELINE AGE WARNING] Canonical baselines are {baseline_status}"
            f" (max age: {args.max_baseline_age_commits} commits)."
        )
        for lane_name, info in baseline_freshness.get("lanes", {}).items():
            age = info.get("age_commits")
            lane_status = info.get("status", "?")
            age_str = f"{age} commits" if age is not None else "unknown"
            print(f"  {lane_name}: {lane_status} (age={age_str})")
        print("  Refresh: ./scripts/refresh-baselines.sh")


def _write_results_file(
    workspace: Path,
    output_rel: str,
    *,
    metadata: dict[str, Any],
    summary: dict[str, Any],
    results: list[Any],
) -> None:
    output_path = workspace / output_rel
    output_path.parent.mkdir(parents=True, exist_ok=True)

    timestamp = datetime.datetime.fromisoformat(metadata["timestamp"])
    generated_at = timestamp.strftime("%Y-%m-%dT%H:%M:%SZ")

    result_dicts = []
    for result in results:
        entry: dict[str, Any] = {
            "name": result.name,
            "status": result.status,
            "message": result.message,
            "duration_ms": result.duration_ms,
            "skip_reason": result.skip_reason,
        }
        error_cat = getattr(result, "error_category", None)
        if error_cat is not None:
            entry["error_category"] = error_cat
        if getattr(result, "message_truncated", False):
            entry["message_truncated"] = True
        vtier = getattr(result, "verification_tier", None)
        if vtier is not None:
            entry["verification_tier"] = vtier
        telemetry = getattr(result, "telemetry", None)
        if telemetry is not None:
            entry["telemetry"] = telemetry.to_dict()
        result_dicts.append(entry)

    output_data = {
        "generated_at": generated_at,
        "metadata": metadata,
        "summary": summary,
        "results": result_dicts,
    }

    output_path.write_text(json.dumps(output_data, indent=2))
    print(f"\nResults written to {output_path}")


def _determine_exit_code(
    harness: Any,
    args: Any,
    summary: dict[str, Any],
    *,
    is_partial: bool,
    head_drift_exceeded_policy: bool,
    fail_on_head_drift: bool,
    routing_safe: bool | None,
) -> int:
    if is_partial and fail_on_head_drift and routing_safe is False:
        return harness.HEAD_DRIFT_POLICY_EXIT_CODE
    if fail_on_head_drift and head_drift_exceeded_policy:
        return harness.HEAD_DRIFT_POLICY_EXIT_CODE
    if args.baseline:
        return 0

    has_failures = summary["fail"] > 0 or summary["unknown"] > 0 or summary["error"] > 0
    return 1 if has_failures else 0
