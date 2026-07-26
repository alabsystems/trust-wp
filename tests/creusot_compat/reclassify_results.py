#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Reclassify existing results.json with the current classifier code.

When the classifier logic in harness_classify.py evolves (e.g., new skip
patterns, improved marker detection, panic-exit handling), existing baseline
results become stale — test statuses may no longer match what the current
classifier would produce.

This script re-runs classify_failure() on the stored output text without
re-running verification, producing an updated results.json that reflects
the current classification logic.

Usage:
    python3 tests/creusot_compat/reclassify_results.py
    python3 tests/creusot_compat/reclassify_results.py --dry-run
    python3 tests/creusot_compat/reclassify_results.py -o results-reclassified.json
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Ensure sibling imports work when run as a script.
_SELF_DIR = Path(__file__).resolve().parent
if str(_SELF_DIR) not in sys.path:
    sys.path.insert(0, str(_SELF_DIR))

from harness_classify import (  # noqa: E402
    BACKEND_PASS_PREFIX,
    NO_REPLAY_PASS_PREFIX,
    NO_REPLAY_STRICT_ERROR_MESSAGE,
    STRICT_PASS_PREFIX,
    _check_backend_superseded,
    _has_timeout_caused_errors,
    _is_no_replay_source,
    classify_error_category,
    classify_failure,
    classify_no_replay_result,
    classify_should_fail_result,
    classify_unknown_category,
)
from harness_baseline import TRUNCATED_OUTPUT_MARKER, TRUNCATED_OUTPUT_SENTINEL
from harness_verification_tier import classify_verification_tier  # noqa: E402


def _find_workspace_root() -> Path:
    """Walk up from script dir to find Cargo.toml workspace root."""
    d = _SELF_DIR
    while d != d.parent:
        if (d / "Cargo.toml").exists() and (d / "crates").is_dir():
            return d
        d = d.parent
    return _SELF_DIR.parent.parent


def _read_source(workspace: Path, test_name: str) -> str:
    """Read the Creusot test source file for classification context."""
    source_path = workspace / "reference" / "creusot" / test_name
    if source_path.exists():
        return source_path.read_text()
    return ""


def _extract_exit_code(message: str) -> int | None:
    """Extract exit code from the stored test output message.

    Handles two formats:
    - ``exit status: N`` — legacy harness output suffix
    - ``base_exit_code=N`` — TRUST_WP_RESULT wire line (#2690)
    """
    match = re.search(r"exit status:\s*(\d+)", message)
    if match:
        return int(match.group(1))
    # Fall back to the wire-format base_exit_code emitted by cargo-trust-wp.
    wire_match = re.search(r"base_exit_code=(\d+)", message)
    if wire_match:
        return int(wire_match.group(1))
    return None


def _message_is_truncated(entry: dict[str, object]) -> bool:
    """Stored truncated output is unsafe to replay through the classifier."""
    explicit_flag = entry.get("message_truncated")
    if explicit_flag is not None:
        return bool(explicit_flag)

    # Older artifacts do not have explicit truncation metadata, so fall back to
    # the legacy sentinel check for backwards compatibility.
    message = entry.get("message", "") or ""
    return TRUNCATED_OUTPUT_SENTINEL in str(message)


def _message_with_stored_telemetry(message: str, entry: dict[str, object]) -> str:
    """Append stored TRUST_WP_RESULT telemetry before tier classification."""
    telemetry = entry.get("telemetry")
    if not isinstance(telemetry, dict):
        return message

    fields = []
    for key in sorted(telemetry):
        value = telemetry[key]
        if isinstance(value, bool):
            continue
        try:
            fields.append(f"{key}={int(value)}")
        except (TypeError, ValueError):
            continue
    if not fields:
        return message
    return f"{message}\nTRUST_WP_RESULT:v1 {' '.join(fields)}"


def reclassify(
    results_path: Path,
    workspace: Path,
    *,
    dry_run: bool = False,
    output_path: Path | None = None,
) -> dict:
    """Reclassify results and backfill verification tiers.

    Status reclassification applies to non-pass results only (unchanged).
    Verification tier backfill applies to **every** entry including passes,
    so that the canonical artifact exposes the new metric (#2510).
    """
    with open(results_path) as f:
        data = json.load(f)

    status_changes: list[dict] = []
    tier_changes: list[dict] = []
    category_backfills: list[dict] = []
    results = data["results"]

    for entry in results:
        old_status = entry["status"]
        old_skip = entry.get("skip_reason")
        name = entry["name"]
        message = entry.get("message", "") or ""
        source = _read_source(workspace, name)
        is_no_replay = (
            _is_no_replay_source(source)
            or message.startswith(NO_REPLAY_PASS_PREFIX)
        )

        # --- Status reclassification ---
        # Non-pass results are always re-examined.
        # For should-fail tests, "pass" results are ALSO re-examined because
        # they may be false-accepts (trust-wp verified code that should fail)
        # that were misclassified as "correctly rejected" by a prior
        # classifier with an exit-code extraction gap (#2690).
        is_should_fail = name.startswith("tests/should_fail/")
        needs_reclass = (
            old_status != "pass"
            or (old_status == "pass" and is_no_replay)
            or (is_should_fail and old_status == "pass" and message != "Correctly rejected")
        )
        is_truncated = _message_is_truncated(entry)

        # Truncation-safe timeout reclassification (#2690): timeout
        # signals ("hard timeout expired", "unknown (timeout)", wire
        # line) survive output truncation because they appear at the
        # tail.  Reclassify truncated unknowns to "error" (timeout)
        # without full classifier replay.
        #
        # Guard (#2690): do NOT convert "fail" to "error" when the
        # truncated output contains genuine FAILED markers.  A test
        # with both failures and timeouts should remain "fail" since
        # the dominant signal is "functions failed", not "timeout".
        # Only reclassify "fail" -> "error" if no FAILED lines survive.
        _has_genuine_fail = (
            old_status == "fail"
            and any(
                "FAILED" in line
                for line in message.split("\n")
                if "trust-wp:" in line
            )
        )
        if (
            is_truncated
            and needs_reclass
            and old_skip != "timeout"
            and old_status in ("unknown", "fail")
            and _has_timeout_caused_errors(message)
            and not _has_genuine_fail
        ):
            exit_code = _extract_exit_code(message)
            new_status = "error"
            new_skip = None
            new_error_cat = "timeout"
            if new_status != old_status or new_skip != old_skip:
                status_changes.append({
                    "test": name,
                    "old_status": old_status,
                    "new_status": new_status,
                    "old_skip_reason": old_skip,
                    "new_skip_reason": new_skip,
                })
                if not dry_run:
                    entry["status"] = new_status
                    entry["skip_reason"] = new_skip
                    entry["error_category"] = new_error_cat
            # Skip to verification tier backfill (below) after timeout reclass.

        elif needs_reclass and old_skip != "timeout" and not is_truncated:
            exit_code = _extract_exit_code(message)

            # Guard: do not reclassify should-fail skips whose stored
            # output shows clean verification (exit_code==0).  When a
            # known-divergence entry is removed because the fix landed,
            # the stored output is stale and still shows success.
            # Reclassifying based on stale output would incorrectly
            # mark these as false-accepts.  They need re-running, not
            # reclassification (#2690).
            # Exception (#2686): backend-superseded tests CAN be reclassified
            # from skip to pass because the classifier recognizes them by name.
            if (
                is_should_fail
                and old_status == "skip"
                and old_skip
                and exit_code == 0
                and _check_backend_superseded(name) is None
            ):
                pass  # skip status reclassification, fall through to tier backfill
            else:
                if not is_should_fail and is_no_replay:
                    new_status, new_skip = classify_no_replay_result(
                        message, exit_code=exit_code, test_name=name
                    )
                elif is_should_fail:
                    # should_fail tests use a different classifier that treats
                    # non-success as "correctly rejected" (pass) by default.
                    # The success flag is inferred: exit_code==0 means success.
                    success = exit_code == 0
                    new_status, new_skip = classify_should_fail_result(
                        success, message, source, name, exit_code=exit_code
                    )
                else:
                    # Pass test_name so name-keyed classifier tables (the
                    # NO_REPLAY translate-only allowlist and the spurious-PA
                    # counterexample table) apply identically offline and in
                    # the live harness (harness_runner passes it too).
                    new_status, new_skip = classify_failure(
                        message, source, exit_code=exit_code, test_name=name
                    )
                if new_status == "error":
                    new_error_cat = (
                        "strict_gate"
                        if is_no_replay
                        else classify_error_category(message, exit_code)
                    )
                elif new_status == "unknown":
                    new_error_cat = classify_unknown_category(message)
                else:
                    new_error_cat = None

                if new_status != old_status or new_skip != old_skip:
                    status_changes.append({
                        "test": name,
                        "old_status": old_status,
                        "new_status": new_status,
                        "old_skip_reason": old_skip,
                        "new_skip_reason": new_skip,
                    })
                    if not dry_run:
                        entry["status"] = new_status
                        entry["skip_reason"] = new_skip
                        # Update message for should_fail pass transitions (#2686).
                        if is_should_fail and new_status == "pass":
                            backend_reason = _check_backend_superseded(name)
                            if backend_reason is not None:
                                entry["message"] = f"{BACKEND_PASS_PREFIX} {backend_reason}"
                            else:
                                entry["message"] = "Correctly rejected"
                        elif is_no_replay and new_status == "error":
                            entry["message"] = NO_REPLAY_STRICT_ERROR_MESSAGE

                old_error_cat = entry.get("error_category")
                if new_error_cat != old_error_cat:
                    if new_error_cat is not None:
                        category_backfills.append({
                            "test": name,
                            "old_category": old_error_cat,
                            "new_category": new_error_cat,
                        })
                if not dry_run:
                    if new_error_cat is not None:
                        entry["error_category"] = new_error_cat
                    elif "error_category" in entry:
                        del entry["error_category"]

        # --- Error category backfill for unknown status (#2690) ---
        # Entries with status "unknown" that lack an error_category get
        # one computed from the stored output.  This is analogous to the
        # tier backfill below — it applies to all unknown entries, not
        # just those whose status changed during reclassification.
        # This catches entries that were already "unknown" but went through
        # the is_should_fail/skip guard path above and didn't enter the
        # reclassification branch.
        #
        # Unlike status reclassification, unknown sub-classification is
        # safe on truncated output: the per-function "trust-wp: X unknown (Y)"
        # lines that survive truncation carry the diagnostic category.
        effective_status = entry["status"]
        if (
            effective_status == "unknown"
            and not entry.get("error_category")
        ):
            backfill_cat = classify_unknown_category(message)
            if backfill_cat:
                category_backfills.append({
                    "test": name,
                    "old_category": None,
                    "new_category": backfill_cat,
                })
                if not dry_run:
                    entry["error_category"] = backfill_cat

        # --- Verification tier backfill (all entries, #2510) ---
        effective_message = entry.get("message", "") or ""
        effective_message = _message_with_stored_telemetry(str(effective_message), entry)
        effective_skip = entry.get("skip_reason")
        new_tier = classify_verification_tier(
            name, effective_status, effective_message, effective_skip, source,
        )
        old_tier = entry.get("verification_tier")
        if new_tier != old_tier:
            tier_changes.append({
                "test": name,
                "old_tier": old_tier,
                "new_tier": new_tier,
            })
            if not dry_run:
                if new_tier is not None:
                    entry["verification_tier"] = new_tier
                elif "verification_tier" in entry:
                    del entry["verification_tier"]

    # Check if should_fail lane needs false_accept_count backfill (#2690).
    summary = data.get("summary", {})
    sf_summary = summary.get("should_fail", {})
    needs_fa_backfill = (
        bool(sf_summary) and "false_accept_count" not in sf_summary
    )

    has_mutations = (
        bool(status_changes)
        or bool(tier_changes)
        or bool(category_backfills)
        or needs_fa_backfill
    )
    if has_mutations and not dry_run:
        _recompute_and_write(
            data, status_changes, tier_changes, output_path or results_path,
        )

    return {
        "total_results": len(results),
        "reclassified": len(status_changes),
        "tier_backfilled": len(tier_changes),
        "category_backfilled": len(category_backfills),
        "changes": status_changes,
        "tier_changes": tier_changes,
        "category_backfills": category_backfills,
    }


def _recompute_and_write(
    data: dict,
    status_changes: list[dict],
    tier_changes: list[dict],
    dest: Path,
) -> None:
    """Recompute summary counts (including tiers) and write updated results."""
    results = data["results"]
    summary = data.get("summary", {})
    status_counts = {"pass": 0, "fail": 0, "unknown": 0, "skip": 0, "error": 0}
    skip_reasons: dict[str, int] = {}

    error_categories: dict[str, int] = {}
    for entry in results:
        s = entry["status"]
        status_counts[s] = status_counts.get(s, 0) + 1
        sr = entry.get("skip_reason")
        if sr:
            skip_reasons[sr] = skip_reasons.get(sr, 0) + 1
        ec = entry.get("error_category")
        if ec:
            error_categories[ec] = error_categories.get(ec, 0) + 1

    strict_pass = sum(
        1 for e in results
        if e["status"] == "pass"
        and (e.get("message") or "").startswith(STRICT_PASS_PREFIX)
    )
    no_replay_pass = sum(
        1 for e in results
        if e["status"] == "pass"
        and (e.get("message") or "").startswith(NO_REPLAY_PASS_PREFIX)
    )
    backend_superseded_pass = sum(
        1 for e in results
        if e["status"] == "pass"
        and (e.get("message") or "").startswith(BACKEND_PASS_PREFIX)
    )
    summary.update(status_counts)
    summary["strict_pass"] = strict_pass
    summary["no_replay_pass"] = no_replay_pass
    summary["backend_superseded_pass"] = backend_superseded_pass
    summary["skip_reasons"] = skip_reasons
    if error_categories:
        summary["error_categories"] = error_categories
    summary["total"] = len(results)

    # Recompute verification tier counts (#2510).
    _recompute_tier_summary(results, summary)

    # Recompute lane sub-summaries from per-lane test membership.
    for lane in ("should_succeed", "should_fail"):
        if lane not in summary:
            continue
        _recompute_lane_summary(results, summary, lane)
    data["summary"] = summary

    metadata = data.setdefault("metadata", {})
    metadata["reclassified_from_commit"] = metadata.get("git_commit", "unknown")

    note_parts = []
    if status_changes:
        note_parts.append(f"reclassified {len(status_changes)} statuses")
    if tier_changes:
        note_parts.append(f"backfilled {len(tier_changes)} verification tiers")
    metadata["reclassification_note"] = (
        "; ".join(note_parts) + " (no re-run, output text preserved)"
    )

    with open(dest, "w") as f:
        json.dump(data, f, indent=2)
        f.write("\n")


def _recompute_tier_summary(results: list[dict], summary: dict) -> None:
    """Recompute verification_tiers, tier2_verified, and tier2_rate."""
    tier_counts: dict[str, int] = {
        "tier0": 0, "tier1": 0, "tier2": 0, "tier3": 0, "legacy_unknown": 0,
    }
    for entry in results:
        vtier = entry.get("verification_tier")
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


def _recompute_lane_summary(
    results: list[dict], summary: dict, lane: str,
) -> None:
    """Recompute per-lane sub-summary including tier counts."""
    lane_segment = f"/{lane}/"
    lane_counts = {"pass": 0, "fail": 0, "unknown": 0, "skip": 0, "error": 0}
    lane_skip: dict[str, int] = {}
    lane_error_cats: dict[str, int] = {}
    lane_total = 0
    for entry in results:
        if lane_segment not in entry.get("name", ""):
            continue
        lane_total += 1
        lane_counts[entry["status"]] = lane_counts.get(entry["status"], 0) + 1
        sr = entry.get("skip_reason")
        if sr:
            lane_skip[sr] = lane_skip.get(sr, 0) + 1
        ec = entry.get("error_category")
        if ec:
            lane_error_cats[ec] = lane_error_cats.get(ec, 0) + 1
    lane_strict = sum(
        1 for e in results
        if lane_segment in e.get("name", "")
        and e["status"] == "pass"
        and (e.get("message") or "").startswith(STRICT_PASS_PREFIX)
    )
    lane_no_replay = sum(
        1 for e in results
        if lane_segment in e.get("name", "")
        and e["status"] == "pass"
        and (e.get("message") or "").startswith(NO_REPLAY_PASS_PREFIX)
    )
    lane_backend_superseded = sum(
        1 for e in results
        if lane_segment in e.get("name", "")
        and e["status"] == "pass"
        and (e.get("message") or "").startswith(BACKEND_PASS_PREFIX)
    )
    lane_summary = summary[lane]
    lane_summary.update(lane_counts)
    lane_summary["strict_pass"] = lane_strict
    lane_summary["no_replay_pass"] = lane_no_replay
    lane_summary["backend_superseded_pass"] = lane_backend_superseded
    lane_summary["skip_reasons"] = lane_skip
    if lane_error_cats:
        lane_summary["error_categories"] = lane_error_cats
    lane_summary["total"] = lane_total

    # Per-lane tier counts.
    lane_tier_counts: dict[str, int] = {
        "tier0": 0, "tier1": 0, "tier2": 0, "tier3": 0, "legacy_unknown": 0,
    }
    for entry in results:
        if lane_segment not in entry.get("name", ""):
            continue
        vtier = entry.get("verification_tier")
        if vtier is not None and vtier in lane_tier_counts:
            lane_tier_counts[vtier] += 1
    lane_summary["verification_tiers"] = lane_tier_counts
    lane_summary["tier2_verified"] = lane_tier_counts["tier2"]
    t2_t3 = lane_tier_counts["tier2"] + lane_tier_counts["tier3"]
    lane_summary["tier2_rate"] = (
        round(lane_tier_counts["tier2"] / t2_t3, 4) if t2_t3 > 0 else None
    )

    # False-accept count for should_fail lane (#2690).
    if lane == "should_fail":
        from harness_classify_fail import _KNOWN_FALSE_ACCEPT_TESTS
        known_fa_names = set(_KNOWN_FALSE_ACCEPT_TESTS.keys())
        known_fa_count = sum(
            1 for e in results
            if lane_segment in e.get("name", "")
            and e["status"] == "skip"
            and e.get("name", "") in known_fa_names
        )
        actual_fa_count = sum(
            1 for e in results
            if lane_segment in e.get("name", "")
            and e["status"] == "fail"
        )
        lane_summary["false_accept_count"] = known_fa_count + actual_fa_count


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Reclassify results.json with current classifier logic"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Show what would change without writing",
    )
    parser.add_argument(
        "-o", "--output",
        type=str,
        default=None,
        help="Output path (default: overwrite input)",
    )
    parser.add_argument(
        "input",
        nargs="?",
        default=str(_SELF_DIR / "results.json"),
        help="Input results.json path",
    )
    args = parser.parse_args()

    results_path = Path(args.input)
    if not results_path.exists():
        print(f"ERROR: {results_path} not found", file=sys.stderr)
        return 1

    workspace = _find_workspace_root()
    output_path = Path(args.output) if args.output else None

    report = reclassify(
        results_path, workspace, dry_run=args.dry_run, output_path=output_path
    )

    has_any_changes = (
        report["changes"] or report["tier_changes"] or report.get("category_backfills")
    )
    if not has_any_changes:
        print("No classification, tier, or category changes detected.")
        return 0

    if report["changes"]:
        print(f"Reclassified {report['reclassified']} / {report['total_results']} tests:")
        print()
        for c in report["changes"]:
            old = c["old_status"]
            new = c["new_status"]
            reason = f" ({c['new_skip_reason']})" if c.get("new_skip_reason") else ""
            print(f"  {c['test']:50s} {old:6s} -> {new}{reason}")

    if report.get("category_backfills"):
        print(f"\nBackfilled {report['category_backfilled']} unknown categories:")
        print()
        for cb in report["category_backfills"]:
            print(f"  {cb['test']:50s} -> {cb['new_category']}")

    if report["tier_changes"]:
        print(f"\nBackfilled {report['tier_backfilled']} verification tiers:")
        print()
        for tc in report["tier_changes"][:20]:
            old_t = tc["old_tier"] or "(none)"
            new_t = tc["new_tier"] or "(none)"
            print(f"  {tc['test']:50s} {old_t:16s} -> {new_t}")
        if len(report["tier_changes"]) > 20:
            print(f"  ... and {len(report['tier_changes']) - 20} more")

    if args.dry_run:
        print(f"\n(dry run — no files written)")
    else:
        dest = output_path or results_path
        print(f"\nWritten to {dest}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
