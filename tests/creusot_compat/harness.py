#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Creusot compatibility test harness for trust-wp.

This module is a sealed compatibility facade — all implementation lives in
extracted ``harness_*`` modules.  It re-exports every symbol that tests
access via ``harness.X`` or monkeypatch, and injects the facade object that
lets extracted modules call back into sibling functions.

Usage:
    python3 tests/creusot_compat/harness.py [--verbose] [--filter PATTERN]

Output:
    tests/creusot_compat/results.json - Test results per file
"""

from __future__ import annotations

import argparse
import functools
import os
import subprocess
import sys
from pathlib import Path
from types import SimpleNamespace

# ---------------------------------------------------------------------------
# Module imports (try package-relative, fall back to bare for script mode)
# ---------------------------------------------------------------------------
try:
    from tests.creusot_compat import (
        harness_baseline, harness_classify, harness_cli,
        harness_disk as _harness_disk, harness_model,
        harness_project, harness_runner, harness_targets,
        harness_verification_tier as _harness_verification_tier,
    )
except ModuleNotFoundError:
    import harness_baseline  # type: ignore[no-redef]
    import harness_classify  # type: ignore[no-redef]
    import harness_cli  # type: ignore[no-redef]
    import harness_disk as _harness_disk  # type: ignore[no-redef]
    import harness_model  # type: ignore[no-redef]
    import harness_project  # type: ignore[no-redef]
    import harness_runner  # type: ignore[no-redef]
    import harness_targets  # type: ignore[no-redef]
    import harness_verification_tier as _harness_verification_tier  # type: ignore[no-redef]

# ---------------------------------------------------------------------------
# Constants & types (from harness_model) — must be in globals() for facade
# ---------------------------------------------------------------------------
BASELINE_FRESHNESS_EXIT_CODE = harness_model.BASELINE_FRESHNESS_EXIT_CODE
BASELINE_MAX_AGE_COMMITS_DEFAULT = harness_model.BASELINE_MAX_AGE_COMMITS_DEFAULT
CANONICAL_OUTPUT = harness_model.CANONICAL_OUTPUT
CANONICAL_SHOULD_FAIL_OUTPUT = harness_model.CANONICAL_SHOULD_FAIL_OUTPUT
CANONICAL_EXAMPLES_OUTPUT = harness_model.CANONICAL_EXAMPLES_OUTPUT
DISK_WARNING_THRESHOLD_PERCENT = harness_model.DISK_WARNING_THRESHOLD_PERCENT
HARNESS_TEMP_TARGET_PREFIX = harness_model.HARNESS_TEMP_TARGET_PREFIX
HEAD_DRIFT_MAX_COMMITS_DEFAULT = harness_model.HEAD_DRIFT_MAX_COMMITS_DEFAULT
HEAD_DRIFT_POLICY_EXIT_CODE = harness_model.HEAD_DRIFT_POLICY_EXIT_CODE
LANE_PAIR_MAX_AGE_GAP_COMMITS = harness_model.LANE_PAIR_MAX_AGE_GAP_COMMITS
PARSE_FAILURE_PATTERNS = harness_model.PARSE_FAILURE_PATTERNS
STALE_HARNESS_TEMP_MAX_AGE_HOURS = harness_model.STALE_HARNESS_TEMP_MAX_AGE_HOURS
VALID_LANES = harness_model.VALID_LANES
WIRE_PREFIX = harness_model.WIRE_PREFIX
TestResult = harness_model.TestResult
VerificationTelemetry = harness_model.VerificationTelemetry
parse_wire_line = harness_model.parse_wire_line
TRUNCATED_OUTPUT_MARKER = harness_baseline.TRUNCATED_OUTPUT_MARKER
TRUNCATED_OUTPUT_SENTINEL = harness_baseline.TRUNCATED_OUTPUT_SENTINEL

# ---------------------------------------------------------------------------
# Classifier re-exports (identity-preserving — tests use ``is`` checks)
# ---------------------------------------------------------------------------
BACKEND_PASS_PREFIX = harness_classify.BACKEND_PASS_PREFIX
NO_REPLAY_PASS_PREFIX = harness_classify.NO_REPLAY_PASS_PREFIX
NO_REPLAY_STRICT_ERROR_MESSAGE = harness_classify.NO_REPLAY_STRICT_ERROR_MESSAGE
STRICT_PASS_PREFIX = harness_classify.STRICT_PASS_PREFIX
_KNOWN_BACKEND_SUPERSEDED_TESTS = harness_classify._KNOWN_BACKEND_SUPERSEDED_TESTS
_KNOWN_STRICT_REJECTION_TESTS = harness_classify._KNOWN_STRICT_REJECTION_TESTS
_check_backend_superseded = harness_classify._check_backend_superseded
_all_contracts_axiomatized = harness_classify._all_contracts_axiomatized
_dropped_obligation_warning_count = harness_classify._dropped_obligation_warning_count
_has_cargo_lock_contention = harness_classify._has_cargo_lock_contention
_has_panic_exit_status = harness_classify._has_panic_exit_status
_has_rustc_panic = harness_classify._has_rustc_panic
_has_timeout_caused_errors = harness_classify._has_timeout_caused_errors
_has_verification_failures = harness_classify._has_verification_failures
_has_verified_contracts = harness_classify._has_verified_contracts
_is_no_replay_source = harness_classify._is_no_replay_source
_is_should_fail_test = harness_classify._is_should_fail_test
_source_has_user_contracts = harness_classify._source_has_user_contracts
_last_contract_count = harness_classify._last_contract_count
_last_proof_assert_summary_counts = harness_classify._last_proof_assert_summary_counts
_last_verification_summary_counts = harness_classify._last_verification_summary_counts
_verification_run_succeeded = harness_classify._verification_run_succeeded
_wire_line_shows_pa_only_failure = harness_classify._wire_line_shows_pa_only_failure
classify_error_category = harness_classify.classify_error_category
classify_failure = harness_classify.classify_failure
classify_no_replay_result = harness_classify.classify_no_replay_result
classify_should_fail_result = harness_classify.classify_should_fail_result
classify_unknown_category = harness_classify.classify_unknown_category

# ---------------------------------------------------------------------------
# Verification tier re-exports (#2510)
# ---------------------------------------------------------------------------
VerificationTier = _harness_verification_tier.VerificationTier
classify_verification_tier = _harness_verification_tier.classify_verification_tier
source_has_verification_surface = _harness_verification_tier.source_has_verification_surface

# ---------------------------------------------------------------------------
# Runner internal delegates (tests monkeypatch _runner_run_harness)
# ---------------------------------------------------------------------------
_runner_ensure_harness_binaries = harness_runner.ensure_harness_binaries
_runner_run_trust_wp_on_project = harness_runner.run_trust_wp_on_project
_runner_run_harness = harness_runner.run_harness
_runner_setup_trust_wp_rustc_wrapper = harness_runner.setup_trust_wp_rustc_wrapper
_cli_main = harness_cli.main


# ---------------------------------------------------------------------------
# Facade machinery
# ---------------------------------------------------------------------------
def _current_facade() -> object:
    return SimpleNamespace(**globals())


def _facade_forward(fn):
    """Create a thin wrapper that injects ``facade=_current_facade()``."""
    @functools.wraps(fn)
    def _wrapper(*args, **kwargs):
        return fn(*args, facade=_current_facade(), **kwargs)
    return _wrapper


# ---------------------------------------------------------------------------
# Non-facade delegates (pure forwarding, no facade needed)
# ---------------------------------------------------------------------------
_format_bytes = _harness_disk._format_bytes
_disk_usage_percent = _harness_disk._disk_usage_percent
_directory_size_bytes = _harness_disk._directory_size_bytes
_is_auxiliary_workspace_target = _harness_disk._is_auxiliary_workspace_target
_prune_directory = _harness_disk._prune_directory
_prune_stale_harness_temp_targets = _harness_disk._prune_stale_harness_temp_targets
_workspace_target_bases = harness_targets._workspace_target_bases
_workspace_target_binary = harness_targets._workspace_target_binary
_skip_harness_prebuild_requested = harness_targets._skip_harness_prebuild_requested
_missing_harness_binaries = harness_targets._missing_harness_binaries
_harness_source_fingerprint = harness_targets._harness_source_fingerprint
_write_harness_binary_provenance = harness_targets._write_harness_binary_provenance
_harness_binary_provenance_error = harness_targets._harness_binary_provenance_error
_current_workspace_target_name = harness_targets._current_workspace_target_name
_parse_target_owner_name = harness_targets._parse_target_owner_name
_pid_target_name = harness_targets._pid_target_name
_read_pid = harness_targets._read_pid
_pid_is_alive = harness_targets._pid_is_alive
_live_role_target_names = harness_targets._live_role_target_names
_active_workspace_target_names = harness_targets._active_workspace_target_names
_rebuildable_workspace_target_cache_paths = harness_targets._rebuildable_workspace_target_cache_paths

# ---------------------------------------------------------------------------
# Facade-forwarding delegates (one-liner wrappers via _facade_forward)
# ---------------------------------------------------------------------------
# harness_project
find_workspace_root = _facade_forward(harness_project.find_workspace_root)
find_creusot_tests = _facade_forward(harness_project.find_creusot_tests)
create_test_project = _facade_forward(harness_project.create_test_project)
create_warmup_project = _facade_forward(harness_project.create_warmup_project)
transform_creusot_to_trust_wp = _facade_forward(harness_project.transform_creusot_to_trust_wp)
apply_test_specific_shims = _facade_forward(harness_project.apply_test_specific_shims)

# harness_runner
setup_trust_wp_rustc_wrapper = _facade_forward(harness_runner.setup_trust_wp_rustc_wrapper)
run_trust_wp_on_project = _facade_forward(harness_runner.run_trust_wp_on_project)

# harness_baseline (output + provenance)
_normalize_output_for_storage = _facade_forward(harness_baseline._normalize_output_for_storage)
_truncate_output = _facade_forward(harness_baseline._truncate_output)
_truncate_output_with_flag = _facade_forward(harness_baseline._truncate_output_with_flag)
_summarize_subset = _facade_forward(harness_baseline._summarize_subset)
summarize_results = _facade_forward(harness_baseline.summarize_results)
_count_parse_failures = _facade_forward(harness_baseline._count_parse_failures)
_get_dirty_files = _facade_forward(harness_baseline._get_dirty_files)
_is_output_artifact_path = _facade_forward(harness_baseline._is_output_artifact_path)
_filter_source_dirty_files = _facade_forward(harness_baseline._filter_source_dirty_files)
_get_git_commit = _facade_forward(harness_baseline._get_git_commit)
build_run_metadata = _facade_forward(harness_baseline.build_run_metadata)
_is_same_rel_path = _facade_forward(harness_baseline._is_same_rel_path)
_strip_dirty_suffix = _facade_forward(harness_baseline._strip_dirty_suffix)
_load_results_git_commit = _facade_forward(harness_baseline._load_results_git_commit)
_commit_distance_to_head = _facade_forward(harness_baseline._commit_distance_to_head)
compute_lane_pair_freshness = _facade_forward(harness_baseline.compute_lane_pair_freshness)
check_baseline_freshness = _facade_forward(harness_baseline.check_baseline_freshness)
_drop_status_fields = _facade_forward(harness_baseline._drop_status_fields)
_snapshot_freshness_for_metadata = _facade_forward(harness_baseline._snapshot_freshness_for_metadata)

# harness_disk (facade-passing subset)
_prune_safe_workspace_target_dirs = _facade_forward(_harness_disk._prune_safe_workspace_target_dirs)
_warn_if_disk_pressure = _facade_forward(_harness_disk._warn_if_disk_pressure)
_prune_workspace_target_caches = _facade_forward(_harness_disk._prune_workspace_target_caches)
_prune_live_workspace_target_caches = _facade_forward(_harness_disk._prune_live_workspace_target_caches)
_prune_default_workspace_target_caches = _facade_forward(
    _harness_disk._prune_default_workspace_target_caches
)
_prune_current_workspace_target_caches = _facade_forward(
    _harness_disk._prune_current_workspace_target_caches
)


# ---------------------------------------------------------------------------
# Custom wrappers (extra logic beyond simple forwarding)
# ---------------------------------------------------------------------------
def ensure_harness_binaries(workspace: Path, verbose: bool) -> None:
    """Build harness binaries, or reuse only cryptographically bound artifacts."""
    if _skip_harness_prebuild_requested():
        missing = _missing_harness_binaries(workspace)
        if missing:
            raise RuntimeError(
                "TRUST_WP_HARNESS_SKIP_PREBUILD=1 but required harness binaries "
                f"are missing: {', '.join(str(p) for p in missing)}"
            )
        if provenance_error := _harness_binary_provenance_error(workspace):
            raise RuntimeError(
                "TRUST_WP_HARNESS_SKIP_PREBUILD=1 cannot reuse unbound or stale "
                f"harness binaries: {provenance_error}"
            )
        if verbose:
            print(
                "Skipping harness binary prebuild "
                "(TRUST_WP_HARNESS_SKIP_PREBUILD=1); reusing provenance-validated "
                "workspace binaries."
            )
        return
    source_before = _harness_source_fingerprint(workspace)
    _runner_ensure_harness_binaries(workspace, verbose, facade=_current_facade())
    source_after = _harness_source_fingerprint(workspace)
    if source_after != source_before:
        raise RuntimeError(
            "harness source, path dependency, toolchain, or build environment "
            "changed while binaries were being built"
        )
    _write_harness_binary_provenance(workspace, source_after)


def run_harness(
    verbose: bool = False,
    filter_pattern: str | None = None,
    limit: int | None = None,
    lane: str = "should_succeed",
    timeout_sec: int = 120,
) -> list[TestResult]:
    """Run the compatibility harness with disk-pressure check."""
    _warn_if_disk_pressure(find_workspace_root())
    return _runner_run_harness(
        verbose=verbose,
        filter_pattern=filter_pattern,
        limit=limit,
        lane=lane,
        timeout_sec=timeout_sec,
        facade=_current_facade(),
    )


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------
def main():
    return _cli_main(facade=_current_facade())


if __name__ == "__main__":
    sys.exit(main())
