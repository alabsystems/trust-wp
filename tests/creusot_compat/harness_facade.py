#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Shared facade contract helpers for extracted harness modules."""

from __future__ import annotations

import sys
from importlib import import_module
from pathlib import Path
from typing import Any, Iterable, Pattern, Protocol, cast, runtime_checkable

FACADE_MODULE_CANDIDATES = (
    # Test loader alias from tests/test_creusot_compat_harness*.py.
    "creusot_compat_harness",
    # Normal package import path.
    "tests.creusot_compat.harness",
    # Direct sibling import path when running harness.py as a script.
    "harness",
)


BASELINE_REQUIRED_ATTRS = (
    "BACKEND_PASS_PREFIX",
    "BASELINE_MAX_AGE_COMMITS_DEFAULT",
    "CANONICAL_EXAMPLES_OUTPUT",
    "CANONICAL_OUTPUT",
    "CANONICAL_SHOULD_FAIL_OUTPUT",
    "LANE_PAIR_MAX_AGE_GAP_COMMITS",
    "NO_REPLAY_PASS_PREFIX",
    "PARSE_FAILURE_PATTERNS",
    "STRICT_PASS_PREFIX",
    "_commit_distance_to_head",
    "_count_parse_failures",
    "_is_same_rel_path",
    "_is_should_fail_test",
    "_load_results_git_commit",
    "_normalize_output_for_storage",
    "_summarize_subset",
    "_truncate_output_with_flag",
)

CLI_REQUIRED_ATTRS = (
    "BASELINE_FRESHNESS_EXIT_CODE",
    "BASELINE_MAX_AGE_COMMITS_DEFAULT",
    "CANONICAL_EXAMPLES_OUTPUT",
    "CANONICAL_OUTPUT",
    "CANONICAL_SHOULD_FAIL_OUTPUT",
    "HEAD_DRIFT_MAX_COMMITS_DEFAULT",
    "HEAD_DRIFT_POLICY_EXIT_CODE",
    "VALID_LANES",
    "_commit_distance_to_head",
    "_filter_source_dirty_files",
    "_get_dirty_files",
    "_get_git_commit",
    "_is_same_rel_path",
    "_snapshot_freshness_for_metadata",
    "build_run_metadata",
    "check_baseline_freshness",
    "compute_lane_pair_freshness",
    "find_creusot_tests",
    "find_workspace_root",
    "run_harness",
    "summarize_results",
)

OUTPUT_REQUIRED_ATTRS = (
    "BACKEND_PASS_PREFIX",
    "NO_REPLAY_PASS_PREFIX",
    "PARSE_FAILURE_PATTERNS",
    "STRICT_PASS_PREFIX",
    "_count_parse_failures",
    "_is_should_fail_test",
    "_normalize_output_for_storage",
    "_summarize_subset",
)

PROVENANCE_REQUIRED_ATTRS = (
    "BASELINE_MAX_AGE_COMMITS_DEFAULT",
    "CANONICAL_EXAMPLES_OUTPUT",
    "CANONICAL_OUTPUT",
    "CANONICAL_SHOULD_FAIL_OUTPUT",
    "LANE_PAIR_MAX_AGE_GAP_COMMITS",
    "_commit_distance_to_head",
    "_drop_status_fields",
    "_get_git_commit",
    "_is_output_artifact_path",
    "_is_same_rel_path",
    "_load_results_git_commit",
    "_strip_dirty_suffix",
)

DISK_REQUIRED_ATTRS = (
    "_active_workspace_target_names",
    "_current_workspace_target_name",
    "_directory_size_bytes",
    "_disk_usage_percent",
    "_format_bytes",
    "_is_auxiliary_workspace_target",
    "_live_role_target_names",
    "_parse_target_owner_name",
    "_prune_current_workspace_target_caches",
    "_prune_default_workspace_target_caches",
    "_prune_directory",
    "_prune_live_workspace_target_caches",
    "_prune_safe_workspace_target_dirs",
    "_prune_stale_harness_temp_targets",
    "_prune_workspace_target_caches",
    "_rebuildable_workspace_target_cache_paths",
)

PROJECT_REQUIRED_ATTRS = (
    "VALID_LANES",
    "apply_test_specific_shims",
    "transform_creusot_to_trust_wp",
)

RUNNER_REQUIRED_ATTRS = (
    "BACKEND_PASS_PREFIX",
    "NO_REPLAY_PASS_PREFIX",
    "NO_REPLAY_STRICT_ERROR_MESSAGE",
    "STRICT_PASS_PREFIX",
    "TestResult",
    "_KNOWN_STRICT_REJECTION_TESTS",
    "_check_backend_superseded",
    "_has_cargo_lock_contention",
    "_is_no_replay_source",
    "_is_should_fail_test",
    "_truncate_output",
    "_verification_run_succeeded",
    "classify_error_category",
    "classify_failure",
    "classify_no_replay_result",
    "classify_should_fail_result",
    "classify_unknown_category",
    "create_test_project",
    "create_warmup_project",
    "ensure_harness_binaries",
    "find_creusot_tests",
    "find_workspace_root",
    "run_trust_wp_on_project",
    "setup_trust_wp_rustc_wrapper",
    "subprocess",
)


@runtime_checkable
class HarnessFacade(Protocol):
    """Typed facade contract shared across extracted harness modules."""

    BACKEND_PASS_PREFIX: str
    BASELINE_FRESHNESS_EXIT_CODE: int
    BASELINE_MAX_AGE_COMMITS_DEFAULT: int
    CANONICAL_EXAMPLES_OUTPUT: str
    CANONICAL_OUTPUT: str
    CANONICAL_SHOULD_FAIL_OUTPUT: str
    HEAD_DRIFT_MAX_COMMITS_DEFAULT: int
    HEAD_DRIFT_POLICY_EXIT_CODE: int
    LANE_PAIR_MAX_AGE_GAP_COMMITS: int
    NO_REPLAY_PASS_PREFIX: str
    NO_REPLAY_STRICT_ERROR_MESSAGE: str
    PARSE_FAILURE_PATTERNS: dict[str, Pattern[str]]
    STRICT_PASS_PREFIX: str
    VALID_LANES: tuple[str, ...]
    TestResult: type[Any]
    _KNOWN_BACKEND_SUPERSEDED_TESTS: dict[str, str]
    _KNOWN_STRICT_REJECTION_TESTS: dict[str, str]
    subprocess: Any

    def _commit_distance_to_head(
        self, workspace: Path, commit: str | None
    ) -> int | None: ...
    def _active_workspace_target_names(self, workspace: Path) -> set[str]: ...
    def _check_backend_superseded(self, test_name: str) -> str | None: ...
    def _count_parse_failures(self, results: list[Any]) -> dict[str, int]: ...
    def _current_workspace_target_name(self) -> str | None: ...
    def _directory_size_bytes(self, path: Path) -> int: ...
    def _disk_usage_percent(self, path: Path) -> int | None: ...
    def _filter_source_dirty_files(self, dirty_files: list[str]) -> list[str]: ...
    def _format_bytes(self, num_bytes: int) -> str: ...
    def _get_dirty_files(self, workspace: Path) -> list[str]: ...
    def _get_git_commit(
        self, workspace: Path, dirty_files: list[str] | None = None
    ) -> str | None: ...
    def _has_cargo_lock_contention(self, output: str) -> bool: ...
    def _is_auxiliary_workspace_target(self, name: str) -> bool: ...
    def _is_no_replay_source(self, source: str) -> bool: ...
    def _is_same_rel_path(self, path_a: str, path_b: str) -> bool: ...
    def _is_should_fail_test(self, test_name: str) -> bool: ...
    def _load_results_git_commit(self, results_path: Path) -> str | None: ...
    def _live_role_target_names(self, workspace: Path) -> set[str]: ...
    def _normalize_output_for_storage(self, output: str, workspace: Path) -> str: ...
    def _parse_target_owner_name(self, name: str) -> str | None: ...
    def _prune_current_workspace_target_caches(
        self, workspace: Path
    ) -> tuple[int, list[str]]: ...
    def _prune_default_workspace_target_caches(
        self, workspace: Path
    ) -> tuple[int, list[str]]: ...
    def _prune_directory(self, path: Path) -> int: ...
    def _prune_live_workspace_target_caches(
        self, workspace: Path
    ) -> tuple[int, list[str]]: ...
    def _prune_safe_workspace_target_dirs(
        self, workspace: Path
    ) -> tuple[int, list[str]]: ...
    def _prune_stale_harness_temp_targets(
        self,
        temp_root: Path | None = None,
        *,
        max_age_hours: int = 0,
        now: float | None = None,
    ) -> int: ...
    def _prune_workspace_target_caches(
        self, workspace: Path, target_dir: Path
    ) -> tuple[int, list[str]]: ...
    def _rebuildable_workspace_target_cache_paths(
        self, target_dir: Path
    ) -> list[Path]: ...
    def _snapshot_freshness_for_metadata(
        self,
        freshness: dict[str, object],
        *,
        evaluated_against_head: str | None,
    ) -> dict[str, object]: ...
    def _summarize_subset(self, results: list[Any]) -> dict[str, Any]: ...
    def _truncate_output(self, output: str, workspace: Path) -> str: ...
    def _truncate_output_with_flag(
        self, output: str, workspace: Path
    ) -> tuple[str, bool]: ...
    def _verification_run_succeeded(self, returncode: int, output: str) -> bool: ...
    def apply_test_specific_shims(self, test_file: Path, source: str) -> str: ...
    def build_run_metadata(
        self,
        args: Any,
        workspace: Path,
        discovered_count: int,
        executed_count: int,
        dirty_files: list[str] | None = None,
        pinned_commit: str | None = None,
        head_drift_commits: int | None = None,
        head_drift_max_commits: int | None = None,
    ) -> dict[str, Any]: ...
    def check_baseline_freshness(
        self,
        workspace: Path,
        max_age_commits: int = 0,
        commit_overrides: dict[str, str] | None = None,
    ) -> dict[str, object]: ...
    def classify_error_category(
        self, output: str, exit_code: int | None = None
    ) -> str | None: ...
    def classify_failure(
        self, output: str, source: str, exit_code: int | None = None
    ) -> tuple[str, str | None]: ...
    def classify_unknown_category(self, output: str) -> str: ...
    def classify_no_replay_result(
        self, output: str, exit_code: int | None = None
    ) -> tuple[str, str | None]: ...
    def classify_should_fail_result(
        self,
        success: bool,
        output: str,
        source: str,
        test_name: str,
        exit_code: int | None = None,
    ) -> tuple[str, str | None]: ...
    def compute_lane_pair_freshness(
        self,
        *,
        workspace: Path,
        lane: str,
        output_rel: str,
        is_partial: bool,
        current_git_commit: str | None,
        max_age_gap_commits: int = 0,
    ) -> dict[str, object] | None: ...
    def create_test_project(
        self, workspace: Path, test_file: Path, temp_dir: Path
    ) -> Path: ...
    def create_warmup_project(self, workspace: Path, temp_dir: Path) -> Path: ...
    def ensure_harness_binaries(self, workspace: Path, verbose: bool) -> None: ...
    def find_creusot_tests(
        self, workspace: Path, lane: str = "should_succeed"
    ) -> list[Path]: ...
    def find_workspace_root(self) -> Path: ...
    def run_harness(
        self,
        verbose: bool = False,
        filter_pattern: str | None = None,
        limit: int | None = None,
        lane: str = "should_succeed",
        timeout_sec: int = 120,
    ) -> list[Any]: ...
    def run_trust_wp_on_project(
        self,
        workspace: Path,
        project_dir: Path,
        timeout_sec: int = 120,
        shared_target_dir: Path | None = None,
    ) -> tuple[bool, str, int, int | None]: ...
    def setup_trust_wp_rustc_wrapper(self, workspace: Path, bin_dir: Path) -> None: ...
    def summarize_results(self, results: list[Any]) -> dict[str, Any]: ...
    def transform_creusot_to_trust_wp(self, source: str) -> str: ...


def has_required_attrs(module: object, required_attrs: Iterable[str]) -> bool:
    return all(hasattr(module, attr) for attr in required_attrs)


def load_harness_facade(
    required_attrs: Iterable[str], *, context: str
) -> HarnessFacade:
    for module_name in FACADE_MODULE_CANDIDATES:
        module = sys.modules.get(module_name)
        if module is not None and has_required_attrs(module, required_attrs):
            return cast(HarnessFacade, module)

    for module_name in FACADE_MODULE_CANDIDATES:
        if module_name == "creusot_compat_harness":
            # This alias only exists when explicitly loaded by tests.
            continue
        try:
            module = import_module(module_name)
        except ModuleNotFoundError:
            continue
        if has_required_attrs(module, required_attrs):
            return cast(HarnessFacade, module)

    main_module = sys.modules.get("__main__")
    if main_module is not None and has_required_attrs(main_module, required_attrs):
        return cast(HarnessFacade, main_module)

    raise RuntimeError(
        f"Unable to locate harness facade module for {context} routing"
    )


def resolve_harness_facade(
    facade: object | None, required_attrs: Iterable[str], *, context: str
) -> HarnessFacade:
    if facade is None:
        return load_harness_facade(required_attrs, context=context)
    if has_required_attrs(facade, required_attrs):
        return cast(HarnessFacade, facade)
    raise RuntimeError(f"Invalid harness facade passed to {context} module")
