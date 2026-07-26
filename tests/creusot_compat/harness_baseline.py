#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Baseline/provenance/summarization re-export hub for the Creusot harness.

Implementation lives in ``harness_output`` (normalization, truncation,
summaries) and ``harness_provenance`` (dirty-tree, git commit, freshness,
metadata).  This module re-exports everything so existing import sites
continue to work unchanged.
"""

from __future__ import annotations

try:
    from tests.creusot_compat.harness_output import (
        TRUNCATED_OUTPUT_HEAD_LEN,
        TRUNCATED_OUTPUT_MARKER,
        TRUNCATED_OUTPUT_MAX_LEN,
        TRUNCATED_OUTPUT_SENTINEL,
        _count_parse_failures,
        _normalize_output_for_storage,
        _summarize_subset,
        _truncate_output,
        _truncate_output_with_flag,
        summarize_results,
    )
    from tests.creusot_compat.harness_provenance import (
        _commit_distance_to_head,
        _drop_status_fields,
        _filter_source_dirty_files,
        _get_dirty_files,
        _get_git_commit,
        _is_output_artifact_path,
        _is_same_rel_path,
        _load_results_git_commit,
        _snapshot_freshness_for_metadata,
        _strip_dirty_suffix,
        build_run_metadata,
        check_baseline_freshness,
        compute_lane_pair_freshness,
    )
except ModuleNotFoundError:
    from harness_output import (  # type: ignore[no-redef]
        TRUNCATED_OUTPUT_HEAD_LEN,
        TRUNCATED_OUTPUT_MARKER,
        TRUNCATED_OUTPUT_MAX_LEN,
        TRUNCATED_OUTPUT_SENTINEL,
        _count_parse_failures,
        _normalize_output_for_storage,
        _summarize_subset,
        _truncate_output,
        _truncate_output_with_flag,
        summarize_results,
    )
    from harness_provenance import (  # type: ignore[no-redef]
        _commit_distance_to_head,
        _drop_status_fields,
        _filter_source_dirty_files,
        _get_dirty_files,
        _get_git_commit,
        _is_output_artifact_path,
        _is_same_rel_path,
        _load_results_git_commit,
        _snapshot_freshness_for_metadata,
        _strip_dirty_suffix,
        build_run_metadata,
        check_baseline_freshness,
        compute_lane_pair_freshness,
    )

__all__ = [
    "TRUNCATED_OUTPUT_HEAD_LEN",
    "TRUNCATED_OUTPUT_MARKER",
    "TRUNCATED_OUTPUT_MAX_LEN",
    "TRUNCATED_OUTPUT_SENTINEL",
    "_commit_distance_to_head",
    "_count_parse_failures",
    "_drop_status_fields",
    "_filter_source_dirty_files",
    "_get_dirty_files",
    "_get_git_commit",
    "_is_output_artifact_path",
    "_is_same_rel_path",
    "_load_results_git_commit",
    "_normalize_output_for_storage",
    "_snapshot_freshness_for_metadata",
    "_strip_dirty_suffix",
    "_summarize_subset",
    "_truncate_output",
    "_truncate_output_with_flag",
    "build_run_metadata",
    "check_baseline_freshness",
    "compute_lane_pair_freshness",
    "summarize_results",
]
