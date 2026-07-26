#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Disk-pressure and target-cache lifecycle helpers for the Creusot harness.

Patch-sensitive helpers route through a harness facade so existing monkeypatch
targets on ``harness.py`` continue to work after extraction.
"""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

try:
    from tests.creusot_compat.harness_facade import (
        DISK_REQUIRED_ATTRS,
        resolve_harness_facade,
    )
    from tests.creusot_compat.harness_model import (
        DISK_WARNING_THRESHOLD_PERCENT,
        HARNESS_TEMP_TARGET_PREFIX,
        STALE_HARNESS_TEMP_MAX_AGE_HOURS,
    )
except ModuleNotFoundError:
    # Running as a script (`python3 tests/creusot_compat/harness.py`) puts this
    # directory on sys.path, so import sibling modules directly.
    from harness_facade import DISK_REQUIRED_ATTRS, resolve_harness_facade
    from harness_model import (  # type: ignore[no-redef]
        DISK_WARNING_THRESHOLD_PERCENT,
        HARNESS_TEMP_TARGET_PREFIX,
        STALE_HARNESS_TEMP_MAX_AGE_HOURS,
    )


def _resolve_harness_facade(facade: object | None) -> object:
    return resolve_harness_facade(facade, DISK_REQUIRED_ATTRS, context="disk")


def _format_bytes(num_bytes: int) -> str:
    """Format a byte count using IEC units for warning messages."""
    if num_bytes < 1024:
        return f"{num_bytes} B"

    size = float(num_bytes)
    for unit in ("KiB", "MiB", "GiB", "TiB"):
        size /= 1024.0
        if size < 1024.0 or unit == "TiB":
            return f"{size:.1f} {unit}"

    return f"{size:.1f} TiB"


def _disk_usage_percent(path: Path) -> int | None:
    """Return the volume capacity percentage for *path*, or ``None`` on failure."""
    try:
        result = subprocess.run(
            ["df", "-Pk", str(path)],
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError:
        return None

    if result.returncode != 0:
        return None

    lines = [line for line in result.stdout.splitlines() if line.strip()]
    if len(lines) < 2:
        return None

    columns = lines[1].split()
    if len(columns) < 5:
        return None

    capacity = columns[4].rstrip("%")
    return int(capacity) if capacity.isdigit() else None


def _directory_size_bytes(path: Path) -> int:
    """Best-effort recursive file-size total for a directory tree."""
    total = 0
    for child in path.rglob("*"):
        try:
            if child.is_file():
                total += child.stat().st_size
        except OSError:
            continue
    return total


def _is_auxiliary_workspace_target(name: str) -> bool:
    """Return True for harness/probe/verification caches safe to drop wholesale."""
    return (
        name == "tmp"
        or name.endswith("_verify")
        or name.endswith("_tests")
        or re.search(r"_probe\d*$", name) is not None
    )


def _prune_directory(path: Path) -> int:
    """Delete a directory tree and return its best-effort reclaimed bytes."""
    if not path.exists():
        return 0
    reclaimed = _directory_size_bytes(path)
    shutil.rmtree(path, ignore_errors=True)
    return reclaimed


def _prune_safe_workspace_target_dirs(
    workspace: Path,
    facade: object | None = None,
) -> tuple[int, list[str]]:
    """Prune stale workspace target dirs while preserving live role-owned targets."""
    harness = _resolve_harness_facade(facade)
    target_root = workspace / "target"
    if not target_root.is_dir():
        return 0, []

    live_targets = harness._live_role_target_names(workspace)
    current_target = harness._current_workspace_target_name()
    reclaimed_bytes = 0
    pruned_paths: list[str] = []

    try:
        candidates = sorted(target_root.iterdir())
    except OSError:
        return 0, []

    for candidate in candidates:
        if not candidate.is_dir():
            continue

        name = candidate.name
        if _is_auxiliary_workspace_target(name):
            reclaimed = _prune_directory(candidate)
            if reclaimed > 0:
                reclaimed_bytes += reclaimed
                pruned_paths.append(str(candidate.relative_to(workspace)))
            continue

        owner = harness._parse_target_owner_name(name)
        if owner is None or owner == current_target or owner in live_targets:
            continue

        reclaimed = _prune_directory(candidate)
        if reclaimed > 0:
            reclaimed_bytes += reclaimed
            pruned_paths.append(str(candidate.relative_to(workspace)))

    return reclaimed_bytes, pruned_paths


def _prune_workspace_target_caches(
    workspace: Path,
    target_dir: Path,
    facade: object | None = None,
) -> tuple[int, list[str]]:
    """Prune rebuildable caches within one isolated target dir."""
    harness = _resolve_harness_facade(facade)
    reclaimed_bytes = 0
    pruned_paths: list[str] = []

    for cache_path in harness._rebuildable_workspace_target_cache_paths(target_dir):
        reclaimed = _prune_directory(cache_path)
        if reclaimed <= 0:
            continue
        reclaimed_bytes += reclaimed
        pruned_paths.append(str(cache_path.relative_to(workspace)))

    return reclaimed_bytes, pruned_paths


def _prune_live_workspace_target_caches(
    workspace: Path,
    facade: object | None = None,
) -> tuple[int, list[str]]:
    """Prune rebuildable caches from live targets that are not the current/active build."""
    harness = _resolve_harness_facade(facade)
    target_root = workspace / "target"
    if not target_root.is_dir():
        return 0, []

    live_targets = harness._live_role_target_names(workspace)
    current_target = harness._current_workspace_target_name()
    active_targets = harness._active_workspace_target_names(workspace)
    reclaimed_bytes = 0
    pruned_paths: list[str] = []

    try:
        candidates = sorted(target_root.iterdir())
    except OSError:
        return 0, []

    for candidate in candidates:
        if not candidate.is_dir():
            continue

        owner = harness._parse_target_owner_name(candidate.name)
        if (
            owner is None
            or owner not in live_targets
            or owner == current_target
            or owner in active_targets
        ):
            continue

        reclaimed, candidate_paths = _prune_workspace_target_caches(
            workspace, candidate, facade=harness
        )
        if reclaimed <= 0:
            continue

        reclaimed_bytes += reclaimed
        pruned_paths.extend(candidate_paths)

    return reclaimed_bytes, pruned_paths


def _prune_default_workspace_target_caches(
    workspace: Path,
    facade: object | None = None,
) -> tuple[int, list[str]]:
    """Prune rebuildable caches from the default (unowned) target dir."""
    target_root = workspace / "target"
    if not target_root.is_dir():
        return 0, []

    # The default target stores debug artifacts directly under target/debug/,
    # unlike per-role targets which nest under target/<role>/debug/.
    # Treat target/ as the target_dir so _rebuildable_workspace_target_cache_paths
    # finds target/debug/deps and target/debug/incremental.
    return _prune_workspace_target_caches(workspace, target_root, facade=facade)


def _prune_current_workspace_target_caches(
    workspace: Path,
    facade: object | None = None,
) -> tuple[int, list[str]]:
    """Prune rebuildable caches from the current target when it is idle."""
    harness = _resolve_harness_facade(facade)
    current_target = harness._current_workspace_target_name()
    if current_target is None:
        return 0, []

    if current_target in harness._active_workspace_target_names(workspace):
        return 0, []

    target_dir = workspace / "target" / current_target
    if not target_dir.is_dir():
        return 0, []

    return _prune_workspace_target_caches(workspace, target_dir, facade=harness)


def _prune_stale_harness_temp_targets(
    temp_root: Path | None = None,
    *,
    max_age_hours: int = STALE_HARNESS_TEMP_MAX_AGE_HOURS,
    now: float | None = None,
) -> int:
    """Remove stale harness-owned temp target dirs and return freed bytes."""
    root = temp_root or Path(tempfile.gettempdir())
    cutoff = (time.time() if now is None else now) - (max_age_hours * 3600)
    freed_bytes = 0

    for candidate in root.glob(f"{HARNESS_TEMP_TARGET_PREFIX}*"):
        try:
            if not candidate.is_dir() or candidate.stat().st_mtime > cutoff:
                continue
        except OSError:
            continue

        freed_bytes += _directory_size_bytes(candidate)
        shutil.rmtree(candidate, ignore_errors=True)

    return freed_bytes


def _warn_if_disk_pressure(
    workspace: Path,
    *,
    threshold_percent: int = DISK_WARNING_THRESHOLD_PERCENT,
    facade: object | None = None,
) -> None:
    """Warn when the current volume is near full and prune stale harness temp dirs."""
    harness = _resolve_harness_facade(facade)
    usage_before = harness._disk_usage_percent(workspace)
    if usage_before is None or usage_before < threshold_percent:
        return

    temp_root = Path(tempfile.gettempdir())
    temp_freed_bytes = harness._prune_stale_harness_temp_targets(temp_root=temp_root)
    usage_after = (
        harness._disk_usage_percent(workspace)
        if temp_freed_bytes > 0
        else usage_before
    )
    workspace_freed_bytes = 0
    workspace_pruned_paths: list[str] = []
    if usage_after is None or usage_after >= threshold_percent:
        workspace_freed_bytes, workspace_pruned_paths = (
            harness._prune_safe_workspace_target_dirs(workspace)
        )
        if workspace_freed_bytes > 0:
            usage_after = harness._disk_usage_percent(workspace)
    live_cache_freed_bytes = 0
    live_cache_pruned_paths: list[str] = []
    if usage_after is None or usage_after >= threshold_percent:
        live_cache_freed_bytes, live_cache_pruned_paths = (
            harness._prune_live_workspace_target_caches(workspace)
        )
        if live_cache_freed_bytes > 0:
            usage_after = harness._disk_usage_percent(workspace)
    current_cache_freed_bytes = 0
    current_cache_pruned_paths: list[str] = []
    if usage_after is None or usage_after >= threshold_percent:
        current_cache_freed_bytes, current_cache_pruned_paths = (
            harness._prune_current_workspace_target_caches(workspace)
        )
        if current_cache_freed_bytes > 0:
            usage_after = harness._disk_usage_percent(workspace)
    default_cache_freed_bytes = 0
    default_cache_pruned_paths: list[str] = []
    if usage_after is None or usage_after >= threshold_percent:
        default_cache_freed_bytes, default_cache_pruned_paths = (
            harness._prune_default_workspace_target_caches(workspace)
        )
        if default_cache_freed_bytes > 0:
            usage_after = harness._disk_usage_percent(workspace)

    message = (
        f"trust-wp-harness: warning: disk usage {usage_before}% >= {threshold_percent}% "
        f"before starting the compatibility harness"
    )
    if temp_freed_bytes > 0:
        message += (
            f"; pruned {_format_bytes(temp_freed_bytes)} of stale harness temp targets "
            f"under {temp_root}"
        )
    if workspace_freed_bytes > 0:
        displayed_paths = workspace_pruned_paths[:3]
        more_count = len(workspace_pruned_paths) - len(displayed_paths)
        target_summary = ", ".join(displayed_paths)
        if more_count > 0:
            target_summary += f", +{more_count} more"
        message += (
            f"; pruned {_format_bytes(workspace_freed_bytes)} of inactive workspace "
            f"targets ({target_summary})"
        )
    if live_cache_freed_bytes > 0:
        displayed_paths = live_cache_pruned_paths[:3]
        more_count = len(live_cache_pruned_paths) - len(displayed_paths)
        cache_summary = ", ".join(displayed_paths)
        if more_count > 0:
            cache_summary += f", +{more_count} more"
        message += (
            f"; pruned {_format_bytes(live_cache_freed_bytes)} of rebuildable caches "
            f"from live but idle targets ({cache_summary})"
        )
    if current_cache_freed_bytes > 0:
        displayed_paths = current_cache_pruned_paths[:3]
        more_count = len(current_cache_pruned_paths) - len(displayed_paths)
        cache_summary = ", ".join(displayed_paths)
        if more_count > 0:
            cache_summary += f", +{more_count} more"
        message += (
            f"; pruned {_format_bytes(current_cache_freed_bytes)} of rebuildable caches "
            f"from the current target ({cache_summary})"
        )
    if default_cache_freed_bytes > 0:
        displayed_paths = default_cache_pruned_paths[:3]
        more_count = len(default_cache_pruned_paths) - len(displayed_paths)
        cache_summary = ", ".join(displayed_paths)
        if more_count > 0:
            cache_summary += f", +{more_count} more"
        message += (
            f"; pruned {_format_bytes(default_cache_freed_bytes)} of rebuildable caches "
            f"from the default target ({cache_summary})"
        )
    if usage_after is not None and usage_after < threshold_percent:
        message += f"; usage after prune: {usage_after}%"
    else:
        message += (
            "; targets currently in use may still need cleanup before long harness runs"
        )

    print(message, file=sys.stderr)
