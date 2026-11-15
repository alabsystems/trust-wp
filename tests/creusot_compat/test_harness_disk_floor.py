# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Disk-pressure pruning must not delete live target caches while free space is ample.

Run with: pytest tests/creusot_compat/test_harness_disk_floor.py -v
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

HARNESS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(HARNESS_DIR.parent.parent))
sys.path.insert(0, str(HARNESS_DIR))
_spec = importlib.util.spec_from_file_location("harness", HARNESS_DIR / "harness.py")
harness = importlib.util.module_from_spec(_spec)
sys.modules.setdefault("harness", harness)
_spec.loader.exec_module(harness)

GIB = 1024**3
PRUNERS = (
    "_prune_safe_workspace_target_dirs",
    "_prune_live_workspace_target_caches",
    "_prune_current_workspace_target_caches",
    "_prune_default_workspace_target_caches",
)


def _instrument(monkeypatch, free_bytes):
    calls: list[str] = []
    monkeypatch.setattr(harness, "_disk_usage_percent", lambda _path: 95)
    monkeypatch.setattr(harness, "_disk_free_bytes", lambda _path: free_bytes)
    monkeypatch.setattr(harness, "_prune_stale_harness_temp_targets", lambda **_kw: 0)
    for name in PRUNERS:
        def fake(_workspace, _name=name):
            calls.append(_name)
            return 0, []
        monkeypatch.setattr(harness, name, fake)
    return calls


def test_ample_free_space_skips_target_cache_pruning(monkeypatch, tmp_path, capsys):
    monkeypatch.delenv("TRUST_WP_HARNESS_PRUNE_MIN_FREE_GIB", raising=False)
    calls = _instrument(monkeypatch, 200 * GIB)
    harness._warn_if_disk_pressure(tmp_path)
    assert calls == []
    assert "not pruning workspace target caches" in capsys.readouterr().out


def test_low_free_space_still_prunes(monkeypatch, tmp_path):
    monkeypatch.delenv("TRUST_WP_HARNESS_PRUNE_MIN_FREE_GIB", raising=False)
    # Below the default floor (now 10 GiB, was 50). 5 GiB is unambiguously low;
    # the old constant of 10 GiB sat exactly on the new boundary.
    calls = _instrument(monkeypatch, 5 * GIB)
    harness._warn_if_disk_pressure(tmp_path)
    assert calls[0] == "_prune_safe_workspace_target_dirs"
    assert set(calls) == set(PRUNERS)


def test_env_floor_override(monkeypatch, tmp_path):
    monkeypatch.setenv("TRUST_WP_HARNESS_PRUNE_MIN_FREE_GIB", "500")
    calls = _instrument(monkeypatch, 200 * GIB)
    harness._warn_if_disk_pressure(tmp_path)
    assert set(calls) == set(PRUNERS)


def test_unknown_free_space_keeps_old_behaviour(monkeypatch, tmp_path):
    calls = _instrument(monkeypatch, None)
    harness._warn_if_disk_pressure(tmp_path)
    assert set(calls) == set(PRUNERS)


def test_below_threshold_does_nothing(monkeypatch, tmp_path):
    calls = _instrument(monkeypatch, 1 * GIB)
    monkeypatch.setattr(harness, "_disk_usage_percent", lambda _path: 50)
    harness._warn_if_disk_pressure(tmp_path)
    assert calls == []
