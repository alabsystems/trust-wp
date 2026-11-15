# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""A pinned debug profile must not rebuild a leftover release driver binary.

Run with: pytest tests/creusot_compat/test_harness_release_rebuild.py -v
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path
from types import SimpleNamespace

HARNESS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(HARNESS_DIR.parent.parent))
sys.path.insert(0, str(HARNESS_DIR))
_spec = importlib.util.spec_from_file_location("harness", HARNESS_DIR / "harness.py")
harness = importlib.util.module_from_spec(_spec)
sys.modules.setdefault("harness", harness)
_spec.loader.exec_module(harness)


def _workspace_with_release_binary(tmp_path: Path) -> Path:
    release = tmp_path / "target" / "release"
    release.mkdir(parents=True)
    (release / "trust-wp-rustc").write_text("stale")
    return tmp_path


def _ensure(workspace):
    # Call the runner directly: the harness.py wrapper also fingerprints the
    # workspace sources through git, which the fake subprocess.run would break.
    harness.harness_runner.ensure_harness_binaries(workspace, False, facade=harness)


def _record_builds(monkeypatch):
    commands: list[list[str]] = []

    def fake_run(cmd, **_kwargs):
        commands.append(list(cmd))
        return SimpleNamespace(returncode=0, stdout="", stderr="")

    monkeypatch.setattr(harness.subprocess, "run", fake_run)
    monkeypatch.delenv("CARGO_TARGET_DIR", raising=False)
    return commands


def test_pinned_debug_ignores_leftover_release_binary(monkeypatch, tmp_path):
    workspace = _workspace_with_release_binary(tmp_path)
    commands = _record_builds(monkeypatch)
    monkeypatch.setenv("TRUST_WP_HARNESS_PROFILE", "debug")
    _ensure(workspace)
    assert commands, "the debug build must still run"
    assert not any("--release" in cmd for cmd in commands)


def test_auto_still_rebuilds_leftover_release_binary(monkeypatch, tmp_path):
    workspace = _workspace_with_release_binary(tmp_path)
    commands = _record_builds(monkeypatch)
    monkeypatch.delenv("TRUST_WP_HARNESS_PROFILE", raising=False)
    _ensure(workspace)
    assert any("--release" in cmd for cmd in commands)


def test_pinned_release_builds_release_without_binary(monkeypatch, tmp_path):
    commands = _record_builds(monkeypatch)
    monkeypatch.setenv("TRUST_WP_HARNESS_PROFILE", "release")
    _ensure(tmp_path)
    assert any("--release" in cmd for cmd in commands)
