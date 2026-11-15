"""A driver binary older than its own sources is refused, not silently used."""
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import os
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

import harness_targets  # noqa: E402


def _driver(tmp_path: Path, profile: str, sources: list[Path], *, age_ns: int) -> Path:
    d = tmp_path / "target" / profile
    d.mkdir(parents=True, exist_ok=True)
    binary = d / "trust-wp-rustc"
    binary.write_text("#!/bin/sh\n")
    deps = " ".join(str(s).replace(" ", "\\ ") for s in sources)
    (d / "trust-wp-rustc.d").write_text(f"{binary}: {deps} /x/.git/index\n")
    t = os.stat(binary).st_mtime_ns
    for src in sources:
        if src.exists():
            os.utime(src, ns=(t - age_ns, t - age_ns))
    return binary


def _src(tmp_path: Path, name: str) -> Path:
    p = tmp_path / "crates dir" / name
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("fn main() {}\n")
    return p


@pytest.fixture(autouse=True)
def _clean_env(monkeypatch):
    monkeypatch.delenv(harness_targets.HARNESS_PROFILE_ENV, raising=False)
    monkeypatch.delenv(harness_targets.ALLOW_STALE_DRIVER_ENV, raising=False)
    harness_targets._STALE_DRIVER_CACHE.clear()


def test_fresh_driver_is_selected(tmp_path):
    a = _src(tmp_path, "a.rs")
    _driver(tmp_path, "release", [a], age_ns=10**9)
    assert harness_targets.resolve_driver_profile(tmp_path)[0] == "release"


def test_auto_refuses_release_older_than_a_source(tmp_path):
    a, b = _src(tmp_path, "a.rs"), _src(tmp_path, "b.rs")
    binary = _driver(tmp_path, "release", [a, b], age_ns=10**9)
    t = os.stat(binary).st_mtime_ns
    os.utime(b, ns=(t + 10**9, t + 10**9))
    with pytest.raises(RuntimeError, match="older than a source"):
        harness_targets.resolve_driver_profile(tmp_path)


def test_pinned_debug_refuses_stale_debug(monkeypatch, tmp_path):
    monkeypatch.setenv(harness_targets.HARNESS_PROFILE_ENV, "debug")
    a = _src(tmp_path, "a.rs")
    binary = _driver(tmp_path, "debug", [a], age_ns=10**9)
    t = os.stat(binary).st_mtime_ns
    os.utime(a, ns=(t + 10**9, t + 10**9))
    with pytest.raises(RuntimeError, match="older than a source"):
        harness_targets.resolve_driver_profile(tmp_path)


def test_missing_source_means_stale(tmp_path):
    a = _src(tmp_path, "a.rs")
    gone = tmp_path / "crates dir" / "gone.rs"
    _driver(tmp_path, "release", [a, gone], age_ns=10**9)
    with pytest.raises(RuntimeError, match="gone.rs"):
        harness_targets.resolve_driver_profile(tmp_path)


def test_non_rust_dep_entries_are_ignored(tmp_path):
    a = _src(tmp_path, "a.rs")
    _driver(tmp_path, "release", [a], age_ns=10**9)
    # /x/.git/index is listed and does not exist; it must not count.
    assert harness_targets.stale_driver_source(tmp_path / "target" / "release" / "trust-wp-rustc") is None


def test_no_depinfo_is_not_judged(tmp_path):
    d = tmp_path / "target" / "release"
    d.mkdir(parents=True)
    (d / "trust-wp-rustc").write_text("#!/bin/sh\n")
    assert harness_targets.resolve_driver_profile(tmp_path)[0] == "release"


def test_explicit_override_allows_old_binary(monkeypatch, tmp_path):
    a = _src(tmp_path, "a.rs")
    binary = _driver(tmp_path, "release", [a], age_ns=10**9)
    t = os.stat(binary).st_mtime_ns
    os.utime(a, ns=(t + 10**9, t + 10**9))
    monkeypatch.setenv(harness_targets.ALLOW_STALE_DRIVER_ENV, "1")
    assert harness_targets.resolve_driver_profile(tmp_path)[0] == "release"
