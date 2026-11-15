#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Tests for Creusot compatibility harness metadata, partial-run protection,
and exit code semantics.

Run with: pytest tests/creusot_compat/test_harness.py -v
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from types import SimpleNamespace

import pytest

# Import harness module from the same directory.
HARNESS_DIR = Path(__file__).resolve().parent
WORKSPACE_ROOT = HARNESS_DIR.parent.parent
sys.path.insert(0, str(HARNESS_DIR.parent.parent))

import importlib

harness_spec = importlib.util.spec_from_file_location(
    "harness", HARNESS_DIR / "harness.py"
)
# Register in sys.modules before exec so dataclass processing works on 3.14+
harness = importlib.util.module_from_spec(harness_spec)
sys.modules["harness"] = harness
harness_spec.loader.exec_module(harness)

# Mirror the canonical field set so the synthetic wire lines stay parseable:
# parse_wire_line() rejects a line whose keys differ from
# harness_model.TELEMETRY_FIELD_NAMES (it grew erasure_errors etc. over time,
# which silently invalidated a hand-maintained copy of this tuple and made
# every synthetic wire line parse as None).
from tests.creusot_compat.harness_model import (  # noqa: E402
    TELEMETRY_FIELD_NAMES as WIRE_TELEMETRY_FIELD_ORDER,
)
from tests.creusot_compat import harness_runner  # noqa: E402
from tests.creusot_compat import harness_targets  # noqa: E402

COMPLETE_ZERO_TELEMETRY = {key: 0 for key in WIRE_TELEMETRY_FIELD_ORDER}


def _complete_telemetry(**overrides: int) -> dict[str, int]:
    telemetry = dict(COMPLETE_ZERO_TELEMETRY)
    telemetry.update(overrides)
    return telemetry


def _wire_line(**overrides: int) -> str:
    telemetry = _complete_telemetry(**overrides)
    pairs = " ".join(
        f"{key}={telemetry[key]}" for key in WIRE_TELEMETRY_FIELD_ORDER
    )
    return f"TRUST_WP_RESULT:v1 {pairs}\n"


def _diag_line(
    def_path: str,
    kind: str,
    *,
    ay_result: str = "sat",
    model_validated: str = "true",
    status: str = "failed",
    **extra: str,
) -> str:
    """A ``TRUST_WP_DIAGNOSTIC:v1`` record; defaults to a VALIDATED refutation."""
    fields = {
        "def_path": def_path,
        "kind": kind,
        "status": status,
        "reason": "counterexample",
        "ay_result": ay_result,
        "model_validated": model_validated,
        **extra,
    }
    pairs = " ".join(f"{key}={value}" for key, value in fields.items())
    return f"TRUST_WP_DIAGNOSTIC:v1 {pairs}\n"


def test_harness_binary_builds_are_locked(monkeypatch, tmp_path):
    """Both debug and stale-release rebuilds must preserve Cargo.lock authority."""

    calls = []

    class RecordingSubprocess:
        @staticmethod
        def run(cmd, **kwargs):
            calls.append((cmd, kwargs))
            return SimpleNamespace(returncode=0, stdout="", stderr="")

    release_binary = tmp_path / "target" / "release" / "trust-wp-rustc"
    release_binary.parent.mkdir(parents=True)
    release_binary.write_bytes(b"stale")
    monkeypatch.setattr(
        harness_runner,
        "_resolve_harness_facade",
        lambda _facade: SimpleNamespace(subprocess=RecordingSubprocess),
    )
    monkeypatch.setattr(
        harness_runner,
        "_workspace_target_binary",
        lambda _workspace, _name, profile="debug": (
            release_binary if profile == "release" else tmp_path / "missing"
        ),
    )

    harness_runner.ensure_harness_binaries(tmp_path, verbose=False)

    assert len(calls) == 2
    # The Trust build tool with its explicit lane, never a bare `cargo`.
    expected = harness_targets.build_tool_argv("build", "--locked")
    assert all(cmd[: len(expected)] == expected for cmd, _ in calls)


def test_build_tool_argv_names_the_trust_tool_and_its_lane(monkeypatch):
    """Harness builds go through targo (or the caller's $CARGO), never a bare
    `cargo`, and name `--unverified` only where targo accepts it."""
    monkeypatch.delenv("CARGO", raising=False)
    monkeypatch.delenv("RUSTC", raising=False)
    assert harness_targets.build_tool_argv("build", "--locked") == [
        "targo", "--unverified", "build", "--locked",
    ]
    # targo refuses `--unverified` on a non-compilation command.
    assert harness_targets.build_tool_argv("metadata", "--locked") == [
        "targo", "metadata", "--locked",
    ]
    assert harness_targets.compiler_tool() == "trustc"
    monkeypatch.setenv("CARGO", "/opt/trust/bin/targo")
    assert harness_targets.build_tool_argv("check") == [
        "/opt/trust/bin/targo", "--unverified", "check",
    ]
    # A caller's non-targo $CARGO picks its own lane.
    monkeypatch.setenv("CARGO", "/opt/other/bin/cargo")
    assert harness_targets.build_tool_argv("check") == ["/opt/other/bin/cargo", "check"]


@pytest.mark.parametrize("command", ["/opt/trust/bin/targo", "/opt/trust/bin/trustc"])
def test_tool_identity_uses_the_closed_native_metadata_query(monkeypatch, command):
    monkeypatch.setenv("BUILD_SLOT_CPU_PROTOCOL", "3")
    identity = b"commit-hash: fixture\nhost: fixture\nrelease: fixture\n"
    calls = []

    def query(argv, **kwargs):
        calls.append(argv)
        assert kwargs == {"stderr": subprocess.STDOUT}
        assert os.environ["BUILD_SLOT_CPU_PROTOCOL"] == "3"
        return identity

    monkeypatch.setattr(harness_targets.subprocess, "check_output", query)

    assert harness_targets._tool_identity(command) == identity
    assert calls == [[command, "-vV"]]


@pytest.mark.parametrize(
    "error",
    [
        OSError("compiler unavailable"),
        subprocess.CalledProcessError(75, ["trustc", "-vV"], output=b"custody refused"),
    ],
)
def test_tool_identity_fails_closed_without_retry_or_fallback(monkeypatch, error):
    calls = []

    def query(argv, **kwargs):
        calls.append(argv)
        assert kwargs == {"stderr": subprocess.STDOUT}
        raise error

    monkeypatch.setattr(harness_targets.subprocess, "check_output", query)

    with pytest.raises(RuntimeError, match="cannot fingerprint build tool trustc") as raised:
        harness_targets._tool_identity("trustc")
    assert raised.value.__cause__ is error
    assert calls == [["trustc", "-vV"]]


def test_the_offline_retry_goes_after_the_subcommand(monkeypatch, tmp_path):
    """`targo --unverified build`: the retry's `--offline` must follow `build`,
    not split the lane from its subcommand."""
    monkeypatch.delenv("CARGO", raising=False)
    calls = []

    class RecordingSubprocess:
        @staticmethod
        def run(cmd, **kwargs):
            calls.append(cmd)
            if cmd[:2] == ["git", "checkout"]:
                return SimpleNamespace(returncode=0, stdout="", stderr="")
            if len(calls) == 1:
                return SimpleNamespace(
                    returncode=101, stdout="", stderr="error: cannot update the lock file"
                )
            return SimpleNamespace(returncode=0, stdout="", stderr="")

    harness = SimpleNamespace(subprocess=RecordingSubprocess)
    cmd = harness_targets.build_tool_argv("build", "--locked", "-p", "trust-wp-driver")
    result = harness_runner._run_cargo_build(harness, cmd, tmp_path, verbose=False)

    assert result.returncode == 0
    assert calls[1] == ["targo", "--unverified", "build", "--offline", "-p", "trust-wp-driver"]


def _seed_harness_provenance_workspace(monkeypatch, tmp_path: Path) -> Path:
    """Create a clean git workspace with ignored synthetic harness binaries."""
    for key in ("CARGO_TARGET_DIR", "AI_ROLE", "AI_WORKER_ID"):
        monkeypatch.delenv(key, raising=False)
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    (workspace / "Cargo.toml").write_text(
        '[package]\nname = "fixture"\nversion = "0.1.0"\n', encoding="utf-8"
    )
    (workspace / "Cargo.lock").write_text("version = 4\n", encoding="utf-8")
    (workspace / ".gitignore").write_text("/target/\n", encoding="utf-8")
    subprocess.run(["git", "init", "-q", str(workspace)], check=True)
    subprocess.run(
        ["git", "-C", str(workspace), "config", "user.email", "harness@test.invalid"],
        check=True,
    )
    subprocess.run(
        ["git", "-C", str(workspace), "config", "user.name", "Harness Test"],
        check=True,
    )
    subprocess.run(["git", "-C", str(workspace), "add", "."], check=True)
    subprocess.run(
        ["git", "-C", str(workspace), "commit", "-q", "-m", "fixture"],
        check=True,
    )
    binary_dir = workspace / "target" / "debug"
    binary_dir.mkdir(parents=True)
    (binary_dir / "cargo-trust-wp").write_bytes(b"cargo fixture\n")
    (binary_dir / "trust-wp-rustc").write_bytes(b"driver fixture\n")
    return workspace


def test_skip_prebuild_accepts_only_provenance_bound_binaries(
    monkeypatch, tmp_path
):
    workspace = _seed_harness_provenance_workspace(monkeypatch, tmp_path)
    harness._write_harness_binary_provenance(workspace)
    monkeypatch.setenv("TRUST_WP_HARNESS_SKIP_PREBUILD", "1")
    monkeypatch.setattr(
        harness,
        "_runner_ensure_harness_binaries",
        lambda *_args, **_kwargs: pytest.fail("skip-prebuild unexpectedly rebuilt"),
    )
    harness.ensure_harness_binaries(workspace, verbose=False)


def test_skip_prebuild_rejects_missing_provenance(monkeypatch, tmp_path):
    workspace = _seed_harness_provenance_workspace(monkeypatch, tmp_path)
    monkeypatch.setenv("TRUST_WP_HARNESS_SKIP_PREBUILD", "1")
    with pytest.raises(RuntimeError, match="missing build provenance"):
        harness.ensure_harness_binaries(workspace, verbose=False)


def test_skip_prebuild_rejects_source_drift(monkeypatch, tmp_path):
    workspace = _seed_harness_provenance_workspace(monkeypatch, tmp_path)
    harness._write_harness_binary_provenance(workspace)
    (workspace / "Cargo.toml").write_text(
        '[package]\nname = "fixture"\nversion = "0.2.0"\n', encoding="utf-8"
    )
    monkeypatch.setenv("TRUST_WP_HARNESS_SKIP_PREBUILD", "1")
    with pytest.raises(RuntimeError, match="source/dependency/toolchain fingerprint changed"):
        harness.ensure_harness_binaries(workspace, verbose=False)


def test_harness_fingerprint_ignores_how_the_build_tool_is_spelled(monkeypatch, tmp_path):
    """One toolchain, one fingerprint: under targo `$CARGO` is targo's absolute
    path, from a shell it is unset and the harness runs bare `targo`. Skip-
    prebuild provenance written in one context must hold in the other, and a
    different toolchain identity must still move the fingerprint."""
    workspace = _seed_harness_provenance_workspace(monkeypatch, tmp_path)
    monkeypatch.delenv("RUSTC", raising=False)
    identities = {"targo": b"targo (commit A)", "trustc": b"trustc (commit A)"}
    monkeypatch.setattr(
        harness_targets, "_tool_identity", lambda command: identities[Path(command).name]
    )
    monkeypatch.delenv("CARGO", raising=False)
    from_shell = harness_targets._harness_source_fingerprint(workspace)
    monkeypatch.setenv("CARGO", "/opt/trust/bin/targo")
    assert harness_targets._harness_source_fingerprint(workspace) == from_shell
    identities["targo"] = b"targo (commit B)"
    assert harness_targets._harness_source_fingerprint(workspace) != from_shell


def test_skip_prebuild_rejects_binary_drift(monkeypatch, tmp_path):
    workspace = _seed_harness_provenance_workspace(monkeypatch, tmp_path)
    harness._write_harness_binary_provenance(workspace)
    stale_driver = workspace / "target" / "debug" / "trust-wp-rustc"
    stale_driver.write_bytes(b"tampered\n")
    assert stale_driver.is_file()
    monkeypatch.setenv("TRUST_WP_HARNESS_SKIP_PREBUILD", "1")
    with pytest.raises(RuntimeError, match="bytes differ from build provenance"):
        harness.ensure_harness_binaries(workspace, verbose=False)


def test_inherited_skip_prebuild_rejects_stale_existing_executable(
    monkeypatch, tmp_path
):
    """A child harness must not trust a stale binary via inherited bypass state."""
    workspace = _seed_harness_provenance_workspace(monkeypatch, tmp_path)
    harness._write_harness_binary_provenance(workspace)
    stale_driver = workspace / "target" / "debug" / "trust-wp-rustc"
    stale_driver.write_bytes(b"stale but executable\n")
    stale_driver.chmod(0o755)
    assert stale_driver.is_file()

    env = dict(os.environ)
    env["TRUST_WP_HARNESS_SKIP_PREBUILD"] = "1"
    result = subprocess.run(
        [
            sys.executable,
            "-c",
            (
                "import sys; from pathlib import Path; "
                "from tests.creusot_compat import harness; "
                "harness.ensure_harness_binaries(Path(sys.argv[1]), False)"
            ),
            str(workspace),
        ],
        cwd=WORKSPACE_ROOT,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode != 0
    assert "bytes differ from build provenance" in result.stderr


def test_fixture_verification_command_is_locked(tmp_path, monkeypatch):
    """The actual cargo-trust-wp fixture subprocess must consume Cargo.lock."""
    monkeypatch.delenv("TRUST_WP_HARNESS_SOLVER_TIMEOUT", raising=False)
    calls = []

    class FinishedProcess:
        returncode = 0

        @staticmethod
        def communicate(timeout=None):
            # The harness wall (-t) stays the process kill-timeout ...
            assert timeout == 17
            return "trust-wp: 1 verified, 0 failed, 0 errors\n", ""

    class RecordingSubprocess:
        PIPE = subprocess.PIPE
        TimeoutExpired = subprocess.TimeoutExpired
        SubprocessError = subprocess.SubprocessError

        @staticmethod
        def Popen(cmd, **kwargs):
            calls.append((cmd, kwargs))
            return FinishedProcess()

    facade = SimpleNamespace(
        subprocess=RecordingSubprocess,
        _verification_run_succeeded=lambda returncode, _output: returncode == 0,
    )
    binary = tmp_path / "cargo-trust-wp"
    project = tmp_path / "project"
    project.mkdir()

    success, _output, _duration_ms, exit_code = harness_runner._execute_cargo_trust_wp(
        facade,
        binary,
        project,
        {"CARGO_TARGET_DIR": str(tmp_path / "fixture-target")},
        17,
        tmp_path,
    )

    assert success is True
    assert exit_code == 0
    # ... while --timeout carries the DERIVED per-obligation solver budget
    # (#2708): for a 17s wall the derivation floors at 15s then caps at
    # wall // 2 = 8s so the driver watchdog (1.5 x B + 0.1s) still fires
    # inside the wall.
    assert calls[0][0] == [
        str(binary),
        "--verbose",
        "--timeout",
        "8",
        "--locked",
    ]


def test_derive_solver_timeout_restores_watchdog_inside_wall(monkeypatch):
    """The derived solver budget keeps every driver envelope inside the wall.

    Invariant (#2708): wall >= compile margin (20s) + 5 x B (driver crate
    wall, #2674) + 1.5 x B + 0.1s (driver watchdog envelope).  Passing the
    wall itself as --timeout breaks it: the watchdog at 1.5 x wall could
    NEVER fire before the process kill at the wall.
    """
    monkeypatch.delenv("TRUST_WP_HARNESS_SOLVER_TIMEOUT", raising=False)
    # The standard walls: SS lane, per-test overrides, SF lane, default.
    assert harness_runner._derive_solver_timeout_sec(600) == 89
    assert harness_runner._derive_solver_timeout_sec(300) == 43
    assert harness_runner._derive_solver_timeout_sec(200) == 27
    assert harness_runner._derive_solver_timeout_sec(120) == 15
    # Floor at the driver's 15s adaptive floor once the wall allows it.
    assert harness_runner._derive_solver_timeout_sec(60) == 15
    # Tiny walls: the watchdog-inside-wall cap (wall // 2) wins over the floor.
    assert harness_runner._derive_solver_timeout_sec(17) == 8
    assert harness_runner._derive_solver_timeout_sec(3) == 1
    for wall in (3, 17, 60, 120, 200, 300, 600, 1800):
        budget = harness_runner._derive_solver_timeout_sec(wall)
        assert budget >= 1
        # The watchdog envelope must fire inside the wall.
        assert 1.5 * budget + 0.1 < wall or wall <= 2


def test_derive_solver_timeout_env_override_still_capped(monkeypatch):
    """TRUST_WP_HARNESS_SOLVER_TIMEOUT overrides the derivation, not the cap."""
    monkeypatch.setenv("TRUST_WP_HARNESS_SOLVER_TIMEOUT", "60")
    assert harness_runner._derive_solver_timeout_sec(600) == 60
    # The override cannot defeat the watchdog-inside-wall invariant.
    monkeypatch.setenv("TRUST_WP_HARNESS_SOLVER_TIMEOUT", "1000")
    assert harness_runner._derive_solver_timeout_sec(600) == 300
    # Junk values fall back to the derivation.
    monkeypatch.setenv("TRUST_WP_HARNESS_SOLVER_TIMEOUT", "not-a-number")
    assert harness_runner._derive_solver_timeout_sec(600) == 89


def test_review_gate_rejects_harness_binary_reuse_env(tmp_path):
    """The public review cannot inherit the development prebuild bypass."""
    env = dict(os.environ)
    env["TRUST_WP_HARNESS_SKIP_PREBUILD"] = "1"
    result = subprocess.run(
        [
            "bash",
            str(WORKSPACE_ROOT / "scripts" / "creusot_replacement_review.sh"),
            "--mode",
            "workspace",
            "--artifact-dir",
            str(tmp_path / "review"),
        ],
        cwd=WORKSPACE_ROOT,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode != 0
    assert "TRUST_WP_HARNESS_SKIP_PREBUILD is forbidden" in result.stderr


def test_review_gate_rejects_shared_fixture_target_env(tmp_path):
    """The public review cannot inherit an unbound fixture target cache."""
    env = dict(os.environ)
    env.pop("TRUST_WP_HARNESS_SKIP_PREBUILD", None)
    env["TRUST_WP_HARNESS_TARGET_DIR"] = str(tmp_path / "stale-target")
    result = subprocess.run(
        [
            "bash",
            str(WORKSPACE_ROOT / "scripts" / "creusot_replacement_review.sh"),
            "--mode",
            "workspace",
            "--artifact-dir",
            str(tmp_path / "review"),
        ],
        cwd=WORKSPACE_ROOT,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode != 0
    assert "TRUST_WP_HARNESS_TARGET_DIR is forbidden" in result.stderr


def test_review_no_bypass_scan_rejects_rust_ignore(tmp_path):
    """The scan result must survive logging and reject a discovered ignore."""
    script = (WORKSPACE_ROOT / "scripts" / "creusot_replacement_review.sh").read_text()
    start = script.index("run_no_bypass_scans() {")
    end = script.index("\n}\n\nrecord_repo_state()", start) + len("\n}")
    function_source = script[start:end]

    project = tmp_path / "project"
    artifact_dir = tmp_path / "artifacts"
    (project / "crates").mkdir(parents=True)
    (artifact_dir / "logs").mkdir(parents=True)
    (project / "crates" / "ignored.rs").write_text(
        "#[test]\n#[ignore]\nfn deliberately_ignored() {}\n"
    )

    result = subprocess.run(
        [
            "bash",
            "-c",
            "\n".join(
                [
                    "set -euo pipefail",
                    'fail() { printf "ERROR: %s\\n" "$*" >&2; exit 1; }',
                    function_source,
                    "run_no_bypass_scans",
                ]
            ),
        ],
        env={
            **os.environ,
            "PROJECT_DIR": str(project),
            "ARTIFACT_DIR": str(artifact_dir),
        },
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode != 0
    assert "forbidden test ignores found" in result.stderr
    assert "#[ignore]" in (artifact_dir / "logs" / "find-ignores.log").read_text()


def test_review_no_bypass_scan_rejects_ignored_rustdoc_fence(tmp_path):
    """An ignored Rustdoc fence is a skipped test and must fail the review."""
    script = (WORKSPACE_ROOT / "scripts" / "creusot_replacement_review.sh").read_text()
    start = script.index("run_no_bypass_scans() {")
    end = script.index("\n}\n\nrecord_repo_state()", start) + len("\n}")
    function_source = script[start:end]

    project = tmp_path / "project"
    artifact_dir = tmp_path / "artifacts"
    (project / "crates").mkdir(parents=True)
    (artifact_dir / "logs").mkdir(parents=True)
    (project / "crates" / "ignored_doc.rs").write_text(
        "/// ```ignore\n/// unbuildable_example();\n/// ```\n"
    )

    result = subprocess.run(
        [
            "bash",
            "-c",
            "\n".join(
                [
                    "set -euo pipefail",
                    'fail() { printf "ERROR: %s\\n" "$*" >&2; exit 1; }',
                    function_source,
                    "run_no_bypass_scans",
                ]
            ),
        ],
        env={
            **os.environ,
            "PROJECT_DIR": str(project),
            "ARTIFACT_DIR": str(artifact_dir),
        },
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode != 0
    assert "forbidden test ignores found" in result.stderr
    assert "```ignore" in (
        artifact_dir / "logs" / "find-ignores.log"
    ).read_text()


def test_review_no_bypass_scan_fails_when_tracked_scan_cannot_run(tmp_path):
    """A git-grep execution error must not be reported as a clean scan."""
    script = (WORKSPACE_ROOT / "scripts" / "creusot_replacement_review.sh").read_text()
    start = script.index("run_no_bypass_scans() {")
    end = script.index("\n}\n\nrecord_repo_state()", start) + len("\n}")
    function_source = script[start:end]

    project = tmp_path / "not-a-repository"
    artifact_dir = tmp_path / "artifacts"
    for directory in ("crates", "tests", "scripts"):
        (project / directory).mkdir(parents=True)
    (artifact_dir / "logs").mkdir(parents=True)

    result = subprocess.run(
        [
            "bash",
            "-c",
            "\n".join(
                [
                    "set -euo pipefail",
                    'fail() { printf "ERROR: %s\\n" "$*" >&2; exit 1; }',
                    function_source,
                    "run_no_bypass_scans",
                ]
            ),
        ],
        cwd=project,
        env={
            **os.environ,
            "PROJECT_DIR": str(project),
            "ARTIFACT_DIR": str(artifact_dir),
        },
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode != 0
    assert "failed to scan tracked sources" in result.stderr


def test_review_env_mutation_boundary_matches_workspace():
    """The fast boundary check must accept exactly the reviewed startup mutation."""
    script = (WORKSPACE_ROOT / "scripts" / "creusot_replacement_review.sh").read_text()
    start = script.index("require_env_mutation_boundary() {")
    end = script.index("\n}\n\nis_git_repo()", start) + len("\n}")
    function_source = script[start:end]

    result = subprocess.run(
        [
            "bash",
            "-c",
            "\n".join(
                [
                    "set -euo pipefail",
                    'fail() { printf "ERROR: %s\\n" "$*" >&2; exit 1; }',
                    function_source,
                    "require_env_mutation_boundary",
                ]
            ),
        ],
        env={**os.environ, "PROJECT_DIR": str(WORKSPACE_ROOT)},
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode == 0, result.stderr


def test_private_wrapper_rejects_ambiguous_driver_identity(tmp_path):
    """The wrapper must never select an arbitrary rustc_driver library."""
    sysroot_lib = tmp_path / "sysroot" / "lib"
    sysroot_lib.mkdir(parents=True)
    (sysroot_lib / "librustc_driver-aaaa.dylib").touch()
    (sysroot_lib / "librustc_driver-bbbb.so").touch()

    fake_rustc = tmp_path / "fake-rustc"
    fake_rustc.write_text(
        "\n".join(
            [
                "#!/bin/sh",
                'if [ "$1" = "--print" ] && [ "$2" = "sysroot" ]; then',
                '    CDPATH="" cd -- "$(dirname -- "$0")/sysroot"',
                "    pwd",
                "    exit 0",
                "fi",
                "exit 97",
                "",
            ]
        )
    )
    fake_rustc.chmod(0o755)

    result = subprocess.run(
        [
            str(WORKSPACE_ROOT / "scripts" / "trustc-private-wrapper.sh"),
            str(fake_rustc),
            "--crate-name",
            "trust_wp_driver",
            "--emit=metadata",
            "input.rs",
        ],
        cwd=WORKSPACE_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode != 0
    assert "multiple librustc_driver dynamic libraries" in result.stderr


def _private_wrapper_layout(
    tmp_path: Path,
    *,
    candidate_count: int,
) -> tuple[Path, str, str]:
    """Create a minimal fake Trust compiler/private-sysroot topology."""
    compiler_commit = "b" * 40
    driver_hash = hashlib.sha256(str(tmp_path).encode()).hexdigest()[:12]
    triple = "test-triple"
    sysroot = tmp_path / "stage"
    sysroot_lib = sysroot / "lib"
    target_lib = sysroot_lib / "rustlib" / triple / "lib"
    target_lib.mkdir(parents=True)
    (sysroot_lib / f"librustc_driver-{driver_hash}.so").touch()
    (target_lib / "libstd-test.rlib").touch()

    private_root = tmp_path / "rustc-private-sysroots"
    for index in range(candidate_count):
        candidate = private_root / f"candidate-{index}"
        candidate.mkdir(parents=True)
        (candidate / ".rustc-commit-hash").write_text(f"{compiler_commit}\n")
        candidate_lib = candidate / triple
        candidate_lib.mkdir()
        (candidate_lib / f"librustc_driver-{driver_hash}.so").touch()
        (candidate_lib / "librustc_middle-test.rmeta").touch()

    fake_rustc = tmp_path / "fake-rustc"
    fake_rustc.write_text(
        "\n".join(
            [
                "#!/bin/sh",
                'if [ "$1" = "--print" ] && [ "$2" = "sysroot" ]; then',
                f"    printf '%s\\n' '{sysroot}'",
                "    exit 0",
                "fi",
                'if [ "$1" = "--print" ] && [ "$2" = "target-libdir" ]; then',
                f"    printf '%s\\n' '{target_lib}'",
                "    exit 0",
                "fi",
                'if [ "$1" = "-vV" ]; then',
                f"    printf '%s\\n' 'commit-hash: {compiler_commit}'",
                "    exit 0",
                "fi",
                "exit 0",
                "",
            ]
        )
    )
    fake_rustc.chmod(0o755)
    return fake_rustc, driver_hash, compiler_commit


def _cross_private_wrapper_layout(
    tmp_path: Path,
    *,
    driver_suffix: str,
) -> dict[str, Path | str]:
    """Create host + target rustc-private surfaces for a wrapper dry run."""
    compiler_commit = "c" * 40
    host_hash = hashlib.sha256(f"host:{tmp_path}".encode()).hexdigest()[:12]
    cross_hash = hashlib.sha256(f"cross:{tmp_path}".encode()).hexdigest()[:12]
    host_triple = f"host-{host_hash}"
    cross_triple = f"cross-{cross_hash}"
    build_root = tmp_path / "build"
    sysroot = build_root / host_triple / "stage2"
    sysroot_lib = sysroot / "lib"
    host_std = sysroot_lib / "rustlib" / host_triple / "lib"
    cross_std = sysroot_lib / "rustlib" / cross_triple / "lib"
    host_std.mkdir(parents=True)
    cross_std.mkdir(parents=True)
    host_driver = sysroot_lib / f"librustc_driver-{host_hash}.{driver_suffix}"
    host_driver.write_bytes(b"host-driver")
    (host_std / "libstd-host.rlib").touch()
    (cross_std / "libstd-cross.rlib").touch()

    private_root = sysroot.parent / "rustc-private-sysroots"
    host_private_root = private_root / f"rustc-private-tool-stage2-{host_triple}-fixture"
    host_private = host_private_root / host_triple
    host_private.mkdir(parents=True)
    (host_private_root / ".rustc-commit-hash").write_text(f"{compiler_commit}\n")
    (host_private / host_driver.name).write_bytes(host_driver.read_bytes())
    (host_private / "librustc_middle-host.rmeta").touch()

    cross_stage = build_root / cross_triple / "stage2"
    cross_stage_lib = cross_stage / "lib"
    cross_stage_lib.mkdir(parents=True)
    cross_driver = cross_stage_lib / f"librustc_driver-{cross_hash}.{driver_suffix}"
    cross_driver.write_bytes(b"cross-driver")
    cross_private_root = private_root / f"rustc-private-tool-stage2-{cross_triple}-fixture"
    cross_private = cross_private_root / cross_triple
    cross_private.mkdir(parents=True)
    (cross_private_root / ".rustc-commit-hash").write_text(f"{compiler_commit}\n")
    (cross_private / cross_driver.name).write_bytes(cross_driver.read_bytes())
    (cross_private / "librustc_middle-cross.rmeta").touch()
    cross_llvm = build_root / cross_triple / "llvm" / "lib"
    cross_llvm.mkdir(parents=True)

    capture = tmp_path / "rustc-args.txt"
    fake_rustc = tmp_path / "fake-rustc"
    fake_rustc.write_text(
        "\n".join(
            [
                "#!/bin/sh",
                'if [ "$1" = "--print" ] && [ "$2" = "sysroot" ]; then',
                f"    printf '%s\\n' '{sysroot}'",
                "    exit 0",
                "fi",
                'if [ "$1" = "--print" ] && [ "$2" = "target-libdir" ]; then',
                f"    printf '%s\\n' '{host_std}'",
                "    exit 0",
                "fi",
                'if [ "$1" = "-vV" ]; then',
                f"    printf '%s\\n' 'commit-hash: {compiler_commit}'",
                "    exit 0",
                "fi",
                f": > '{capture}'",
                f"for arg in \"$@\"; do printf '%s\\n' \"$arg\" >> '{capture}'; done",
                "exit 0",
                "",
            ]
        )
    )
    fake_rustc.chmod(0o755)
    return {
        "fake_rustc": fake_rustc,
        "capture": capture,
        "host_hash": host_hash,
        "cross_triple": cross_triple,
        "compiler_commit": compiler_commit,
        "host_private": host_private,
        "host_std": host_std,
        "cross_private": cross_private,
        "cross_std": cross_std,
        "cross_llvm": cross_llvm,
        "cross_native": cross_stage_lib,
        "private_root": private_root,
        "cross_driver": cross_driver,
    }


def _remove_cross_wrapper_artifacts(layout: dict[str, Path | str]) -> None:
    """Remove the repository-local cache/overlay made by a cross dry run."""
    cross_triple = str(layout["cross_triple"])
    host_hash = str(layout["host_hash"])
    compiler_commit = str(layout["compiler_commit"])
    cache = WORKSPACE_ROOT / "target" / f".trust-private-env-{cross_triple}"
    overlay = (
        WORKSPACE_ROOT
        / "target"
        / f"trust-private-sysroot-{host_hash}-{compiler_commit}-{cross_triple}"
    )
    cache.unlink(missing_ok=True)
    shutil.rmtree(overlay, ignore_errors=True)
    shutil.rmtree(Path(f"{overlay}.lock"), ignore_errors=True)


@pytest.mark.parametrize(
    ("driver_suffix", "relative_rpath"),
    [("dylib", "@executable_path/../lib"), ("so", "$ORIGIN/../lib")],
)
def test_private_wrapper_stages_and_links_cross_target_surface(
    tmp_path, driver_suffix, relative_rpath
):
    """Cross driver units must use target std/private/native paths exclusively."""
    layout = _cross_private_wrapper_layout(tmp_path, driver_suffix=driver_suffix)
    _remove_cross_wrapper_artifacts(layout)
    command = [
        str(WORKSPACE_ROOT / "scripts" / "trustc-private-wrapper.sh"),
        str(layout["fake_rustc"]),
        "--target",
        str(layout["cross_triple"]),
        "--crate-name",
        "trust_wp_driver",
        "--crate-type",
        "bin",
    ]
    try:
        for _ in range(2):  # slow assembly, then the per-target cache fast path
            result = subprocess.run(
                command,
                cwd=WORKSPACE_ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            assert result.returncode == 0, result.stderr
            args = Path(layout["capture"]).read_text().splitlines()
            rendered = "\n".join(args)
            assert f"-L\n{layout['cross_llvm']}" in rendered
            assert f"-L\n{layout['cross_native']}" in rendered
            assert str(layout["cross_private"]) in rendered
            assert str(layout["cross_std"]) in rendered
            assert str(layout["host_private"]) not in rendered
            assert str(layout["host_std"]) not in rendered
            assert f"-Clink-arg=-Wl,-rpath,{relative_rpath}" in args

        overlay = (
            WORKSPACE_ROOT
            / "target"
            / (
                f"trust-private-sysroot-{layout['host_hash']}-"
                f"{layout['compiler_commit']}-{layout['cross_triple']}"
            )
            / "lib"
            / "rustlib"
            / str(layout["cross_triple"])
            / "lib"
        )
        assert (overlay / "libstd-cross.rlib").exists()
        assert (overlay / Path(layout["cross_driver"]).name).exists()
        assert (overlay / "librustc_middle-cross.rmeta").exists()
    finally:
        _remove_cross_wrapper_artifacts(layout)


def test_private_wrapper_rejects_ambiguous_cross_private_sysroots(tmp_path):
    """Cross metadata selection must not fall back to private-root order."""
    layout = _cross_private_wrapper_layout(tmp_path, driver_suffix="dylib")
    duplicate_root = (
        Path(layout["private_root"])
        / f"duplicate-{layout['cross_triple']}-fixture"
    )
    duplicate = duplicate_root / str(layout["cross_triple"])
    duplicate.mkdir(parents=True)
    cross_driver = Path(layout["cross_driver"])
    (duplicate / cross_driver.name).write_bytes(cross_driver.read_bytes())
    (duplicate / "librustc_middle-duplicate.rmeta").touch()
    _remove_cross_wrapper_artifacts(layout)
    try:
        result = subprocess.run(
            [
                str(WORKSPACE_ROOT / "scripts" / "trustc-private-wrapper.sh"),
                str(layout["fake_rustc"]),
                "--target",
                str(layout["cross_triple"]),
                "--crate-name",
                "trust_wp_driver",
            ],
            cwd=WORKSPACE_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        assert result.returncode != 0
        assert "multiple byte-identical private sysroots match the cross driver" in result.stderr
    finally:
        _remove_cross_wrapper_artifacts(layout)


def test_private_wrapper_rejects_target_spec_paths_before_cache_use(tmp_path):
    """A JSON target path must not become part of an overlay/cache pathname."""
    target_spec = tmp_path / "custom-target.json"
    target_spec.write_text("{}")
    result = subprocess.run(
        [
            str(WORKSPACE_ROOT / "scripts" / "trustc-private-wrapper.sh"),
            sys.executable,  # Invalid targets must be refused before compiler probing.
            "--target",
            str(target_spec),
            "--crate-name",
            "trust_wp_driver",
            "--emit=metadata",
            "input.rs",
        ],
        cwd=WORKSPACE_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode != 0
    assert "--target must name an installed target triple" in result.stderr


def test_private_wrapper_rejects_ambiguous_private_sysroots(tmp_path):
    """Two matching private sysroots must not be resolved by directory order."""
    fake_rustc, _, _ = _private_wrapper_layout(tmp_path, candidate_count=2)

    result = subprocess.run(
        [
            str(WORKSPACE_ROOT / "scripts" / "trustc-private-wrapper.sh"),
            str(fake_rustc),
            "--crate-name",
            "trust_wp_driver",
            "--emit=metadata",
            "input.rs",
        ],
        cwd=WORKSPACE_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode != 0
    assert "multiple byte-identical private sysroots match compiler" in result.stderr


def test_private_wrapper_does_not_reclaim_observed_stale_lock(tmp_path):
    """A waiter must not delete a lock that could have been concurrently replaced."""
    fake_rustc, driver_hash, compiler_commit = _private_wrapper_layout(
        tmp_path,
        candidate_count=1,
    )
    overlay = (
        WORKSPACE_ROOT
        / "target"
        / f"trust-private-sysroot-{driver_hash}-{compiler_commit}"
    )
    lock = Path(f"{overlay}.lock")
    shutil.rmtree(overlay, ignore_errors=True)
    shutil.rmtree(lock, ignore_errors=True)
    lock.mkdir(parents=True)
    stale_owner = "999999999"
    (lock / "pid").write_text(f"{stale_owner}\n")

    process = subprocess.Popen(
        [
            str(WORKSPACE_ROOT / "scripts" / "trustc-private-wrapper.sh"),
            str(fake_rustc),
            "--crate-name",
            "trust_wp_driver",
            "--emit=metadata",
            "input.rs",
        ],
        cwd=WORKSPACE_ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    try:
        time.sleep(0.4)
        if process.poll() is not None:
            stdout, stderr = process.communicate()
            pytest.fail(
                "wrapper reclaimed an observed lock instead of waiting:\n"
                f"stdout={stdout}\nstderr={stderr}"
            )
        assert lock.is_dir()
        assert (lock / "pid").read_text().strip() == stale_owner
    finally:
        process.terminate()
        try:
            process.communicate(timeout=2)
        except subprocess.TimeoutExpired:
            process.kill()
            process.communicate()
        shutil.rmtree(lock, ignore_errors=True)
        shutil.rmtree(overlay, ignore_errors=True)


def test_driver_has_no_suppressed_proof_by_scaffold():
    """Unwired authored-proof code must not survive behind dead-code allows."""
    source = (
        WORKSPACE_ROOT / "crates" / "trust-wp-driver" / "src" / "proof_assert.rs"
    ).read_text()
    forbidden = (
        "#[allow(dead_code)]",
        "struct ProofBy",
        "find_proof_bys_in_mir",
        "get_proof_by_text_from_def_id",
        "mod authored_lane",
        "grade_proof_by",
    )

    for marker in forbidden:
        assert marker not in source, f"unconsumed proof-by scaffold remains: {marker}"


def _review_dependency_validator_source() -> str:
    """Return the exact embedded dependency validator used by the review."""
    script = (WORKSPACE_ROOT / "scripts" / "creusot_replacement_review.sh").read_text()
    marker = (
        'python3 - "$PROJECT_DIR" "${AY_DIR:-}" "${TRUST_IR_DIR:-}" '
        '"${EXPECT_AY_REF:-}" "${EXPECT_TRUST_IR_REF:-}" <<\'PY\' > "$out"\n'
    )
    start = script.index(marker) + len(marker)
    end = script.index("\nPY\n}", start)
    return script[start:end]


@pytest.fixture
def review_dependency_fixture(tmp_path):
    """Minimal clean path-AY/git-TrustIR fixture for validator negatives."""
    project = tmp_path / "trust-wp"
    ay = tmp_path / "ay"
    project.mkdir()
    (ay / "Cargo.toml").parent.mkdir(parents=True)
    (ay / "Cargo.toml").write_text(
        '[workspace]\nmembers = ["crates/ay-core", "crates/ay-dpll"]\n'
        '\n[workspace.package]\nversion = "0.1.0"\n',
        encoding="utf-8",
    )
    for crate in ("ay-core", "ay-dpll"):
        crate_dir = ay / "crates" / crate
        crate_dir.mkdir(parents=True)
        (crate_dir / "Cargo.toml").write_text(
            f'[package]\nname = "{crate}"\nversion = "0.1.0"\n'
        )

    subprocess.run(["git", "init", "-q", str(ay)], check=True)
    subprocess.run(
        ["git", "-C", str(ay), "config", "user.email", "review@test.invalid"],
        check=True,
    )
    subprocess.run(
        ["git", "-C", str(ay), "config", "user.name", "Review Test"],
        check=True,
    )
    subprocess.run(["git", "-C", str(ay), "add", "."], check=True)
    subprocess.run(
        ["git", "-C", str(ay), "commit", "-q", "-m", "fixture"],
        check=True,
    )
    subprocess.run(
        [
            "git",
            "-C",
            str(ay),
            "remote",
            "add",
            "origin",
            "https://github.com/alabsystems/ay.git",
        ],
        check=True,
    )
    trust_ir_commit = "1" * 40
    (project / "Cargo.toml").write_text(
        f"""\
[workspace]
members = []

[workspace.dependencies]
trust-ir = {{ git = "https://github.com/alabsystems/trust-ir.git", rev = "{trust_ir_commit}" }}
ay-core = {{ path = "../ay/crates/ay-core" }}
ay-dpll = {{ path = "../ay/crates/ay-dpll" }}
"""
    )
    (project / "Cargo.lock").write_text(
        f"""\
version = 4

[[package]]
name = "trust-ir"
version = "0.1.0"
source = "git+https://github.com/alabsystems/trust-ir.git?rev={trust_ir_commit}#{trust_ir_commit}"

[[package]]
name = "ay-core"
version = "0.1.0"

[[package]]
name = "ay-dpll"
version = "0.1.0"
"""
    )
    return project, ay, trust_ir_commit


def _run_review_dependency_validator(
    project: Path, ay: Path, trust_ir_ref: str, *, ay_ref: str = ""
):
    return subprocess.run(
        [sys.executable, "-", str(project), str(ay), "", ay_ref, trust_ir_ref],
        input=_review_dependency_validator_source(),
        capture_output=True,
        text=True,
        check=False,
    )


def test_review_dependency_validator_accepts_exact_fixture(review_dependency_fixture):
    project, ay, trust_ir_commit = review_dependency_fixture
    ay_commit = subprocess.check_output(
        ["git", "-C", str(ay), "rev-parse", "HEAD"], text=True
    ).strip()
    result = _run_review_dependency_validator(
        project, ay, trust_ir_commit, ay_ref=ay_commit
    )
    assert result.returncode == 0, result.stderr
    assert "cargo_toml_trust_ir_matches_lock: yes" in result.stdout
    assert "sibling_ay_is_path_dep_source_of_truth: yes" in result.stdout
    assert "ay_evidence_version: 0.1.0" in result.stdout
    assert f"ay_evidence_commit: {ay_commit}" in result.stdout
    assert "ay_dependency_evidence_validated: yes" in result.stdout
    assert not (project / "VISION.md").exists()


def test_review_dependency_validator_rejects_wrong_remote(review_dependency_fixture):
    project, ay, trust_ir_commit = review_dependency_fixture
    lock = (project / "Cargo.lock").read_text().replace(
        "github.com/alabsystems/trust-ir.git",
        "github.com/example/trust-ir.git",
    )
    (project / "Cargo.lock").write_text(lock)
    result = _run_review_dependency_validator(project, ay, trust_ir_commit)
    assert result.returncode != 0
    assert "expected github.com/alabsystems/trust-ir" in result.stderr


def test_review_dependency_validator_rejects_selector_drift(review_dependency_fixture):
    project, ay, trust_ir_commit = review_dependency_fixture
    wrong_rev = "2" * 40
    manifest = (project / "Cargo.toml").read_text().replace(
        f'rev = "{trust_ir_commit}"', f'rev = "{wrong_rev}"'
    )
    (project / "Cargo.toml").write_text(manifest)
    result = _run_review_dependency_validator(project, ay, trust_ir_commit)
    assert result.returncode != 0
    assert "does not match Cargo.lock commit" in result.stderr


def test_review_dependency_validator_rejects_moving_manifest_branch(
    review_dependency_fixture,
):
    project, ay, trust_ir_commit = review_dependency_fixture
    manifest = (project / "Cargo.toml").read_text().replace(
        f'rev = "{trust_ir_commit}"', 'branch = "main"'
    )
    (project / "Cargo.toml").write_text(manifest)
    result = _run_review_dependency_validator(project, ay, trust_ir_commit)
    assert result.returncode != 0
    assert "must use an exact rev, not a branch" in result.stderr


def test_review_dependency_validator_rejects_moving_lock_branch(
    review_dependency_fixture,
):
    project, ay, trust_ir_commit = review_dependency_fixture
    lock = (project / "Cargo.lock").read_text().replace(
        f"?rev={trust_ir_commit}", "?branch=main"
    )
    (project / "Cargo.lock").write_text(lock)
    result = _run_review_dependency_validator(project, ay, trust_ir_commit)
    assert result.returncode != 0
    assert "Cargo.lock trust-ir source must use the exact rev selector" in result.stderr


def test_review_dependency_validator_rejects_ay_path_drift(review_dependency_fixture):
    project, ay, trust_ir_commit = review_dependency_fixture
    manifest = (project / "Cargo.toml").read_text().replace(
        'ay-core = { path = "../ay/crates/ay-core" }',
        'ay-core = { path = "../ay/crates/ay-dpll" }',
    )
    (project / "Cargo.toml").write_text(manifest)
    result = _run_review_dependency_validator(project, ay, trust_ir_commit)
    assert result.returncode != 0
    assert "expected" in result.stderr and "ay-core" in result.stderr


def test_review_dependency_validator_rejects_dirty_ay(review_dependency_fixture):
    project, ay, trust_ir_commit = review_dependency_fixture
    (ay / "untracked.txt").write_text("drift\n")
    result = _run_review_dependency_validator(project, ay, trust_ir_commit)
    assert result.returncode != 0
    assert "uncommitted path" in result.stderr


def test_review_dependency_validator_uses_dependencies_despite_stale_document_claims(
    review_dependency_fixture,
):
    project, ay, trust_ir_commit = review_dependency_fixture
    manifest = (project / "Cargo.toml").read_text()
    (project / "Cargo.toml").write_text(
        "# Current AY authority: version=9.9.9 commit=" + "0" * 40 + "\n" + manifest
    )
    (project / "VISION.md").write_text(
        "| trust-wp-ay | Historical prose without dependency authority |\n"
    )
    result = _run_review_dependency_validator(project, ay, trust_ir_commit)
    assert result.returncode == 0, result.stderr
    assert "ay_evidence_version: 0.1.0" in result.stdout


@pytest.mark.parametrize("ay_ref", ["main", "0" * 40])
def test_review_dependency_validator_rejects_ay_expected_ref_drift(
    review_dependency_fixture,
    ay_ref,
):
    project, ay, trust_ir_commit = review_dependency_fixture
    result = _run_review_dependency_validator(
        project, ay, trust_ir_commit, ay_ref=ay_ref
    )
    assert result.returncode != 0
    assert (
        "must be the 40-hex sibling ../ay HEAD commit" in result.stderr
        if ay_ref == "main"
        else "does not match sibling ../ay HEAD" in result.stderr
    )


def test_review_dependency_validator_rejects_wrong_ay_origin(review_dependency_fixture):
    project, ay, trust_ir_commit = review_dependency_fixture
    subprocess.run(
        [
            "git", "-C", str(ay), "remote", "set-url", "origin",
            "https://github.com/example/ay.git",
        ],
        check=True,
    )
    result = _run_review_dependency_validator(project, ay, trust_ir_commit)
    assert result.returncode != 0
    assert "expected github.com/alabsystems/ay" in result.stderr


def test_review_dependency_validator_rejects_stale_ay_lock_version(
    review_dependency_fixture,
):
    project, ay, trust_ir_commit = review_dependency_fixture
    lock = (project / "Cargo.lock").read_text()
    for crate in ("ay-core", "ay-dpll"):
        lock = lock.replace(
            f'name = "{crate}"\nversion = "0.1.0"',
            f'name = "{crate}"\nversion = "0.0.9"',
        )
    (project / "Cargo.lock").write_text(lock)
    result = _run_review_dependency_validator(project, ay, trust_ir_commit)
    assert result.returncode != 0
    assert "does not match sibling package version" in result.stderr


@pytest.mark.parametrize("drift", [None, "origin", "selector", "manifest", "expected"])
def test_review_dependency_validator_requires_exact_git_ay_evidence(
    review_dependency_fixture, drift,
):
    project, ay, trust_ir_commit = review_dependency_fixture
    commit = "3" * 40
    manifest = (project / "Cargo.toml").read_text()
    lock = (project / "Cargo.lock").read_text()
    for crate in ("ay-core", "ay-dpll"):
        manifest = manifest.replace(
            f'{crate} = {{ path = "../ay/crates/{crate}" }}',
            f'{crate} = {{ git = "https://github.com/alabsystems/ay.git", rev = "{commit}" }}',
        )
        lock = lock.replace(
            f'name = "{crate}"\nversion = "0.1.0"',
            f'name = "{crate}"\nversion = "0.1.0"\n'
            f'source = "git+https://github.com/alabsystems/ay.git?rev={commit}#{commit}"',
        )
    if drift == "origin":
        lock = lock.replace("github.com/alabsystems/ay.git", "github.com/example/ay.git")
    elif drift == "selector":
        lock = lock.replace(f"?rev={commit}", "?branch=main")
    elif drift == "manifest":
        manifest = manifest.replace(commit, "4" * 40)
    (project / "Cargo.toml").write_text(manifest)
    (project / "Cargo.lock").write_text(lock)
    result = _run_review_dependency_validator(
        project, ay, trust_ir_commit, ay_ref="4" * 40 if drift == "expected" else commit
    )
    if drift is None:
        assert result.returncode == 0, result.stderr
        assert "ay_dependency_mode: git" in result.stdout
        assert f"ay_evidence_commit: {commit}" in result.stdout
        assert "ay_dependency_evidence_validated: yes" in result.stdout
    else:
        assert result.returncode != 0, result.stdout
        assert "ay" in result.stderr


# ---------------------------------------------------------------------------
# build_run_metadata
# ---------------------------------------------------------------------------


class TestBuildRunMetadata:
    """Tests for the build_run_metadata function."""

    def _make_args(self, **kwargs) -> argparse.Namespace:
        defaults = {
            "verbose": False,
            "filter": None,
            "limit": None,
            "output": None,
            "baseline": False,
            "lane": "should_succeed",
        }
        defaults.update(kwargs)
        return argparse.Namespace(**defaults)

    def test_full_run_metadata(self):
        args = self._make_args()
        meta = harness.build_run_metadata(
            args,
            WORKSPACE_ROOT,
            discovered_count=273,
            executed_count=273,
        )
        assert meta["is_partial"] is False
        assert meta["filter"] is None
        assert meta["limit"] is None
        assert meta["discovered_tests"] == 273
        assert meta["executed_tests"] == 273
        assert "timestamp" in meta
        assert "git_commit" in meta
        assert "command" in meta

    def test_partial_run_with_filter(self):
        args = self._make_args(filter="bug/")
        meta = harness.build_run_metadata(
            args,
            WORKSPACE_ROOT,
            discovered_count=273,
            executed_count=50,
        )
        assert meta["is_partial"] is True
        assert meta["filter"] == "bug/"
        assert meta["limit"] is None
        assert meta["discovered_tests"] == 273
        assert meta["executed_tests"] == 50

    def test_partial_run_with_limit(self):
        args = self._make_args(limit=10)
        meta = harness.build_run_metadata(
            args,
            WORKSPACE_ROOT,
            discovered_count=273,
            executed_count=10,
        )
        assert meta["is_partial"] is True
        assert meta["filter"] is None
        assert meta["limit"] == 10

    def test_partial_run_with_filter_and_limit(self):
        args = self._make_args(filter="bug/", limit=5)
        meta = harness.build_run_metadata(
            args,
            WORKSPACE_ROOT,
            discovered_count=273,
            executed_count=5,
        )
        assert meta["is_partial"] is True
        assert meta["filter"] == "bug/"
        assert meta["limit"] == 5


# ---------------------------------------------------------------------------
# Exit code semantics
# ---------------------------------------------------------------------------


class TestExitCodes:
    """Test harness exit code behavior via subprocess."""

    HARNESS_PATH = str(HARNESS_DIR / "harness.py")

    def test_help_exits_0(self):
        """`--help` should not fail during harness module import."""
        result = subprocess.run(
            [sys.executable, self.HARNESS_PATH, "--help"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 0, (
            f"Expected --help to exit 0, got {result.returncode} with stderr "
            f"{result.stderr!r}"
        )
        assert "Run Creusot compatibility tests against trust-wp" in result.stdout, (
            f"Expected harness help text in stdout, got {result.stdout!r}"
        )
        assert "ImportError" not in result.stderr, (
            f"Expected no import failure in stderr, got {result.stderr!r}"
        )

    def test_partial_run_without_output_exits_3(self):
        """Partial run (--filter) without --output must exit 3."""
        result = subprocess.run(
            [sys.executable, self.HARNESS_PATH, "--filter", "nonexistent"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 3
        assert "require an explicit --output" in result.stderr

    def test_partial_run_with_limit_without_output_exits_3(self):
        """Partial run (--limit) without --output must exit 3."""
        result = subprocess.run(
            [sys.executable, self.HARNESS_PATH, "--limit", "1"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 3
        assert "require an explicit --output" in result.stderr


# ---------------------------------------------------------------------------
# Project helpers
# ---------------------------------------------------------------------------


class TestProjectHelpers:
    """Tests for extracted project helper functions."""

    def test_create_warmup_project_writes_scaffold(self, tmp_path, monkeypatch):
        harness_project = harness.harness_project
        ws_lock_text = (WORKSPACE_ROOT / "Cargo.lock").read_text()
        # Exercise scaffolding and the real lock-subgraph validator without
        # requiring a populated Cargo cache or waiting on another Cargo build.
        # Metadata resolution itself belongs to the locked build integration
        # gate. This stand-in adds only the fixture root to the reviewed graph.
        expected_child_lock = ws_lock_text + '''
[[package]]
name = "creusot_test"
version = "0.1.0"
dependencies = [
 "creusot-contracts",
 "creusot-std",
 "trust-wp",
 "trust-wp-std",
]
'''
        metadata_calls = []

        def metadata(cmd, **kwargs):
            metadata_calls.append(cmd)
            assert kwargs["env"]["CARGO_NET_OFFLINE"] == "true"
            lock_path = Path(kwargs["cwd"]) / "Cargo.lock"
            if "--locked" in cmd:
                assert lock_path.read_text() == expected_child_lock
            else:
                assert lock_path.read_text() == ws_lock_text
                lock_path.write_text(expected_child_lock)
            return SimpleNamespace(returncode=0, stdout="{}", stderr="")

        monkeypatch.setattr(harness_project, "_CHILD_LOCK_CACHE", {})
        monkeypatch.setattr(harness_project.subprocess, "run", metadata)
        project_dir = harness.create_warmup_project(WORKSPACE_ROOT, tmp_path)
        assert metadata_calls == [
            harness_targets.build_tool_argv("metadata", "--format-version", "1"),
            harness_targets.build_tool_argv("metadata", "--locked", "--format-version", "1"),
        ]
        assert project_dir == tmp_path / "test_project", (
            f"Expected warmup project at {tmp_path / 'test_project'}, got {project_dir}"
        )
        assert (project_dir / "Cargo.toml").exists(), (
            f"Expected Cargo.toml in generated project {project_dir}"
        )
        assert (project_dir / "src" / "lib.rs").exists(), (
            f"Expected src/lib.rs in generated project {project_dir}"
        )
        # The fixture lock is DERIVED from the reviewed workspace lockfile (a
        # byte-for-byte copy can never satisfy --locked: the fixture needs a
        # creusot_test root entry and drops packages/dev-edges unreachable
        # from its graph). The derivation itself verifies, fail-closed, that
        # every package is pinned identically to the workspace lock; here we
        # re-assert the observable contract on the written file.
        child_lock_text = (project_dir / "Cargo.lock").read_text()
        assert child_lock_text == expected_child_lock
        harness_project._verify_child_lock_subgraph(child_lock_text, ws_lock_text)
        child_packages = harness_project._parse_lock_packages(child_lock_text)
        assert any(p["name"] == "creusot_test" for p in child_packages), (
            "Fixture lock must contain the creusot_test root entry"
        )
        assert any(p["name"] == "trust-wp" for p in child_packages), (
            "Fixture lock must pin the trust-wp path dependency"
        )
        assert any(
            (project_dir / toolchain_name).exists()
            for toolchain_name in ("rust-toolchain.toml", "rust-toolchain")
        ), f"Expected rust toolchain file copied into {project_dir}"

        lib_rs = (project_dir / "src" / "lib.rs").read_text()
        assert "use trust_wp as _;" in lib_rs, (
            f"Expected warmup source to import trust_wp, got {lib_rs!r}"
        )
        assert "use creusot_contracts as _;" in lib_rs, (
            f"Expected warmup source to import creusot_contracts, got {lib_rs!r}"
        )
        assert "pub fn warmup_dependencies() {}" in lib_rs, (
            f"Expected warmup marker function in generated source, got {lib_rs!r}"
        )

    def test_persistent_array_shim_anchors_depth_and_rc_keys(self):
        source = """
            depth: snapshot!(|_| 0),
            let new_ag = snapshot!(Ag(v@));
            let new_ag = snapshot!(Ag(self@.set(index@, value)));
            pa.depth = snapshot!(pa.depth.set(permcell, pa.depth[*self.permcell@] + 1));
            Self::reroot(&next, auth_id, ghost!(&mut *pa));
            pa.perms.get_ghost(&snapshot!(*inner@)).unwrap();
            pa.perms.get_ghost(&snapshot!(*self.permcell@)).unwrap();
            pa.perms.remove_ghost(&snapshot!(*cur@)).unwrap();
            pa.perms.get_mut_ghost(&snapshot!(*next@)).unwrap();
            let new_d = snapshot!(Int::min(pa.depth.get(*cur@), pa.depth.get(*next@) - 1));
            pa.depth = snapshot!(pa.depth.set(*cur@, *new_d))
        """

        shimmed = harness.apply_test_specific_shims(
            Path("reference/creusot/examples/persistent_array.rs"),
            source,
        )

        def assert_contains(needle: str) -> None:
            assert needle in shimmed, (
                f"Expected persistent_array shim to contain {needle!r}, got {shimmed!r}"
            )

        def assert_not_contains(needle: str) -> None:
            assert needle not in shimmed, (
                f"Expected persistent_array shim to remove {needle!r}, got {shimmed!r}"
            )

        assert_not_contains("depth: snapshot!(|_| 0),")
        assert_contains(
            "depth: Snapshot::capture(&Mapping::<PermCell<Inner<T>>, Int>::cst(Int::ZERO)),"
        )
        assert_not_contains("snapshot!(Ag(v@))")
        assert_contains("snapshot!(Ag((&v)@))")
        assert_contains("Snapshot::capture(&value).into_inner()")
        assert_contains("pa.depth.set(permcell.clone(),")
        assert_not_contains("ghost!(&mut *pa)")
        assert_contains("ghost!(pa.into_inner())")
        assert_not_contains("pa.depth[*self.permcell@]")
        assert_contains("pa.depth.get(self.permcell.as_ref().clone())")
        assert_not_contains("snapshot!(*inner@)")
        assert_contains("snapshot!(inner.as_ref().clone())")
        assert_contains("snapshot!(self.permcell.as_ref().clone())")
        assert_contains("snapshot!(cur.as_ref().clone())")
        assert_contains("snapshot!(next.as_ref().clone())")
        assert_contains("pa.depth.get(cur.as_ref().clone())")
        assert_contains("pa.depth.get(next.as_ref().clone())")
        assert_contains("pa.depth.set(cur.as_ref().clone(), *new_d)")


# ---------------------------------------------------------------------------
# Canonical output path constant
# ---------------------------------------------------------------------------


def test_canonical_output_path():
    assert harness.CANONICAL_OUTPUT == "tests/creusot_compat/results.json", (
        f"Expected should_succeed canonical output path, got {harness.CANONICAL_OUTPUT!r}"
    )
    assert (
        harness.CANONICAL_SHOULD_FAIL_OUTPUT
        == "tests/creusot_compat/results-should-fail.json"
    ), (
        "Expected should_fail canonical output path, got "
        f"{harness.CANONICAL_SHOULD_FAIL_OUTPUT!r}"
    )
    assert (
        harness.CANONICAL_EXAMPLES_OUTPUT
        == "tests/creusot_compat/results-examples.json"
    ), (
        "Expected examples canonical output path, got "
        f"{harness.CANONICAL_EXAMPLES_OUTPUT!r}"
    )

def test_canonical_results_outputs_are_not_gitignored():
    """Canonical lane artifacts must stay visible after refresh.

    Local exploratory outputs use the same ``results-*.json`` prefix and remain
    ignored, but the canonical should-fail and examples lane files must be
    addable without ``git add -f``.
    """

    canonical_paths = [
        "tests/creusot_compat/results-should-fail.json",
        "tests/creusot_compat/results-examples.json",
    ]
    for rel_path in canonical_paths:
        result = subprocess.run(
            ["git", "check-ignore", "--no-index", rel_path],
            cwd=WORKSPACE_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        assert result.returncode == 1, (
            f"{rel_path} should not be ignored; stdout={result.stdout!r} "
            f"stderr={result.stderr!r}"
        )

    adhoc = subprocess.run(
        ["git", "check-ignore", "--no-index", "tests/creusot_compat/results-slot12d.json"],
        cwd=WORKSPACE_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert adhoc.returncode == 0, (
        "ad-hoc creusot compat result files should remain ignored; "
        f"stdout={adhoc.stdout!r} stderr={adhoc.stderr!r}"
    )


def test_refresh_baselines_script_updates_all_canonical_outputs():
    script = (WORKSPACE_ROOT / "scripts" / "refresh-baselines.sh").read_text(
        encoding="utf-8"
    )

    assert "--lane should_succeed" in script, (
        "refresh-baselines.sh should refresh the should_succeed lane"
    )
    assert "--lane should_fail" in script, (
        "refresh-baselines.sh should refresh the should_fail lane"
    )
    assert "--lane examples" in script, (
        "refresh-baselines.sh should refresh the examples lane"
    )
    assert script.count("--lane examples") == 1, (
        "refresh-baselines.sh should run the examples lane exactly once"
    )
    assert "ALLOW_DIRTY_ARGS" not in script, (
        "refresh-baselines.sh should not reference the stale undefined dirty args array"
    )
    assert "STAGE_DIR=" in script and "mktemp -d" in script, (
        "refresh-baselines.sh should stage all lane outputs before canonical writes"
    )
    assert '--output "$STAGE_DIR/results-should-fail.json"' in script, (
        "refresh-baselines.sh should stage the should_fail canonical output"
    )
    assert '--output "$STAGE_DIR/results-examples.json"' in script, (
        "refresh-baselines.sh should stage the examples canonical output"
    )
    assert "publish_staged_result" in script, (
        "refresh-baselines.sh should publish staged outputs through atomic file replacement"
    )
    assert (
        'publish_staged_result "$STAGE_DIR/results.json" '
        "tests/creusot_compat/results.json"
    ) in script, (
        "refresh-baselines.sh should publish should_succeed only after all lanes pass"
    )
    assert (
        'publish_staged_result "$STAGE_DIR/results-should-fail.json" '
        "tests/creusot_compat/results-should-fail.json"
    ) in script, (
        "refresh-baselines.sh should publish should_fail only after all lanes pass"
    )
    assert (
        'publish_staged_result "$STAGE_DIR/results-examples.json" '
        "tests/creusot_compat/results-examples.json"
    ) in script, (
        "refresh-baselines.sh should publish examples only after all lanes pass"
    )
    assert "validate_result_artifact" in script, (
        "refresh-baselines.sh should reject non-routing-safe staged artifacts"
    )
    assert "metadata.head_drift_commits" in script, (
        "refresh-baselines.sh should reject staged artifacts with positive head drift"
    )
    assert "require_clean_ay_reference" in script, (
        "refresh-baselines.sh should require clean ay dependency evidence"
    )
    assert "--expect-ay-ref" in script, (
        "refresh-baselines.sh should support pinning the ay checkout"
    )
    assert script.count("--max-head-drift-commits 0") == 3, (
        "refresh-baselines.sh should collect each lane with zero head drift"
    )
    assert script.count("--fail-on-head-drift") == 3, (
        "refresh-baselines.sh should fail closed on head drift for each lane"
    )
    assert "WARNING: metrics update failed" not in script, (
        "metrics/latest.json update failures must be fatal for canonical refresh"
    )
    assert "read_summary tests/creusot_compat/results-examples.json" in script, (
        "refresh-baselines.sh should include examples in the refresh summary"
    )
    assert "! -name 'results-examples.json'" in script, (
        "--clean-adhoc should preserve the examples canonical output"
    )


def test_refresh_baselines_help_documents_operator_path():
    result = subprocess.run(
        [str(WORKSPACE_ROOT / "scripts" / "refresh-baselines.sh"), "--help"],
        cwd=WORKSPACE_ROOT,
        capture_output=True,
        text=True,
        timeout=5,
        check=False,
    )

    assert result.returncode == 0, (
        f"Expected refresh-baselines.sh --help to succeed, got {result.returncode}: "
        f"{result.stderr}"
    )
    assert "Refreshes all canonical lanes:" in result.stdout, (
        f"Expected lane list heading in --help output, got: {result.stdout}"
    )
    assert "should_succeed -> tests/creusot_compat/results.json" in result.stdout, (
        f"Expected should_succeed canonical path in --help output, got: {result.stdout}"
    )
    assert (
        "should_fail    -> tests/creusot_compat/results-should-fail.json"
        in result.stdout
    ), f"Expected should_fail canonical path in --help output, got: {result.stdout}"
    assert "examples       -> tests/creusot_compat/results-examples.json" in result.stdout, (
        f"Expected examples canonical path in --help output, got: {result.stdout}"
    )
    assert "reference/creusot exists, is a git checkout, and is clean" in result.stdout, (
        f"Expected reference/creusot prerequisite in --help output, got: {result.stdout}"
    )
    assert "../ay exists, is a git checkout, and is clean" in result.stdout, (
        f"Expected ay prerequisite in --help output, got: {result.stdout}"
    )
    assert "--expect-ay-ref <sha>" in result.stdout, (
        f"Expected pinned ay ref option in --help output, got: {result.stdout}"
    )
    assert "--expect-creusot-ref <sha>" in result.stdout, (
        f"Expected pinned Creusot ref option in --help output, got: {result.stdout}"
    )
    assert "worktree is clean unless --force is passed" in result.stdout, (
        f"Expected clean worktree prerequisite in --help output, got: {result.stdout}"
    )
    assert "runs --check-baseline-freshness" in result.stdout, (
        f"Expected freshness check note in --help output, got: {result.stdout}"
    )


def _write_regression_baseline(
    workspace: Path,
    rel_path: str,
    *,
    lane: str,
    test_name: str,
) -> None:
    path = workspace / rel_path
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "metadata": {
            "git_commit": "test-head",
            "lane": lane,
        },
        "summary": {
            "pass": 1,
            "fail": 0,
            "unknown": 0,
            "skip": 0,
            "error": 0,
            "total": 1,
        },
        "results": [
            {
                "name": test_name,
                "status": "pass",
                "message": "",
                "duration_ms": 1,
            }
        ],
    }
    path.write_text(json.dumps(payload), encoding="utf-8")


def _copy_regression_scripts(workspace: Path) -> Path:
    scripts_dir = workspace / "scripts"
    scripts_dir.mkdir(parents=True, exist_ok=True)
    for script_name in ("creusot_regression.sh", "compare_baselines.py"):
        shutil.copy2(
            WORKSPACE_ROOT / "scripts" / script_name,
            scripts_dir / script_name,
        )
    return scripts_dir / "creusot_regression.sh"


def _write_compare_payload(path: Path, test_result: dict) -> None:
    _write_compare_payloads(path, [test_result])


def _write_compare_payloads(path: Path, test_results: list[dict]) -> None:
    for test_result in test_results:
        telemetry = test_result.get("telemetry")
        if telemetry is None:
            test_result["telemetry"] = _complete_telemetry(verified=1)
        elif isinstance(telemetry, dict):
            merged = _complete_telemetry(verified=1)
            merged.update(telemetry)
            test_result["telemetry"] = merged

    status_counts = {
        "pass": 0,
        "fail": 0,
        "unknown": 0,
        "skip": 0,
        "error": 0,
        "total": len(test_results),
    }
    for test_result in test_results:
        status = test_result.get("status")
        if status in status_counts:
            status_counts[status] += 1
    payload = {
        "metadata": {
            "git_commit": "synthetic-head",
            "lane": "synthetic",
            "head_drift_max_commits": 0,
            "head_drift_exceeded": False,
        },
        "summary": status_counts,
        "results": test_results,
    }
    path.write_text(json.dumps(payload), encoding="utf-8")


@pytest.mark.parametrize(
    "test_name,result_overrides,expected_fragments",
    [
        pytest.param(
            "tests/synthetic/non_pass.rs",
            {"status": "fail", "message": "trust-wp: failed"},
            ["status='fail'"],
            id="non_pass_status",
        ),
        pytest.param(
            "tests/synthetic/no_replay.rs",
            {"message": "Parse-only (NO_REPLAY): syntax-only test"},
            ["NO_REPLAY parse-only pass"],
            id="no_replay_pass",
        ),
        pytest.param(
            "tests/synthetic/tier3.rs",
            {"verification_tier": "tier3"},
            ["verification_tier='tier3' (expected 'tier2')"],
            id="verification_tier_not_tier2",
        ),
        pytest.param(
            "tests/synthetic/timeout_category.rs",
            {"error_category": "timeout"},
            ["timeout error_category"],
            id="timeout_error_category",
        ),
        pytest.param(
            "tests/synthetic/timeout_skip_reason.rs",
            {"skip_reason": "timeout"},
            ["timeout skip_reason"],
            id="timeout_skip_reason",
        ),
        pytest.param(
            "tests/synthetic/proof_assert_failed.rs",
            {"telemetry": {"proof_assert_failed": 1, "proof_assert_errors": 0}},
            ["telemetry.proof_assert_failed=1"],
            id="proof_assert_failed",
        ),
        pytest.param(
            "tests/synthetic/proof_assert_errors.rs",
            {"telemetry": {"proof_assert_failed": 0, "proof_assert_errors": 2}},
            ["telemetry.proof_assert_errors=2"],
            id="proof_assert_errors",
        ),
        pytest.param(
            "tests/synthetic/trusted.rs",
            {
                "message": "trust-wp: f trusted (skipped)",
                "telemetry": {"trusted": 1, "skipped": 0, "assumed": 0},
            },
            ["non-verifying marker: trusted (skipped)", "telemetry.trusted=1"],
            id="trusted_skipped_marker",
        ),
        pytest.param(
            "tests/synthetic/axiomatized.rs",
            {
                "message": "trust-wp: f is a logic function (axiomatized, not verified)",
                "telemetry": {"trusted": 0, "skipped": 1, "assumed": 0},
            },
            ["non-verifying marker: axiomatized, not verified", "telemetry.skipped=1"],
            id="axiomatized_skipped_marker",
        ),
        pytest.param(
            "tests/synthetic/assumed.rs",
            {
                "message": "trust-wp: f assumed (axiom-only function: proof surface)",
                "telemetry": {"trusted": 0, "skipped": 0, "assumed": 1},
            },
            ["non-verifying marker: assumed (axiom-only function", "telemetry.assumed=1"],
            id="assumed_axiom_only_marker",
        ),
        pytest.param(
            "tests/synthetic/axiom_deps.rs",
            {"telemetry": {"verified_with_axiom_deps": 1}},
            ["telemetry.verified_with_axiom_deps=1"],
            id="verified_with_axiom_deps",
        ),
        pytest.param(
            "tests/synthetic/unverified_axioms.rs",
            {"telemetry": {"unverified_axioms": 1}},
            ["telemetry.unverified_axioms=1"],
            id="unverified_axioms",
        ),
        pytest.param(
            "tests/synthetic/vacuous.rs",
            {"telemetry": {"vacuous": 1}},
            ["telemetry.vacuous=1"],
            id="vacuous_telemetry",
        ),
        pytest.param(
            "tests/synthetic/evidence_gaps.rs",
            {"telemetry": {"evidence_gaps": 1}},
            ["telemetry.evidence_gaps=1"],
            id="evidence_gaps_telemetry",
        ),
        pytest.param(
            "tests/synthetic/assumed_summary.rs",
            {"message": "trust-wp: 1 verified, 0 failed, 0 errors, 1 assumed"},
            ["assumed summary count"],
            id="assumed_summary_count",
        ),
        pytest.param(
            "tests/synthetic/axiom_deps_summary.rs",
            {
                "message": (
                    "trust-wp: 1 verified, 0 failed, 0 errors, "
                    "1 verified* (unproven axiom deps)"
                )
            },
            ["verified with unproven axiom deps"],
            id="verified_axiom_deps_summary_count",
        ),
        pytest.param(
            "tests/synthetic/open_functions.rs",
            {"skip_reason": "open functions"},
            ["unsupported-source skip_reason='open functions'"],
            id="unsupported_source_skip_reason",
        ),
    ],
)
def test_compare_baselines_true_100_gate_fails_identical_bad_current(
    tmp_path,
    test_name,
    result_overrides,
    expected_fragments,
):
    test_result = {
        "name": test_name,
        "status": "pass",
        "message": "trust-wp: ok",
        "duration_ms": 1,
        "skip_reason": None,
        "error_category": None,
    }
    test_result.update(result_overrides)

    baseline_path = tmp_path / "baseline.json"
    current_path = tmp_path / "current.json"
    _write_compare_payload(baseline_path, test_result)
    _write_compare_payload(current_path, test_result)

    completed = subprocess.run(
        [
            sys.executable,
            str(WORKSPACE_ROOT / "scripts" / "compare_baselines.py"),
            str(baseline_path),
            str(current_path),
            "synthetic",
        ],
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )

    assert completed.returncode == 1, (
        "Identical bad baseline/current JSON should fail the strict true-100 "
        f"gate; stdout={completed.stdout!r} stderr={completed.stderr!r}"
    )
    assert "TRUE-100 VIOLATIONS (1)" in completed.stdout, (
        f"Expected strict gate report in stdout, got: {completed.stdout}"
    )
    for expected_fragment in expected_fragments:
        assert expected_fragment in completed.stdout, (
            f"Expected {expected_fragment!r} in stdout, got: {completed.stdout}"
        )


def test_compare_baselines_should_fail_lane_excludes_true_100_tier_gate(tmp_path):
    test_result = {
        "name": "tests/should_fail/bug/false.rs",
        "status": "pass",
        "message": "Correctly rejected",
        "duration_ms": 1,
        "skip_reason": None,
        "error_category": None,
    }

    baseline_path = tmp_path / "baseline.json"
    current_path = tmp_path / "current.json"
    _write_compare_payload(baseline_path, test_result)
    _write_compare_payload(current_path, test_result)

    completed = subprocess.run(
        [
            sys.executable,
            str(WORKSPACE_ROOT / "scripts" / "compare_baselines.py"),
            str(baseline_path),
            str(current_path),
            "should_fail",
        ],
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )

    assert completed.returncode == 0, (
        "should_fail pass results intentionally have no verification_tier; "
        f"stdout={completed.stdout!r} stderr={completed.stderr!r}"
    )
    assert "TRUE-100 VIOLATIONS" not in completed.stdout, (
        f"should_fail lane should not run proof-pass true-100 checks: {completed.stdout}"
    )


@pytest.mark.parametrize(
    "result_overrides,expected_fragment",
    [
        pytest.param(
            {"status": "fail", "message": "Verification succeeded"},
            "status='fail' (expected 'pass')",
            id="false_accept_status",
        ),
        pytest.param(
            {"status": "error", "error_category": "timeout"},
            "timeout error_category",
            id="timeout_error",
        ),
        pytest.param(
            {"status": "pass", "telemetry": {"assumed": 1}},
            "telemetry.assumed=1",
            id="soundness_telemetry",
        ),
        pytest.param(
            {"status": "pass", "telemetry": {"evidence_gaps": 1}},
            "telemetry.evidence_gaps=1",
            id="evidence_gaps_telemetry",
        ),
    ],
)
def test_compare_baselines_should_fail_lane_fails_current_result_gaps(
    tmp_path, result_overrides, expected_fragment
):
    test_result = {
        "name": "tests/should_fail/bug/false.rs",
        "status": "pass",
        "message": "Correctly rejected",
        "duration_ms": 1,
        "skip_reason": None,
        "error_category": None,
    }
    test_result.update(result_overrides)

    baseline_path = tmp_path / "baseline.json"
    current_path = tmp_path / "current.json"
    _write_compare_payload(baseline_path, test_result)
    _write_compare_payload(current_path, test_result)

    completed = subprocess.run(
        [
            sys.executable,
            str(WORKSPACE_ROOT / "scripts" / "compare_baselines.py"),
            str(baseline_path),
            str(current_path),
            "should_fail",
        ],
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )

    assert completed.returncode == 1, (
        "should_fail current-result gaps should fail strict comparison even "
        f"when baseline and current match; stdout={completed.stdout!r} "
        f"stderr={completed.stderr!r}"
    )
    assert expected_fragment in completed.stdout, (
        f"Expected {expected_fragment!r} in stdout, got: {completed.stdout}"
    )


@pytest.mark.parametrize(
    "baseline_results,current_results,expected_fragment",
    [
        pytest.param(
            [
                {
                    "name": "tests/synthetic/covered.rs",
                    "status": "pass",
                    "message": "trust-wp: ok",
                    "verification_tier": "tier2",
                }
            ],
            [
                {
                    "name": "tests/synthetic/covered.rs",
                    "status": "pass",
                    "message": "trust-wp: ok",
                    "verification_tier": "tier2",
                },
                {
                    "name": "tests/synthetic/missing-baseline.rs",
                    "status": "pass",
                    "message": "trust-wp: ok",
                    "verification_tier": "tier2",
                },
            ],
            "NEW TESTS (1)",
            id="missing_baseline",
        ),
        pytest.param(
            [
                {
                    "name": "tests/synthetic/covered.rs",
                    "status": "pass",
                    "message": "trust-wp: ok",
                    "verification_tier": "tier2",
                },
                {
                    "name": "tests/synthetic/removed.rs",
                    "status": "pass",
                    "message": "trust-wp: ok",
                    "verification_tier": "tier2",
                },
            ],
            [
                {
                    "name": "tests/synthetic/covered.rs",
                    "status": "pass",
                    "message": "trust-wp: ok",
                    "verification_tier": "tier2",
                }
            ],
            "REMOVED TESTS (1)",
            id="removed_current_result",
        ),
    ],
)
def test_compare_baselines_fails_closed_on_baseline_membership_drift(
    tmp_path, baseline_results, current_results, expected_fragment
):
    baseline_path = tmp_path / "baseline.json"
    current_path = tmp_path / "current.json"
    _write_compare_payloads(baseline_path, baseline_results)
    _write_compare_payloads(current_path, current_results)

    completed = subprocess.run(
        [
            sys.executable,
            str(WORKSPACE_ROOT / "scripts" / "compare_baselines.py"),
            str(baseline_path),
            str(current_path),
            "synthetic",
        ],
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )

    assert completed.returncode == 1, (
        "Baseline membership drift should fail closed; "
        f"stdout={completed.stdout!r} stderr={completed.stderr!r}"
    )
    assert expected_fragment in completed.stdout, (
        f"Expected {expected_fragment!r} in stdout, got: {completed.stdout}"
    )


@pytest.mark.parametrize(
    "metadata_overrides,expected_fragment",
    [
        pytest.param(
            {"head_drift_exceeded": True},
            "metadata.head_drift_exceeded=true",
            id="head_drift_exceeded",
        ),
        pytest.param(
            {"head_drift_max_commits": 3},
            "metadata.head_drift_max_commits=3 (expected 0)",
            id="nonzero_head_drift_policy",
        ),
        pytest.param(
            {"head_drift_commits": 1},
            "metadata.head_drift_commits=1 (expected 0 or absent)",
            id="nonzero_head_drift",
        ),
        pytest.param(
            {"routing_safe": False},
            "metadata.routing_safe=false",
            id="not_routing_safe",
        ),
        pytest.param(
            {"dirty_file_count": 1},
            "metadata.dirty_file_count=1 (expected 0 or absent)",
            id="dirty_file_count",
        ),
        pytest.param(
            {"dirty_files": ["src/lib.rs"]},
            "metadata.dirty_files nonempty (1 file(s))",
            id="dirty_files",
        ),
        pytest.param(
            {"provisional_reason": "head_drift"},
            "metadata.provisional_reason='head_drift'",
            id="provisional_reason",
        ),
    ],
)
def test_compare_baselines_fails_closed_on_current_metadata_gaps(
    tmp_path, metadata_overrides, expected_fragment
):
    test_result = {
        "name": "tests/synthetic/covered.rs",
        "status": "pass",
        "message": "trust-wp: ok",
        "verification_tier": "tier2",
    }
    baseline_path = tmp_path / "baseline.json"
    current_path = tmp_path / "current.json"
    _write_compare_payload(baseline_path, test_result)
    _write_compare_payload(current_path, test_result)

    current_payload = json.loads(current_path.read_text(encoding="utf-8"))
    current_payload["metadata"].update(metadata_overrides)
    current_path.write_text(json.dumps(current_payload), encoding="utf-8")

    completed = subprocess.run(
        [
            sys.executable,
            str(WORKSPACE_ROOT / "scripts" / "compare_baselines.py"),
            str(baseline_path),
            str(current_path),
            "synthetic",
        ],
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )

    assert completed.returncode == 1, (
        "Current artifact metadata gaps should fail closed; "
        f"stdout={completed.stdout!r} stderr={completed.stderr!r}"
    )
    assert "METADATA VIOLATIONS (1)" in completed.stdout, (
        f"Expected metadata violations report, got: {completed.stdout}"
    )
    assert expected_fragment in completed.stdout, (
        f"Expected {expected_fragment!r} in stdout, got: {completed.stdout}"
    )


def test_compare_baselines_fails_closed_when_current_head_drift_metadata_missing(
    tmp_path,
):
    test_result = {
        "name": "tests/synthetic/covered.rs",
        "status": "pass",
        "message": "trust-wp: ok",
        "verification_tier": "tier2",
    }
    baseline_path = tmp_path / "baseline.json"
    current_path = tmp_path / "current.json"
    _write_compare_payload(baseline_path, test_result)
    _write_compare_payload(current_path, test_result)

    current_payload = json.loads(current_path.read_text(encoding="utf-8"))
    current_payload["metadata"].pop("head_drift_exceeded")
    current_path.write_text(json.dumps(current_payload), encoding="utf-8")

    completed = subprocess.run(
        [
            sys.executable,
            str(WORKSPACE_ROOT / "scripts" / "compare_baselines.py"),
            str(baseline_path),
            str(current_path),
            "synthetic",
        ],
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )

    assert completed.returncode == 1, (
        "Missing current head-drift metadata should fail closed; "
        f"stdout={completed.stdout!r} stderr={completed.stderr!r}"
    )
    assert "metadata.head_drift_exceeded missing" in completed.stdout, (
        f"Expected missing head-drift metadata in stdout, got: {completed.stdout}"
    )


@pytest.mark.parametrize(
    "mutate_result,expected_fragment",
    [
        pytest.param(
            lambda result: result.pop("telemetry"),
            "telemetry missing or malformed",
            id="missing_telemetry",
        ),
        pytest.param(
            lambda result: result["telemetry"].pop("evidence_gaps"),
            "telemetry missing field(s): evidence_gaps",
            id="missing_field",
        ),
        pytest.param(
            lambda result: result["telemetry"].__setitem__("future_counter", 1),
            "telemetry unexpected field(s): future_counter",
            id="extra_field",
        ),
        pytest.param(
            lambda result: result["telemetry"].__setitem__("trusted", "1"),
            "telemetry.trusted is not an integer",
            id="string_value",
        ),
        pytest.param(
            lambda result: result["telemetry"].__setitem__("trusted", True),
            "telemetry.trusted is not an integer",
            id="bool_value",
        ),
        pytest.param(
            lambda result: result["telemetry"].__setitem__("trusted", -1),
            "telemetry.trusted is negative",
            id="negative_value",
        ),
    ],
)
def test_compare_baselines_fails_closed_on_current_telemetry_integrity(
    tmp_path, mutate_result, expected_fragment
):
    test_result = {
        "name": "tests/synthetic/covered.rs",
        "status": "pass",
        "message": "trust-wp: ok",
        "verification_tier": "tier2",
    }
    baseline_path = tmp_path / "baseline.json"
    current_path = tmp_path / "current.json"
    _write_compare_payload(baseline_path, test_result)
    _write_compare_payload(current_path, test_result)

    current_payload = json.loads(current_path.read_text(encoding="utf-8"))
    mutate_result(current_payload["results"][0])
    current_path.write_text(json.dumps(current_payload), encoding="utf-8")

    completed = subprocess.run(
        [
            sys.executable,
            str(WORKSPACE_ROOT / "scripts" / "compare_baselines.py"),
            str(baseline_path),
            str(current_path),
            "synthetic",
        ],
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )

    assert completed.returncode == 1, (
        "Current telemetry schema gaps should fail closed; "
        f"stdout={completed.stdout!r} stderr={completed.stderr!r}"
    )
    assert expected_fragment in completed.stdout, (
        f"Expected {expected_fragment!r} in stdout, got: {completed.stdout}"
    )


@pytest.mark.parametrize(
    "mutate_payload,expected_fragment",
    [
        pytest.param(
            lambda payload: payload["results"].append(dict(payload["results"][0])),
            "current.results duplicate name: tests/synthetic/covered.rs",
            id="duplicate_name",
        ),
        pytest.param(
            lambda payload: payload["summary"].__setitem__("total", 99),
            "current.summary.total=99 (expected 1)",
            id="summary_total",
        ),
        pytest.param(
            lambda payload: payload["summary"].__setitem__("pass", 0),
            "current.summary.pass=0 (expected 1)",
            id="summary_status_count",
        ),
    ],
)
def test_compare_baselines_fails_closed_on_artifact_integrity(
    tmp_path, mutate_payload, expected_fragment
):
    test_result = {
        "name": "tests/synthetic/covered.rs",
        "status": "pass",
        "message": "trust-wp: ok",
        "verification_tier": "tier2",
    }
    baseline_path = tmp_path / "baseline.json"
    current_path = tmp_path / "current.json"
    _write_compare_payload(baseline_path, test_result)
    _write_compare_payload(current_path, test_result)

    current_payload = json.loads(current_path.read_text(encoding="utf-8"))
    mutate_payload(current_payload)
    current_path.write_text(json.dumps(current_payload), encoding="utf-8")

    completed = subprocess.run(
        [
            sys.executable,
            str(WORKSPACE_ROOT / "scripts" / "compare_baselines.py"),
            str(baseline_path),
            str(current_path),
            "synthetic",
        ],
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )

    assert completed.returncode == 1, (
        "Artifact structural gaps should fail closed; "
        f"stdout={completed.stdout!r} stderr={completed.stderr!r}"
    )
    assert "ARTIFACT VIOLATIONS" in completed.stdout, (
        f"Expected artifact violation report, got: {completed.stdout}"
    )
    assert expected_fragment in completed.stdout, (
        f"Expected {expected_fragment!r} in stdout, got: {completed.stdout}"
    )


def test_parse_wire_line_preserves_evidence_gaps_counter():
    telemetry = harness.parse_wire_line(_wire_line(verified=1, evidence_gaps=2))

    assert telemetry is not None, "Expected TRUST_WP_RESULT wire line to parse"
    assert telemetry.evidence_gaps == 2, (
        f"Expected evidence_gaps=2, got {telemetry.evidence_gaps!r}"
    )
    assert telemetry.to_dict()["evidence_gaps"] == 2, (
        f"Expected serialized evidence_gaps=2, got {telemetry.to_dict()!r}"
    )


def test_parse_wire_line_rejects_invalid_telemetry_fields():
    assert harness.parse_wire_line(
        "TRUST_WP_RESULT:v1 base_exit_code=0 verified=1 failed=0 errors=0"
    ) is None, "Incomplete wire line should be rejected"
    assert harness.parse_wire_line(
        _wire_line(verified=1).strip() + " verified=1"
    ) is None, "Duplicate telemetry fields should be rejected"
    assert harness.parse_wire_line(
        _wire_line(verified=1).strip().replace("trusted=0", "trusted=no")
    ) is None, "Non-integer telemetry fields should be rejected"
    assert harness.parse_wire_line(
        _wire_line(verified=1).strip().replace("trusted=0", "trusted=-1")
    ) is None, "Negative telemetry fields should be rejected"


def test_parse_wire_line_rejects_future_fields():
    telemetry = harness.parse_wire_line(
        _wire_line(verified=1, evidence_gaps=1).strip() + " future_counter=7"
    )

    assert telemetry is None, "Unexpected future telemetry fields should fail closed"


def test_parse_wire_line_accepts_current_driver_emitter_shape():
    """The exact line the current driver emits (with proof_assert_verified)
    must parse: when parse_wire_line rejects it, every wire-based
    classification carve-out silently collapses to error with no reason."""
    line = (
        "TRUST_WP_RESULT:v1 base_exit_code=2 verified=2 failed=0 errors=0 "
        "warnings=0 assumed=0 trusted=2 skipped=0 verified_with_axiom_deps=0 "
        "unverified_axioms=0 vacuous=0 evidence_gaps=0 proof_assert_verified=3 "
        "proof_assert_failed=0 proof_assert_errors=0 panics=0 demoted=0 "
        "parse_errors=0 termination_errors=0 logic_recursion_errors=0 "
        "erasure_errors=0"
    )
    telemetry = harness.parse_wire_line(line)

    assert telemetry is not None, "Current driver wire line must parse"
    assert telemetry.trusted == 2
    assert telemetry.proof_assert_verified == 3
    assert telemetry.base_exit_code == 2


def test_parse_wire_line_accepts_missing_proof_assert_verified():
    """Lines without the field (older drivers, stored baselines) must keep
    parsing: the field is optional, mirroring the Rust decoder's
    REQUIRED_FIELDS bitmask which claims no bit for it."""
    line = " ".join(
        token
        for token in _wire_line(verified=1, trusted=1).strip().split()
        if not token.startswith("proof_assert_verified=")
    )
    telemetry = harness.parse_wire_line(line)

    assert telemetry is not None, "Pre-field wire line must keep parsing"
    assert telemetry.proof_assert_verified == 0
    assert telemetry.verified == 1
    assert telemetry.trusted == 1


# --- Wire-protocol conformance fixture (#132) -------------------------------
#
# tests/creusot_compat/wire_fields.v1.txt is GENERATED from the Rust manifest
# (trust_wp_core::result_protocol::WIRE_FIELDS_V1 — the same const slice the
# Rust emitter and decoder are driven by) and pinned by a Rust unit test
# (wire_manifest_fixture_matches_code). The tests below pin BOTH Python
# decoders to the same file, so a wire-field change cannot land without
# touching the mirrors — the drift class behind the stale hand-maintained
# tuple documented atop this file and a decoder that lagged the
# proof_assert_verified field. Unknown-field rejection
# stays (test_parse_wire_line_rejects_future_fields): the fixture enforces
# agreement, not tolerance.

WIRE_FIXTURE_PATH = HARNESS_DIR / "wire_fields.v1.txt"


def _load_wire_field_manifest() -> tuple[list[str], list[str]]:
    """Parse the Rust-generated conformance fixture into (required, optional)."""
    sections: dict[str, list[str]] = {"[required]": [], "[optional]": []}
    current: list[str] | None = None
    for raw_line in WIRE_FIXTURE_PATH.read_text().splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if line in sections:
            current = sections[line]
            continue
        assert current is not None, f"fixture field before any section marker: {line!r}"
        current.append(line)
    return sections["[required]"], sections["[optional]"]


def test_wire_fixture_is_well_formed():
    """Both section markers present, non-empty required set, no duplicates,
    no field claimed by both sections."""
    required, optional = _load_wire_field_manifest()

    assert required, "fixture must declare at least one required field"
    assert len(required) == len(set(required)), "duplicate required fields"
    assert len(optional) == len(set(optional)), "duplicate optional fields"
    assert set(required).isdisjoint(optional), "field in both sections"


def test_harness_model_field_sets_match_wire_fixture():
    """harness_model's known/optional field sets must equal the Rust manifest
    exactly — its parse_wire_line rejects unknown fields and fails closed on
    missing required ones, so any inequality is a live decoder split-brain."""
    required, optional = _load_wire_field_manifest()
    from tests.creusot_compat import harness_model

    fixture_known = set(required) | set(optional)
    model_known = set(harness_model.TELEMETRY_FIELD_NAMES)
    assert model_known == fixture_known, (
        "harness_model.TELEMETRY_FIELD_NAMES drifted from the Rust wire manifest: "
        f"missing={sorted(fixture_known - model_known)} "
        f"extra={sorted(model_known - fixture_known)}"
    )

    model_optional = set(harness_model.OPTIONAL_TELEMETRY_FIELDS)
    assert model_optional == set(optional), (
        "harness_model.OPTIONAL_TELEMETRY_FIELDS drifted from the Rust wire manifest: "
        f"missing={sorted(set(optional) - model_optional)} "
        f"extra={sorted(model_optional - set(optional))}"
    )


def test_compare_baselines_field_sets_match_wire_fixture():
    """compare_baselines' telemetry-integrity gate must agree with the Rust
    manifest exactly, or every refreshed baseline flags spurious
    missing/unexpected-field violations (the second drift incident)."""
    required, optional = _load_wire_field_manifest()
    compare_spec = importlib.util.spec_from_file_location(
        "compare_baselines_under_test",
        WORKSPACE_ROOT / "scripts" / "compare_baselines.py",
    )
    compare_baselines = importlib.util.module_from_spec(compare_spec)
    compare_spec.loader.exec_module(compare_baselines)

    fixture_known = set(required) | set(optional)
    script_known = set(compare_baselines.TELEMETRY_FIELD_NAMES)
    assert script_known == fixture_known, (
        "compare_baselines.TELEMETRY_FIELD_NAMES drifted from the Rust wire manifest: "
        f"missing={sorted(fixture_known - script_known)} "
        f"extra={sorted(script_known - fixture_known)}"
    )

    script_optional = set(compare_baselines.OPTIONAL_TELEMETRY_FIELDS)
    assert script_optional == set(optional), (
        "compare_baselines.OPTIONAL_TELEMETRY_FIELDS drifted from the Rust wire "
        f"manifest: missing={sorted(set(optional) - script_optional)} "
        f"extra={sorted(script_optional - set(optional))}"
    )


def test_extract_telemetry_uses_last_complete_wire_line():
    runner = importlib.import_module("tests.creusot_compat.harness_runner")

    telemetry = runner._extract_telemetry(
        _wire_line(verified=1)
        + "middle\n"
        + _wire_line(verified=2, evidence_gaps=1)
    )

    assert telemetry is not None, "Expected last complete wire line to parse"
    assert telemetry.verified == 2, (
        f"Expected last complete verified=2, got {telemetry.verified!r}"
    )
    assert telemetry.evidence_gaps == 1, (
        f"Expected last complete evidence_gaps=1, got {telemetry.evidence_gaps!r}"
    )


def test_extract_telemetry_rejects_malformed_wire_line():
    runner = importlib.import_module("tests.creusot_compat.harness_runner")

    telemetry = runner._extract_telemetry(
        _wire_line(verified=1) + "TRUST_WP_RESULT:v1 base_exit_code=0 verified=2\n"
    )

    assert telemetry is None, "Malformed later wire line must fail closed"


def test_extract_wire_line_pairs_requires_final_wire_line_to_parse():
    succeed = importlib.import_module("tests.creusot_compat.harness_classify_succeed")

    pairs = succeed._extract_wire_line_pairs(
        _wire_line(verified=1) + "TRUST_WP_RESULT:v1 base_exit_code=0 verified=2\n"
    )

    assert pairs is None, "Malformed final wire line must not use earlier telemetry"


@pytest.mark.parametrize(
    "message",
    [
        "Verification succeeded\n" + _wire_line(verified=1, evidence_gaps=1),
        "trust-wp: evidence gap: proof contains inferred fallback evidence",
        "trust-wp: evidence-gap marker emitted for incomplete reconstruction",
    ],
)
def test_verification_tier_evidence_gap_markers_fail_closed(message):
    tier = harness.classify_verification_tier(
        "tests/should_succeed/policy/evidence_gap.rs",
        "pass",
        message,
        None,
        "#[requires(true)]\nfn f() {}",
    )

    assert tier == "tier3", (
        f"Evidence-gap accepted output should fail closed to tier3, got {tier!r}"
    )


def test_creusot_regression_script_rejects_all_no_run(tmp_path):
    script = _copy_regression_scripts(tmp_path)
    _write_regression_baseline(
        tmp_path,
        "tests/creusot_compat/results.json",
        lane="should_succeed",
        test_name="tests/should_succeed/lang/empty.rs",
    )
    _write_regression_baseline(
        tmp_path,
        "tests/creusot_compat/results-should-fail.json",
        lane="should_fail",
        test_name="tests/should_fail/bug/false.rs",
    )
    _write_regression_baseline(
        tmp_path,
        "tests/creusot_compat/results-examples.json",
        lane="examples",
        test_name="examples/sum_first_n.rs",
    )

    result = subprocess.run(
        ["bash", str(script), "--lane", "all", "--no-run"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )

    assert result.returncode != 0, (
        f"Expected no-run all-lane comparison to fail closed, got {result.returncode}: "
        f"stdout={result.stdout} stderr={result.stderr}"
    )
    assert "--no-run is not allowed" in result.stderr, (
        f"Expected strict no-run error in stderr, got: {result.stderr}"
    )


class TestIsSameRelPath:
    """Tests for relative-path canonicalization helper."""

    def test_parent_segments_resolve_to_same_path(self):
        assert harness._is_same_rel_path(
            "tests/creusot_compat/../creusot_compat/results.json",
            harness.CANONICAL_OUTPUT,
        )

    def test_different_paths_are_not_equal(self):
        assert not harness._is_same_rel_path(
            "tests/creusot_compat/results-temp.json",
            harness.CANONICAL_OUTPUT,
        )


# ---------------------------------------------------------------------------
# Lane detection
# ---------------------------------------------------------------------------


class TestIsShouldFailTest:
    """Tests for _is_should_fail_test helper."""

    def test_should_fail_path(self):
        assert harness._is_should_fail_test("tests/should_fail/bad_borrow.rs") is True

    def test_should_fail_nested(self):
        assert harness._is_should_fail_test("tests/should_fail/bug/123.rs") is True

    def test_should_succeed_path(self):
        assert harness._is_should_fail_test("tests/should_succeed/100doors.rs") is False

    def test_examples_path(self):
        assert harness._is_should_fail_test("examples/binary_search.rs") is False, (
            "examples/ paths should not be classified as should_fail"
        )

    def test_examples_nested_path(self):
        assert harness._is_should_fail_test("examples/iterators/01_range.rs") is False, (
            "nested examples/ paths should not be classified as should_fail"
        )


# ---------------------------------------------------------------------------
# classify_should_fail_result
# ---------------------------------------------------------------------------


def test_harness_classifier_exports_track_split_policy_modules():
    signals_module = importlib.import_module(
        "tests.creusot_compat.harness_classify_signals"
    )
    succeed_module = importlib.import_module(
        "tests.creusot_compat.harness_classify_succeed"
    )
    fail_module = importlib.import_module("tests.creusot_compat.harness_classify_fail")

    assert harness._has_rustc_panic is signals_module._has_rustc_panic, (
        "Harness should re-export panic detection from harness_classify_signals.py"
    )
    assert harness.classify_failure is succeed_module.classify_failure, (
        "Harness should re-export should-succeed policy from harness_classify_succeed.py"
    )
    assert harness.classify_should_fail_result is fail_module.classify_should_fail_result, (
        "Harness should re-export should-fail policy from harness_classify_fail.py"
    )


class TestClassifyShouldFailResult:
    """Tests for the should_fail classification logic."""

    def test_expected_reject_is_pass(self):
        """A ``FAILED ✗`` verdict backed by a validated model -> pass."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                _diag_line("bad", "function_contract")
                + "trust-wp: bad FAILED ✗ (counterexample found)\n"
                + _wire_line(failed=1, base_exit_code=1)
            ),
            source="fn bad() {}",
        )
        assert status == "pass"
        assert reason is None, f"Rc source should not produce a skip reason, got {reason!r}"

    def test_bare_failed_verdict_line_is_unknown(self):
        """The driver prints ``FAILED ✗`` for unvalidated results too; the line
        alone is not a refutation."""
        status, _reason, credit = harness.classify_should_fail_result_with_credit(
            success=False,
            output="trust-wp: bad FAILED ✗ (counterexample found)",
            source="fn bad() {}",
        )
        assert (status, credit) == ("unknown", None)

    def test_generic_fail_without_disproof_evidence_is_unknown(self):
        """classify_failure's ``fail`` without a refutation line
        (no ``FAILED ✗`` verdict, no wire failed, no ghost validation error)
        is not a credited rejection."""
        status, reason, credit = harness.classify_should_fail_result_with_credit(
            success=False,
            output="FAILED: verification counterexample found",
            source="fn bad() {}",
        )
        assert (status, credit) == ("unknown", None), (status, reason, credit)

    def test_broad_compile_error_is_error_without_expected_evidence(self):
        """Broad compile diagnostics do not prove an expected should-fail rejection."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output="error[E0001]: something went wrong",
            source="fn bad() {}",
        )
        assert status == "error", (
            f"Broad compile error should classify as error, got {status!r}"
        )
        assert reason is None, (
            f"Broad compile error should not produce a skip reason, got {reason!r}"
        )

    def test_allowlisted_compile_rejection_evidence_is_pass(self, monkeypatch):
        """Named compile-only rejections must match stable expected evidence."""
        fail_module = importlib.import_module(
            "tests.creusot_compat.harness_classify_fail"
        )
        monkeypatch.setitem(
            fail_module._KNOWN_EXPECTED_COMPILE_REJECTION_EVIDENCE,
            "tests/should_fail/synthetic_compile_only.rs",
            ("error[E0001]: expected synthetic rejection",),
        )

        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "error[E0001]: expected synthetic rejection\n"
                "error: could not compile `creusot_test` (lib) due to 1 previous error\n"
            ),
            source="fn bad() {}",
            test_name="tests/should_fail/synthetic_compile_only.rs",
            exit_code=101,
        )
        assert status == "pass", (
            f"Allowlisted compile rejection should classify as pass, got {status!r}"
        )
        assert reason is None, (
            "Expected no skip reason for allowlisted compile rejection, "
            f"got {reason!r}"
        )

    def test_allowlisted_compile_rejection_requires_evidence(self, monkeypatch):
        """A listed test still fails closed when the diagnostic evidence is absent."""
        fail_module = importlib.import_module(
            "tests.creusot_compat.harness_classify_fail"
        )
        monkeypatch.setitem(
            fail_module._KNOWN_EXPECTED_COMPILE_REJECTION_EVIDENCE,
            "tests/should_fail/synthetic_compile_only.rs",
            ("error[E0001]: expected synthetic rejection",),
        )

        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "error[E9999]: unrelated compile failure\n"
                "error: could not compile `creusot_test` (lib) due to 1 previous error\n"
            ),
            source="fn bad() {}",
            test_name="tests/should_fail/synthetic_compile_only.rs",
            exit_code=101,
        )
        assert status == "error", (
            f"Mismatched allowlisted compile rejection should classify as error, got {status!r}"
        )
        assert reason is None, (
            "Mismatched allowlisted compile rejection should not produce a reason, "
            f"got {reason!r}"
        )

    def test_backend_superseded_compile_error_is_error(self):
        """Backend-superseded names do not hide broad compile failures."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "error[E0433]: failed to resolve: use of undeclared type `Missing`\n"
                "error: could not compile `creusot_test` (lib) due to 1 previous error\n"
            ),
            source="fn bad() {}",
            test_name="tests/should_fail/unsupported/char_pattern.rs",
            exit_code=101,
        )
        assert status == "error", (
            f"Backend-superseded compile error should classify as error, got {status!r}"
        )
        assert reason is None, (
            f"Backend compile error should not produce a reason, got {reason!r}"
        )

    def test_ignore_overflow_is_not_backend_superseded(self):
        """ignore_overflow must be credited by a real rejection, never allowlisted.

        `const { N + 1 }` overflows for N = u32::MAX; crediting it as
        "backend superseded" would hide a false accept.
        """
        assert harness._check_backend_superseded("tests/should_fail/ignore_overflow.rs") is None
        status, _reason = harness.classify_should_fail_result(
            success=True,
            output="trust-wp: 0 verified, 0 failed, 0 errors\n",
            source="pub fn f<const N: u32>() { const { N + 1 }; }",
            test_name="tests/should_fail/ignore_overflow.rs",
            exit_code=0,
        )
        assert status != "pass", (
            f"an accepted ignore_overflow run must not classify as pass, got {status!r}"
        )

    def test_cargo_lock_error_stays_error(self):
        """Infrastructure cargo-lock failures must not count as rejection pass."""
        output = (
            "[cargo-lock] Waiting for build lock on trust-wp "
            "(held by slot 0: trust-wp (WORKER) [build])...\n"
            "error: could not compile `creusot_test`\n"
        )
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=output,
            source="fn bad() {}",
        )
        assert status == "error"
        assert reason == "cargo-lock contention"

    def test_timeout_error_stays_error_even_for_logic_only_source(self):
        """Timeout infrastructure errors must not fall through to logic-only skip/pass."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output="Timeout after 60s",
            source="#[logic]\nfn bad() -> bool { true }",
        )
        assert status == "error"
        assert reason == "timeout"

    def test_network_download_error_stays_error(self):
        """Crates.io fetch failures are infrastructure errors, not should_fail passes."""
        output = (
            "error: failed to download from https://index.crates.io/config.json\n"
            "Caused by:\n"
            "  [28] Timeout was reached\n"
        )
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=output,
            source="fn bad() {}",
        )
        assert status == "error"
        assert reason == "network download failure"

    def test_unexpected_verify_is_fail(self):
        """When trust-wp verifies (success=True), should_fail -> fail."""
        status, reason = harness.classify_should_fail_result(
            success=True,
            output="verified \u2713",
            source="fn bad() {}",
        )
        assert status == "fail", f"Rc/Arc usage should classify from output, got {status!r}"
        assert reason is None, f"Rc/Arc usage should not produce a skip reason, got {reason!r}"

    def test_vacuous_should_fail_accept_is_error(self):
        """Should-fail contracts with no verification activity fail closed."""
        output = (
            "trust-wp: 0 verified, 0 failed, 0 errors\n"
            "trust-wp-wire verified=0 failed=0 errors=0 panics=0 "
            "proof_assert_failed=0 proof_assert_errors=0 parse_errors=0 "
            "termination_errors=0 logic_recursion_errors=0 erasure_errors=0 "
            "base_exit_code=0\n"
        )
        status, reason = harness.classify_should_fail_result(
            success=True,
            output=output,
            source="#[ensures(false)]\nfn bad() {}",
            test_name="tests/should_fail/unsupported/hash_map.rs",
            exit_code=0,
        )
        assert status == "error"
        assert reason == "vacuous accept: no verification activity"

    def test_should_fail_per_function_rejection_is_not_vacuous(self):
        """Per-function status lines prove the lane saw real verification work.

        Without a validated refutation record the failure is ``unknown`` —
        but never the vacuous-accept ``error``.
        """
        output = (
            "trust-wp: bad failed \u2717\n"
            "trust-wp: 0 verified, 1 failed, 0 errors\n"
        )
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=output,
            source="#[ensures(false)]\nfn bad() {}",
            test_name="tests/should_fail/synthetic_contract.rs",
            exit_code=1,
        )
        assert status == "unknown"
        assert reason is None

    def test_unsupported_source_is_error(self):
        """Unsupported should_fail sources fail closed instead of skipping."""
        # Use `#[open]` as the unsupported feature — prophetic is supported (#2683).
        status, reason = harness.classify_should_fail_result(
            success=False,
            output="some output",
            source='#[open]\nfn reflexive() {}',
        )
        assert status == "error", f"Expected open-function source to be an error, got {status!r}"
        assert reason is None, f"Expected no skip reason for unsupported open source, got {reason!r}"

    def test_law_source_should_fail_result_falls_through(self):
        """Law source should classify from the actual verification outcome."""
        status, reason = harness.classify_should_fail_result(
            success=True,
            output="verified ✓",
            source='#[law]\nfn reflexive() {}',
        )
        assert status == "fail", f"Expected verified should-fail law case to fail, got {status!r}"
        assert reason is None, f"Expected no skip reason for #[law] fallthrough, got {reason!r}"

    def test_logic_law_source_should_fail_result_falls_through(self):
        """#[logic(law)] is not intercepted as unsupported."""
        status, reason = harness.classify_should_fail_result(
            success=True,
            output="verified ✓",
            source='#[logic(law)]\nfn reflexive() {}',
        )
        assert status == "fail", (
            f"Expected verified should-fail #[logic(law)] case to fail, got {status!r}"
        )
        assert reason is None, (
            f"Expected no skip reason for #[logic(law)] fallthrough, got {reason!r}"
        )

    def test_ghost_type_escape_is_pass(self):
        """Ghost type escape error output is classified as pass (valid rejection, #2686)."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output="ghost type escape: function `bad` accepts Ghost/Snapshot parameter(s)",
            source="fn deref_wrap() {}\nfn bad(x: Ghost<i32>) {}",
            test_name="tests/should_fail/generic_deref_ghost.rs",
            exit_code=2,
        )
        assert status == "pass", (
            f"Ghost type escape should be classified as 'pass' (valid rejection), got {status!r}"
        )

    def test_snap_type_escape_is_pass(self):
        """Snapshot type escape error output is classified as pass (valid rejection, #2686)."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output="ghost type escape: function `bad` accepts Ghost/Snapshot parameter(s)",
            source="fn deref_wrap() {}\nfn bad(x: Snapshot<i32>) {}",
            test_name="tests/should_fail/generic_deref_snap.rs",
            exit_code=2,
        )
        assert status == "pass", (
            f"Snapshot type escape should be classified as 'pass' (valid rejection), got {status!r}"
        )

    def test_unknown_test_not_skipped(self):
        """A test not in the known-false-accept list is classified normally."""
        status, reason = harness.classify_should_fail_result(
            success=True,
            output="verified \u2713",
            source="fn bad() {}",
            test_name="tests/should_fail/some_other_test.rs",
        )
        assert status == "fail"
        assert reason is None, (
            f"Snapshot self-reference rejection should not report a residual reason, got {reason!r}"
        )

    def test_resolved_divergence_clean_accept_fails(self):
        """Resolved divergence tests fail if they are cleanly accepted."""
        status, reason = harness.classify_should_fail_result(
            success=True,
            output="verified \u2713",
            source="fn bad() {}",
            test_name="tests/should_fail/bug/1762.rs",
        )
        assert status == "fail", (
            f"Expected cleanly accepted bug/1762.rs to be 'fail', got {status!r}"
        )
        assert reason is None, (
            f"Expected no residual reason for clean accept, got {reason!r}"
        )

    def test_panic_exit_code_is_error(self):
        """Crash exit code must stay error in should_fail lane (not pass)."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output="trust-wp: 0 verified, 0 failed, 0 errors\n(exit status: 101)",
            source="fn bad() {}",
            exit_code=101,
        )
        assert status == "error"
        assert reason is None, (
            f"Clean false accept should not report a skip reason, got {reason!r}"
        )

    def test_multi_error_compile_rejection_is_pass(self):
        """Exit 101 with 'due to N previous errors' is compile rejection, not panic (#1473)."""
        output = (
            "error: trust-wp: logic recursion check failed: `test::f`: mutual recursion\n"
            "error: trust-wp: logic recursion check failed: `test::g`: mutual recursion\n"
            "error: could not compile `test` (lib) due to 2 previous errors\n"
        )
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=output,
            source="#[logic]\nfn f() { g(); }\n#[logic]\nfn g() { f(); }",
            exit_code=101,
        )
        assert status == "pass"
        assert reason is None, f"Expected no skip reason for open source strict error, got {reason!r}"

    def test_unconditional_self_recursion_rejection_is_pass(self):
        """Unconditional self-recursion errors are valid rejections (#2686)."""
        output = (
            "error: trust-wp: logic recursion check failed: `test::falso`: "
            "unconditional self-recursion without #[variant(...)]: "
            "function always calls itself with no decreasing argument\n"
            "error: could not compile `test` (lib) due to 1 previous error\n"
        )
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=output,
            source="#[logic]\n#[ensures(false)]\nfn falso() { falso() }",
            exit_code=101,
        )
        assert status == "pass", (
            f"Expected logic recursion error to be classified as pass, got {status!r}"
        )
        assert reason is None, (
            f"Expected no skip reason for recursion rejection, got {reason!r}"
        )

    def test_bug_1762_trusted_contract_validation_is_pass(self):
        """bug/1762: #[check(ghost)] fn in #[trusted] contract is rejected (#2686)."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "error: trust-wp: trusted contract validation: `f` requires clause "
                "calls #[check(ghost)] function `faux`\n"
                "error: could not compile `creusot_test` (lib) due to 1 previous error\n"
            ),
            source="#[check(ghost)]\npub fn faux() -> bool { false }\n#[trusted]\n#[requires(faux())]\npub fn f() {}",
            test_name="tests/should_fail/bug/1762.rs",
            exit_code=2,
        )
        assert status == "pass", (
            f"Expected pass for bug/1762 trusted-contract rejection, got {status!r}"
        )
        assert reason is None, (
            f"Expected no residual reason for trusted-contract rejection, got {reason!r}"
        )

    def test_duplicate_specs_correctly_rejected(self):
        """duplicate_specs: trust-wp detects duplicate extern_spec (#2686).

        duplicate_specs.rs is not in _KNOWN_EXPECTED_DIVERGENCE_TESTS because
        trust-wp detects duplicate/conflicting extern_spec declarations and
        rejects them with exit code 2.
        When the output contains 'duplicate/conflicting extern_spec',
        the classifier should return 'pass' (correctly rejected).
        """
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "error: duplicate/conflicting extern_spec for Vec::new\n"
                "trust-wp: 0 verified, 0 failed, 1 errors"
            ),
            source="extern_spec! { impl<T> Vec<T> { fn new() -> Vec<T>; } }",
            test_name="tests/should_fail/duplicate_specs.rs",
        )
        assert status == "pass", (
            f"Expected pass (correctly rejected) for duplicate_specs, got {status!r}"
        )

    def test_frontend_rejection_raw_pointer_is_pass(self):
        """Raw-pointer deref rejection is a valid should-fail result (#2686 follow-up)."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "error: Dereference of a raw pointer is forbidden in creusot\n"
                "error: could not compile `creusot_test` (lib) due to 1 previous error\n"
            ),
            source="#[logic]\nfn bad(p: *const i32) -> i32 { *p }",
            test_name="tests/should_fail/raw_ptr_deref.rs",
            exit_code=101,
        )
        assert status == "pass", (
            f"Raw-pointer deref rejection should classify as pass, got {status!r}"
        )
        assert reason is None, (
            f"Frontend rejection should not produce a skip reason, got {reason!r}"
        )

    def test_frontend_rejection_ghost_context_is_pass(self):
        """Ghost-context violation rejection is a valid should-fail result."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "error: cannot create a ghost variable in program context\n"
                "error: could not compile `creusot_test` (lib) due to 1 previous error\n"
            ),
            source="fn bad() { let g = ghost!(1); }",
            test_name="tests/should_fail/ghost_in_program.rs",
            exit_code=101,
        )
        assert status == "pass", (
            f"Ghost-context rejection should classify as pass, got {status!r}"
        )
        assert reason is None

    def test_frontend_rejection_ghost_run_time_body_is_pass(self):
        """generic_deref_ghost: the program-context refusal of a bound that runs
        a ghost's `Deref` is a valid should-fail result (D-193)."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "error: trust-wp: `<creusot_std::Ghost<i32> as Deref>` runs outside "
                "ghost!(...) and snapshot!(...), where its run-time body is not the "
                "logical operation the verifier reads; move it into ghost!(...), "
                "snapshot!(...) or a specification\n"
                "error: could not compile `creusot_test` (lib) due to 1 previous error\n"
            ),
            source=(
                "pub fn deref_wrap<T: Deref>(x: &T) -> &T::Target { &*x }\n"
                "pub fn bad(x: Ghost<i32>) -> i32 { *deref_wrap(&x) }"
            ),
            test_name="tests/should_fail/generic_deref_ghost.rs",
            exit_code=101,
        )
        assert status == "pass", (
            f"Ghost run-time body refusal should classify as pass, got {status!r}"
        )
        assert reason is None

    def test_frontend_rejection_marker_pair_is_pass(self):
        """Two-token rejection passes only when both fragments are present."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "error: called logic function `spec` in program context\n"
                "error: could not compile `creusot_test` (lib) due to 1 previous error\n"
            ),
            source="#[logic]\nfn spec() -> bool { true }\nfn bad() { spec(); }",
            test_name="tests/should_fail/logic_in_program.rs",
            exit_code=101,
        )
        assert status == "pass", (
            f"Complete marker pair should classify as pass, got {status!r}"
        )
        assert reason is None

    def test_frontend_rejection_partial_pair_is_not_credited(self):
        """A single fragment of a marker pair must not credit a rejection."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "note: called logic function during analysis\n"
                "error[E0599]: no method named `foo`\n"
                "error: could not compile `creusot_test` (lib) due to 1 previous error\n"
            ),
            source="fn bad() {}",
            test_name="tests/should_fail/unrelated_compile.rs",
            exit_code=101,
        )
        assert status == "error", (
            f"Partial marker pair must not be credited as a rejection, got {status!r}"
        )

    def test_frontend_rejection_does_not_override_false_accept(self):
        """Soundness: a clean verification outranks any frontend marker text."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "trust-wp: 1 verified, 0 failed, 0 errors\n"
                "note: Dereference of a raw pointer is forbidden in creusot\n"
            ),
            source="fn bad() {}",
            test_name="tests/should_fail/false_accept_with_marker.rs",
            exit_code=0,
        )
        assert status == "fail", (
            f"False-accept guard must win over frontend marker, got {status!r}"
        )

    def test_frontend_rejection_does_not_override_panic(self):
        """Soundness: an internal crash outranks any frontend marker text."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "thread 'rustc' panicked at compiler/foo.rs:1:1\n"
                "note: Dereference of a raw pointer is forbidden in creusot\n"
                "(exit status: 101)"
            ),
            source="fn bad() {}",
            test_name="tests/should_fail/panic_with_marker.rs",
            exit_code=101,
        )
        assert status == "error", (
            f"Panic guard must win over frontend marker, got {status!r}"
        )

    def test_frontend_rejection_erasure_check_is_pass(self):
        """A failed #[erasure] check is a genuine trust-wp rejection -> pass."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "error: failed #[erasure] check for bar2: target expression "
                "`baz<42>()` does not match erasure expression `baz<0>()`\n"
                "error: could not compile `creusot_test` (lib) due to 1 previous error\n"
            ),
            source="#[erasure(bar)]\nfn bar2() -> i32 { baz::<0>() }",
            test_name="tests/should_fail/bad_erasure.rs",
            exit_code=2,
        )
        assert status == "pass", (
            f"Failed erasure check should classify as pass, got {status!r}"
        )
        assert reason is None

    def test_real_allowlist_bad_borrow_is_pass(self):
        """A real allowlisted compile-rejection (E0499 borrow) classifies as pass."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "error[E0499]: cannot borrow `x` as mutable more than once at a time\n"
                "error: could not compile `creusot_test` (lib) due to 1 previous error\n"
            ),
            source="fn bad() {}",
            test_name="tests/should_fail/bad_borrow.rs",
            exit_code=101,
        )
        assert status == "pass", (
            f"Allowlisted E0499 borrow rejection should be pass, got {status!r}"
        )

    def test_real_allowlist_requires_specific_evidence(self):
        """An allowlisted test still fails closed for an unrelated compile error."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "error[E0277]: some unrelated trait bound is not satisfied\n"
                "error: could not compile `creusot_test` (lib) due to 1 previous error\n"
            ),
            source="fn bad() {}",
            test_name="tests/should_fail/bad_borrow.rs",
            exit_code=101,
        )
        assert status == "error", (
            f"Mismatched diagnostic for an allowlisted test must stay error, got {status!r}"
        )

    def test_empty_allowlist_evidence_does_not_vacuously_pass(self, monkeypatch):
        """An empty evidence tuple must never vacuously credit a compile error."""
        fail_module = importlib.import_module(
            "tests.creusot_compat.harness_classify_fail"
        )
        monkeypatch.setitem(
            fail_module._KNOWN_EXPECTED_COMPILE_REJECTION_EVIDENCE,
            "tests/should_fail/synthetic_empty_evidence.rs",
            (),
        )
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "error[E9999]: anything at all\n"
                "error: could not compile `creusot_test` (lib) due to 1 previous error\n"
            ),
            source="fn bad() {}",
            test_name="tests/should_fail/synthetic_empty_evidence.rs",
            exit_code=101,
        )
        assert status == "error", (
            f"Empty evidence tuple must not vacuously pass, got {status!r}"
        )


# ---------------------------------------------------------------------------
# verification success gating
# ---------------------------------------------------------------------------


class TestVerificationRunSucceeded:
    """Regression tests for mixed verified/failed outputs (#945)."""

    def test_mixed_verified_and_failed_is_not_success(self):
        output = """\
trust-wp: foo verified \u2713
trust-wp: bar FAILED \u2717
trust-wp: 3 verified, 5 failed, 3 errors, 2 skipped
"""
        assert harness._verification_run_succeeded(0, output) is False

    def test_clean_verified_summary_is_success(self):
        output = """\
trust-wp: foo verified \u2713
trust-wp: 1 verified, 0 failed, 0 errors
"""
        assert harness._verification_run_succeeded(0, output) is True

    def test_nonzero_exit_code_is_not_success(self):
        output = "trust-wp: foo verified \u2713\ntrust_wp: 1 verified, 0 failed, 0 errors\n"
        assert harness._verification_run_succeeded(1, output) is False


# ---------------------------------------------------------------------------
# find_creusot_tests with lane parameter
# ---------------------------------------------------------------------------


class TestFindCreusotTestsLane:
    """Tests for lane-aware test discovery."""

    def _seed_reference_workspace(self, tmp_path: Path) -> Path:
        workspace = tmp_path / "workspace"
        creusot = workspace / "reference" / "creusot"

        should_succeed = creusot / "tests" / "should_succeed"
        should_fail = creusot / "tests" / "should_fail"
        examples = creusot / "examples"
        for directory in (should_succeed, should_fail, examples / "iterators"):
            directory.mkdir(parents=True)

        (should_succeed / "basic.rs").write_text("fn succeeds() {}\n")
        (should_succeed / "mod.rs").write_text("mod helper;\n")
        (should_fail / "reject.rs").write_text("fn rejects() {}\n")
        (should_fail / "lib.rs").write_text("pub mod helper;\n")
        (examples / "all_zero.rs").write_text("fn example() {}\n")
        (examples / "iterators" / "02_iter_mut.rs").write_text("fn example() {}\n")
        (examples / "iterators" / "common.rs").write_text("fn helper() {}\n")
        return workspace

    def test_should_succeed_lane(self, tmp_path):
        workspace = self._seed_reference_workspace(tmp_path)
        tests = harness.find_creusot_tests(workspace, lane="should_succeed")
        assert len(tests) > 0
        for t in tests:
            assert "should_succeed" in str(t)
            assert "should_fail" not in str(t)
            assert t.name != "mod.rs", f"mod.rs helper should be excluded: {t}"

    def test_should_fail_lane(self, tmp_path):
        workspace = self._seed_reference_workspace(tmp_path)
        tests = harness.find_creusot_tests(workspace, lane="should_fail")
        assert len(tests) > 0
        for t in tests:
            assert "should_fail" in str(t)
            assert "should_succeed" not in str(t)
            assert t.name != "lib.rs", f"lib.rs helper should be excluded: {t}"

    def test_examples_lane(self, tmp_path):
        workspace = self._seed_reference_workspace(tmp_path)
        tests = harness.find_creusot_tests(workspace, lane="examples")
        assert len(tests) > 0, "examples lane should discover at least one test"
        for t in tests:
            assert "examples" in str(t), f"examples lane test {t} should contain 'examples' in path"
            # common.rs is a helper module, not a standalone test
            assert t.name != "common.rs", f"common.rs helper should be excluded: {t}"

    def test_all_lane(self, tmp_path):
        workspace = self._seed_reference_workspace(tmp_path)
        succeed = harness.find_creusot_tests(workspace, lane="should_succeed")
        fail = harness.find_creusot_tests(workspace, lane="should_fail")
        examples = harness.find_creusot_tests(workspace, lane="examples")
        all_tests = harness.find_creusot_tests(workspace, lane="all")
        assert len(all_tests) == len(succeed) + len(fail) + len(examples), (
            f"all lane ({len(all_tests)}) should equal "
            f"succeed ({len(succeed)}) + fail ({len(fail)}) + examples ({len(examples)})"
        )

    def test_invalid_lane_raises(self):
        with pytest.raises(ValueError, match="Invalid lane"):
            harness.find_creusot_tests(WORKSPACE_ROOT, lane="invalid")


# ---------------------------------------------------------------------------
# --lane exit code protection
# ---------------------------------------------------------------------------


class TestLaneExitCodes:
    """Test that non-default lanes require --output."""

    HARNESS_PATH = str(HARNESS_DIR / "harness.py")

    def test_should_fail_lane_without_output_exits_3(self):
        """--lane should_fail without --output must exit 3."""
        result = subprocess.run(
            [sys.executable, self.HARNESS_PATH, "--lane", "should_fail"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 3
        assert "require an explicit --output" in result.stderr
        assert "tests/creusot_compat/results-should-fail.json" in result.stderr, (
            f"should_fail lane should suggest canonical output path, got: {result.stderr}"
        )

    def test_all_lane_without_output_exits_3(self):
        """--lane all without --output must exit 3."""
        result = subprocess.run(
            [sys.executable, self.HARNESS_PATH, "--lane", "all"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 3
        assert "require an explicit --output" in result.stderr

    def test_examples_lane_without_output_exits_3(self):
        """--lane examples without --output must exit 3."""
        result = subprocess.run(
            [sys.executable, self.HARNESS_PATH, "--lane", "examples"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 3, (
            f"examples lane without --output should exit 3, got {result.returncode}"
        )
        assert "require an explicit --output" in result.stderr, (
            f"expected explicit --output error, got: {result.stderr[:200]}"
        )
        assert "tests/creusot_compat/results-examples.json" in result.stderr, (
            f"examples lane should suggest canonical output path, got: {result.stderr}"
        )


# ---------------------------------------------------------------------------
# Metadata includes lane
# ---------------------------------------------------------------------------


class TestMetadataLane:
    """Tests that metadata includes the lane field."""

    def _make_args(self, **kwargs) -> argparse.Namespace:
        defaults = {
            "verbose": False,
            "filter": None,
            "limit": None,
            "output": None,
            "baseline": False,
            "lane": "should_succeed",
        }
        defaults.update(kwargs)
        return argparse.Namespace(**defaults)

    def test_default_lane_in_metadata(self):
        args = self._make_args()
        meta = harness.build_run_metadata(args, WORKSPACE_ROOT, 273, 273)
        assert meta["lane"] == "should_succeed"

    def test_should_fail_lane_in_metadata(self):
        args = self._make_args(lane="should_fail")
        meta = harness.build_run_metadata(args, WORKSPACE_ROOT, 97, 97)
        assert meta["lane"] == "should_fail"

    def test_all_lane_in_metadata(self):
        args = self._make_args(lane="all")
        meta = harness.build_run_metadata(args, WORKSPACE_ROOT, 370, 370)
        assert meta["lane"] == "all"


# ---------------------------------------------------------------------------
# summarize_results with mixed lanes
# ---------------------------------------------------------------------------


class TestSummarizeResultsLane:
    """Tests for per-lane breakdown in summary."""

    def test_mixed_lanes_produce_breakdown(self):
        results = [
            harness.TestResult(
                name="tests/should_succeed/foo.rs",
                status="pass",
                message="ok",
                duration_ms=100,
            ),
            harness.TestResult(
                name="tests/should_fail/bar.rs",
                status="pass",
                message="Correctly rejected",
                duration_ms=50,
            ),
        ]
        summary = harness.summarize_results(results)
        assert "should_succeed" in summary
        assert "should_fail" in summary
        assert summary["should_succeed"]["total"] == 1
        assert summary["should_fail"]["total"] == 1

    def test_single_lane_no_extra_breakdown(self):
        results = [
            harness.TestResult(
                name="tests/should_succeed/foo.rs",
                status="pass",
                message="ok",
                duration_ms=100,
            ),
        ]
        summary = harness.summarize_results(results)
        assert "should_succeed" in summary
        assert "should_fail" not in summary

    def test_all_lane_keeps_examples_separate_from_should_succeed(self):
        results = [
            harness.TestResult(
                name="tests/should_succeed/foo.rs",
                status="pass",
                message="ok",
                duration_ms=100,
            ),
            harness.TestResult(
                name="examples/all_zero.rs",
                status="unknown",
                message="incomplete",
                duration_ms=50,
            ),
            harness.TestResult(
                name="tests/should_fail/bar.rs",
                status="pass",
                message="Correctly rejected",
                duration_ms=25,
            ),
        ]

        summary = harness.summarize_results(results)

        assert summary["should_succeed"]["total"] == 1, (
            f"Expected should_succeed to exclude examples, got {summary!r}"
        )
        assert summary["examples"]["total"] == 1, (
            f"Expected examples lane summary, got {summary!r}"
        )
        assert summary["examples"]["unknown"] == 1, (
            f"Expected examples unknown count to stay separate, got {summary!r}"
        )
        assert summary["should_fail"]["total"] == 1, (
            f"Expected should_fail lane summary, got {summary!r}"
        )


# ---------------------------------------------------------------------------
# compute_lane_pair_freshness
# ---------------------------------------------------------------------------


class TestComputeLanePairFreshness:
    def test_noncanonical_or_partial_run_returns_none(self):
        workspace = WORKSPACE_ROOT
        assert (
            harness.compute_lane_pair_freshness(
                workspace=workspace,
                lane="should_fail",
                output_rel="tests/creusot_compat/results-temp.json",
                is_partial=False,
                current_git_commit="abc12345",
            )
            is None
        )
        assert (
            harness.compute_lane_pair_freshness(
                workspace=workspace,
                lane="should_succeed",
                output_rel=harness.CANONICAL_OUTPUT,
                is_partial=True,
                current_git_commit="abc12345",
            )
            is None
        )

    def test_stale_when_age_gap_exceeds_threshold(self, monkeypatch):
        def fake_load_commit(_path):
            return "old00000-dirty"

        def fake_distance(_workspace, commit):
            if commit == "new11111-dirty":
                return 3
            if commit == "old00000-dirty":
                return 43
            return None

        monkeypatch.setattr(harness, "_load_results_git_commit", fake_load_commit)
        monkeypatch.setattr(harness, "_commit_distance_to_head", fake_distance)

        freshness = harness.compute_lane_pair_freshness(
            workspace=WORKSPACE_ROOT,
            lane="should_succeed",
            output_rel=harness.CANONICAL_OUTPUT,
            is_partial=False,
            current_git_commit="new11111-dirty",
        )

        assert freshness is not None
        assert freshness["status"] == "stale"
        assert freshness["age_gap_commits"] == 40
        assert freshness["current_lane"] == "should_succeed"
        assert freshness["paired_lane"] == "should_fail"

    def test_ok_when_age_gap_within_threshold(self, monkeypatch):
        def fake_load_commit(_path):
            return "old00000"

        def fake_distance(_workspace, commit):
            if commit == "cur00000":
                return 15
            if commit == "old00000":
                return 10
            return None

        monkeypatch.setattr(harness, "_load_results_git_commit", fake_load_commit)
        monkeypatch.setattr(harness, "_commit_distance_to_head", fake_distance)

        freshness = harness.compute_lane_pair_freshness(
            workspace=WORKSPACE_ROOT,
            lane="should_fail",
            output_rel=harness.CANONICAL_SHOULD_FAIL_OUTPUT,
            is_partial=False,
            current_git_commit="cur00000",
        )

        assert freshness is not None
        assert freshness["status"] == "ok"
        assert freshness["age_gap_commits"] == 5
        assert freshness["paired_lane"] == "should_succeed"

    def test_unknown_when_paired_metadata_missing(self, monkeypatch):
        monkeypatch.setattr(harness, "_load_results_git_commit", lambda _path: None)
        monkeypatch.setattr(
            harness,
            "_commit_distance_to_head",
            lambda _workspace, commit: 7 if commit == "cur00000" else None,
        )

        freshness = harness.compute_lane_pair_freshness(
            workspace=WORKSPACE_ROOT,
            lane="should_fail",
            output_rel=harness.CANONICAL_SHOULD_FAIL_OUTPUT,
            is_partial=False,
            current_git_commit="cur00000",
        )

        assert freshness is not None
        assert freshness["status"] == "unknown"
        assert freshness["age_gap_commits"] is None
        assert "paired lane metadata missing" in freshness["reason"]


# ---------------------------------------------------------------------------
# check_baseline_freshness / canonical write integration
# ---------------------------------------------------------------------------


class TestBaselineFreshness:
    @pytest.fixture(autouse=True)
    def _mock_commit_relation_for_metadata_tests(self, monkeypatch):
        from tests.creusot_compat import harness_provenance

        def relation(workspace, commit):
            age = harness._commit_distance_to_head(workspace, commit)
            return {
                "is_ancestor": age is not None,
                "age_commits": age,
                "source_equivalent_to_head": False,
            }

        monkeypatch.setattr(harness_provenance, "_baseline_commit_relation", relation)

    def test_commit_override_replaces_lane_metadata(self, monkeypatch, tmp_path):
        canonical_output = tmp_path / "results.json"
        canonical_should_fail_output = tmp_path / "results-should-fail.json"
        canonical_output.write_text(json.dumps({"metadata": {"git_commit": "old00000"}}))
        canonical_should_fail_output.write_text(
            json.dumps({"metadata": {"git_commit": "pair0000"}})
        )

        monkeypatch.setattr(harness, "CANONICAL_OUTPUT", str(canonical_output))
        monkeypatch.setattr(
            harness, "CANONICAL_SHOULD_FAIL_OUTPUT", str(canonical_should_fail_output)
        )
        ages = {"old00000": 120, "pair0000": 80, "new11111": 0}
        monkeypatch.setattr(
            harness, "_commit_distance_to_head", lambda _workspace, commit: ages.get(commit)
        )

        freshness = harness.check_baseline_freshness(
            WORKSPACE_ROOT,
            max_age_commits=50,
            commit_overrides={"should_succeed": "new11111"},
        )

        lane = freshness["lanes"]["should_succeed"]
        assert lane["git_commit"] == "new11111"
        assert lane["age_commits"] == 0
        assert lane["status"] == "fresh"

    def test_check_baseline_freshness_fails_when_examples_baseline_missing(
        self, monkeypatch, tmp_path, capsys
    ):
        canonical_output = tmp_path / "results.json"
        canonical_should_fail_output = tmp_path / "results-should-fail.json"
        canonical_examples_output = tmp_path / "results-examples.json"
        canonical_output.write_text(json.dumps({"metadata": {"git_commit": "cur00000"}}))
        canonical_should_fail_output.write_text(
            json.dumps({"metadata": {"git_commit": "fail0000"}})
        )

        monkeypatch.setattr(harness, "CANONICAL_OUTPUT", str(canonical_output))
        monkeypatch.setattr(
            harness, "CANONICAL_SHOULD_FAIL_OUTPUT", str(canonical_should_fail_output)
        )
        monkeypatch.setattr(
            harness, "CANONICAL_EXAMPLES_OUTPUT", str(canonical_examples_output)
        )
        monkeypatch.setattr(sys, "argv", ["harness.py", "--check-baseline-freshness"])
        monkeypatch.setattr(harness, "find_workspace_root", lambda: WORKSPACE_ROOT)
        monkeypatch.setattr(
            harness,
            "_commit_distance_to_head",
            lambda _workspace, commit: {"cur00000": 0, "fail0000": 0}.get(commit),
        )
        monkeypatch.setattr(
            harness,
            "find_creusot_tests",
            lambda *_args, **_kwargs: pytest.fail(
                "--check-baseline-freshness should not discover tests"
            ),
        )
        monkeypatch.setattr(
            harness,
            "run_harness",
            lambda **_kwargs: pytest.fail(
                "--check-baseline-freshness should not run verification"
            ),
        )

        exit_code = harness.main()
        captured = capsys.readouterr()

        assert exit_code == harness.BASELINE_FRESHNESS_EXIT_CODE, (
            f"Expected missing examples baseline to exit "
            f"{harness.BASELINE_FRESHNESS_EXIT_CODE}, got {exit_code!r}"
        )
        assert "Baseline freshness: missing" in captured.out, (
            f"Expected missing freshness headline, got: {captured.out}"
        )
        assert "examples: missing" in captured.out, (
            f"Expected examples lane to be reported missing, got: {captured.out}"
        )
        assert str(canonical_examples_output) in captured.out, (
            f"Expected examples canonical path in report, got: {captured.out}"
        )
        assert "./scripts/refresh-baselines.sh" in captured.out, (
            f"Expected single full-refresh command in report, got: {captured.out}"
        )
        assert "./scripts/refresh-baselines.sh --help" in captured.out, (
            f"Expected help command in report, got: {captured.out}"
        )
        assert "python3 tests/creusot_compat/harness.py --baseline" not in captured.out, (
            "Freshness remediation should point at the full refresh script, got: "
            f"{captured.out}"
        )

    def test_main_uses_current_canonical_commit_for_baseline_freshness(
        self, monkeypatch, tmp_path
    ):
        canonical_output = tmp_path / "results.json"
        canonical_should_fail_output = tmp_path / "results-should-fail.json"
        canonical_output.write_text(json.dumps({"metadata": {"git_commit": "old00000"}}))
        canonical_should_fail_output.write_text(
            json.dumps({"metadata": {"git_commit": "pair0000"}})
        )

        monkeypatch.setattr(harness, "CANONICAL_OUTPUT", str(canonical_output))
        monkeypatch.setattr(
            harness, "CANONICAL_SHOULD_FAIL_OUTPUT", str(canonical_should_fail_output)
        )
        monkeypatch.setattr(sys, "argv", ["harness.py", "--output", str(canonical_output)])
        monkeypatch.setattr(harness, "find_workspace_root", lambda: WORKSPACE_ROOT)
        monkeypatch.setattr(harness, "_get_dirty_files", lambda _workspace: [])
        monkeypatch.setattr(
            harness, "find_creusot_tests", lambda _workspace, lane="should_succeed": []
        )
        monkeypatch.setattr(harness, "run_harness", lambda **_kwargs: [])
        monkeypatch.setattr(
            harness, "_get_git_commit", lambda _workspace, dirty_files=None: "new11111"
        )
        ages = {"old00000": 120, "pair0000": 80, "new11111": 0}
        monkeypatch.setattr(
            harness, "_commit_distance_to_head", lambda _workspace, commit: ages.get(commit)
        )
        monkeypatch.setattr(harness, "compute_lane_pair_freshness", lambda **_kwargs: None)

        exit_code = harness.main()

        assert exit_code == 0
        payload = json.loads(canonical_output.read_text())
        assert payload["metadata"]["git_commit"] == "new11111"
        baseline_meta = payload["metadata"]["baseline_freshness"]
        lane = baseline_meta["lanes"]["should_succeed"]
        assert lane["git_commit"] == "new11111"
        assert lane["age_commits"] == 0
        assert baseline_meta["evaluated_against_head"] == "new11111"
        assert "status" not in baseline_meta
        assert "status" not in lane

    def test_main_uses_current_examples_commit_for_baseline_freshness(
        self, monkeypatch, tmp_path
    ):
        canonical_output = tmp_path / "results.json"
        canonical_should_fail_output = tmp_path / "results-should-fail.json"
        canonical_examples_output = tmp_path / "results-examples.json"
        canonical_output.write_text(json.dumps({"metadata": {"git_commit": "old00000"}}))
        canonical_should_fail_output.write_text(
            json.dumps({"metadata": {"git_commit": "pair0000"}})
        )
        canonical_examples_output.write_text(
            json.dumps({"metadata": {"git_commit": "olderex0"}})
        )

        monkeypatch.setattr(harness, "CANONICAL_OUTPUT", str(canonical_output))
        monkeypatch.setattr(
            harness, "CANONICAL_SHOULD_FAIL_OUTPUT", str(canonical_should_fail_output)
        )
        monkeypatch.setattr(
            harness, "CANONICAL_EXAMPLES_OUTPUT", str(canonical_examples_output)
        )
        monkeypatch.setattr(
            sys,
            "argv",
            [
                "harness.py",
                "--lane",
                "examples",
                "--output",
                str(canonical_examples_output),
            ],
        )
        monkeypatch.setattr(harness, "find_workspace_root", lambda: WORKSPACE_ROOT)
        monkeypatch.setattr(harness, "_get_dirty_files", lambda _workspace: [])
        monkeypatch.setattr(
            harness, "find_creusot_tests", lambda _workspace, lane="examples": []
        )
        monkeypatch.setattr(harness, "run_harness", lambda **_kwargs: [])
        monkeypatch.setattr(
            harness, "_get_git_commit", lambda _workspace, dirty_files=None: "new11111"
        )
        ages = {
            "old00000": 120,
            "pair0000": 80,
            "olderex0": 70,
            "new11111": 0,
        }
        monkeypatch.setattr(
            harness, "_commit_distance_to_head", lambda _workspace, commit: ages.get(commit)
        )

        exit_code = harness.main()

        assert exit_code == 0, (
            f"Expected examples canonical write to exit 0, got {exit_code!r}"
        )
        payload = json.loads(canonical_examples_output.read_text())
        assert payload["metadata"]["lane"] == "examples", (
            f"Expected examples lane metadata, got {payload['metadata']!r}"
        )
        assert payload["metadata"]["git_commit"] == "new11111", (
            f"Expected new examples commit anchor, got {payload['metadata']!r}"
        )
        baseline_meta = payload["metadata"]["baseline_freshness"]
        lane = baseline_meta["lanes"]["examples"]
        assert lane["git_commit"] == "new11111", (
            f"Expected examples freshness to use current commit, got {lane!r}"
        )
        assert lane["age_commits"] == 0, (
            f"Expected examples freshness age 0, got {lane!r}"
        )
        assert baseline_meta["evaluated_against_head"] == "new11111", (
            f"Expected freshness evaluation head to be current commit, got {baseline_meta!r}"
        )
        assert "status" not in baseline_meta, (
            f"Persisted freshness metadata should omit status words, got {baseline_meta!r}"
        )
        assert "status" not in lane, (
            f"Persisted examples freshness should omit status words, got {lane!r}"
        )
    def test_baseline_age_warning_points_to_full_refresh_script(
        self, monkeypatch, tmp_path, capsys
    ):
        canonical_output = tmp_path / "results.json"
        canonical_should_fail_output = tmp_path / "results-should-fail.json"
        canonical_examples_output = tmp_path / "results-examples.json"
        canonical_output.write_text(json.dumps({"metadata": {"git_commit": "old00000"}}))
        canonical_should_fail_output.write_text(
            json.dumps({"metadata": {"git_commit": "fail0000"}})
        )

        monkeypatch.setattr(harness, "CANONICAL_OUTPUT", str(canonical_output))
        monkeypatch.setattr(
            harness, "CANONICAL_SHOULD_FAIL_OUTPUT", str(canonical_should_fail_output)
        )
        monkeypatch.setattr(
            harness, "CANONICAL_EXAMPLES_OUTPUT", str(canonical_examples_output)
        )
        monkeypatch.setattr(sys, "argv", ["harness.py", "--output", str(canonical_output)])
        monkeypatch.setattr(harness, "find_workspace_root", lambda: WORKSPACE_ROOT)
        monkeypatch.setattr(harness, "_get_dirty_files", lambda _workspace: [])
        monkeypatch.setattr(
            harness, "find_creusot_tests", lambda _workspace, lane="should_succeed": []
        )
        monkeypatch.setattr(harness, "run_harness", lambda **_kwargs: [])
        monkeypatch.setattr(
            harness, "_get_git_commit", lambda _workspace, dirty_files=None: "new11111"
        )
        ages = {"new11111": 0, "fail0000": 120}
        monkeypatch.setattr(
            harness, "_commit_distance_to_head", lambda _workspace, commit: ages.get(commit)
        )
        monkeypatch.setattr(harness, "compute_lane_pair_freshness", lambda **_kwargs: None)

        exit_code = harness.main()
        captured = capsys.readouterr()

        assert exit_code == 0, f"Expected run to succeed, got exit {exit_code!r}"
        assert "[BASELINE AGE WARNING]" in captured.out, (
            f"Expected baseline warning in output, got: {captured.out!r}"
        )
        assert "Refresh: ./scripts/refresh-baselines.sh" in captured.out, (
            f"Expected full refresh script recommendation, got: {captured.out!r}"
        )
        assert (
            "Refresh: python3 tests/creusot_compat/harness.py --baseline -v"
            not in captured.out
        ), (
            "Baseline warning should not recommend only the should_succeed "
            f"default command, got: {captured.out!r}"
        )

    def test_main_metadata_omits_stale_freshness_status_words(
        self, monkeypatch, tmp_path
    ):
        canonical_output = tmp_path / "results.json"
        canonical_should_fail_output = tmp_path / "results-should-fail.json"
        canonical_output.write_text(json.dumps({"metadata": {"git_commit": "old00000"}}))
        canonical_should_fail_output.write_text(
            json.dumps({"metadata": {"git_commit": "pair0000"}})
        )

        monkeypatch.setattr(harness, "CANONICAL_OUTPUT", str(canonical_output))
        monkeypatch.setattr(
            harness, "CANONICAL_SHOULD_FAIL_OUTPUT", str(canonical_should_fail_output)
        )
        monkeypatch.setattr(sys, "argv", ["harness.py", "--output", str(canonical_output)])
        monkeypatch.setattr(harness, "find_workspace_root", lambda: WORKSPACE_ROOT)
        monkeypatch.setattr(harness, "_get_dirty_files", lambda _workspace: [])
        monkeypatch.setattr(
            harness, "find_creusot_tests", lambda _workspace, lane="should_succeed": []
        )
        monkeypatch.setattr(harness, "run_harness", lambda **_kwargs: [])
        monkeypatch.setattr(
            harness, "_get_git_commit", lambda _workspace, dirty_files=None: "new11111"
        )
        ages = {"old00000": 120, "pair0000": 80, "new11111": 0}
        monkeypatch.setattr(
            harness, "_commit_distance_to_head", lambda _workspace, commit: ages.get(commit)
        )
        monkeypatch.setattr(
            harness,
            "compute_lane_pair_freshness",
            lambda **_kwargs: {
                "status": "ok",
                "current_lane": "should_succeed",
                "current_age_commits": 0,
                "paired_lane": "should_fail",
                "paired_age_commits": 80,
                "max_age_gap_commits": 20,
                "age_gap_commits": 80,
            },
        )

        exit_code = harness.main()

        assert exit_code == 0
        payload = json.loads(canonical_output.read_text())
        baseline_meta = payload["metadata"]["baseline_freshness"]
        lane_pair_meta = payload["metadata"]["lane_pair_freshness"]
        assert baseline_meta["lanes"]["should_fail"]["age_commits"] == 80
        assert baseline_meta["evaluated_against_head"] == "new11111"
        assert lane_pair_meta["paired_age_commits"] == 80
        assert lane_pair_meta["evaluated_against_head"] == "new11111"
        assert "status" not in baseline_meta
        assert "status" not in baseline_meta["lanes"]["should_succeed"]
        assert "status" not in baseline_meta["lanes"]["should_fail"]
        assert "status" not in lane_pair_meta


# ---------------------------------------------------------------------------
# classify_failure: Rc/Arc source is not auto-skipped (#634)
# ---------------------------------------------------------------------------


class TestClassifyFailureRcArc:
    """Rc/Arc source patterns must NOT trigger auto-skip: trust-wp-std has
    Rc/Arc specs wired in std_specs.rs."""

    def test_rc_source_not_skipped(self):
        """Source with Rc:: should fall through to output-based classification."""
        status, reason = harness.classify_failure(
            output="FAILED: verification counterexample found",
            source="use std::rc::Rc;\nfn foo(r: Rc<i32>) {}",
        )
        assert status == "fail", f"Rc source should classify from output, got {status}"
        assert reason is None, f"Expected no skip reason for open source exit 101 error, got {reason!r}"

    def test_arc_source_not_skipped(self):
        """Source with Arc:: should fall through to output-based classification."""
        status, reason = harness.classify_failure(
            output="error[E0001]: something broke",
            source="use std::sync::Arc;\nfn foo(a: Arc<i32>) {}",
        )
        assert status == "error", f"Arc source should classify from output, got {status}"
        assert reason is None, f"Expected no skip reason for Arc source, got {reason!r}"

    def test_rc_arc_usage_not_skipped(self):
        """Bare Rc::/Arc:: usage patterns should not trigger skip."""
        status, reason = harness.classify_failure(
            output="FAILED: counterexample",
            source="let x = Rc::new(42);\nlet y = Arc::clone(&z);",
        )
        assert status == "fail"
        assert reason is None

    def test_other_unsupported_is_error(self):
        """Other source-level unsupported features fail closed."""
        # Use `#[open]` as the unsupported feature — prophetic is supported (#2683).
        status, reason = harness.classify_failure(
            output="FAILED: something",
            source="#[open]\nfn reflexive() {}",
        )
        assert status == "error", f"Expected open-function source to be an error, got {status!r}"
        assert reason is None, f"Expected no skip reason for open source strict error, got {reason!r}"

    def test_law_source_falls_through_to_output_classification(self):
        """Law annotations classify from the output text."""
        status, reason = harness.classify_failure(
            output="FAILED: counterexample",
            source="#[law]\nfn reflexive() {}",
        )
        assert status == "fail", (
            f"Expected law source to follow output failure markers, got {status!r}"
        )
        assert reason is None, f"Expected no skip reason for #[law] output fallthrough, got {reason!r}"

    def test_prophetic_source_falls_through_to_output_classification(self):
        """Prophetic logic is supported — classify from output, not skip (#2683)."""
        status, reason = harness.classify_failure(
            output="FAILED: counterexample",
            source="#[logic(prophetic)]\nfn reflexive() {}",
        )
        assert status == "fail", (
            f"Expected prophetic source to follow output failure markers, got {status!r}"
        )
        assert reason is None, f"Expected no skip reason for prophetic fallthrough, got {reason!r}"

    def test_unsupported_source_exit_101_is_error(self):
        """Unsupported sources fail closed even with panic-like exit text."""
        # Use `#[open]` as the unsupported feature — prophetic is supported (#2683).
        status, reason = harness.classify_failure(
            output="trust-wp: 0 verified, 0 failed, 0 errors\n(exit status: 101)",
            source="#[open]\nfn p() {}",
            exit_code=101,
        )
        assert status == "error", f"Expected open-function source to be an error, got {status!r}"
        assert reason is None, f"Expected no skip reason for open source exit 101 error, got {reason!r}"

    def test_exit_status_101_without_panic_string_is_error(self):
        """Suppressed panic hook still emits exit status 101; classify as error."""
        status, reason = harness.classify_failure(
            output="trust-wp: 0 verified, 0 failed, 0 errors\n(exit status: 101)",
            source="fn fib() -> i32 { 1 }",
        )
        assert status == "error"
        assert reason is None

    def test_exit_code_101_param_without_text_is_error(self):
        """Exit code 101 via exit_code param (no textual hint) is also error (#1032)."""
        status, reason = harness.classify_failure(
            output="trust-wp: 0 verified, 0 failed, 0 errors",
            source="fn fib() -> i32 { 1 }",
            exit_code=101,
        )
        assert status == "error"
        assert reason is None

    def test_cell_02_fib_scenario_suppressed_panic_with_contracts(self):
        """cell/02_fib.rs: contracts found, exit code 101, no panic string (#1032).

        Without the _has_panic_exit_status guard the classifier falls through
        to the contract-count check and misclassifies this as 'skip' with
        'no contracts verified'.
        """
        # Simulates the cell/02_fib output: trust-wp finds contracts but panics
        # during encoding (fmap_lookup). The panic hook is suppressed so the
        # output has no "panicked" text, only the cargo wrapper's exit status.
        output = (
            "trust-wp: Found 4 functions with contracts:\n"
            "  fib\n"
            "  lemma_fib_bound\n"
            "  fib_memo\n"
            "trust-wp: verifying fib_memo\n"
            "error: could not compile `creusot_test`\n"
            "\n"
            "Caused by:\n"
            "  process didn't exit successfully: "
            "`trust-wp-rustc rustc ...` (exit status: 101)\n"
        )
        status, reason = harness.classify_failure(
            output=output,
            source="fn fib() -> i32 { 1 }",
            exit_code=101,
        )
        assert status == "error", f"expected 'error', got '{status}' (reason={reason})"
        assert reason is None


# ---------------------------------------------------------------------------
# classify_failure: caught ay sort panics (#885)
# ---------------------------------------------------------------------------


class TestClassifyCaughtAYPanic:
    """Tests for caught ay sort panics not being classified as errors (#885)."""

    def test_caught_ay_panic_not_classified_as_rustc_crash(self):
        """Caught ay sort panic with 'ay solver panic during verification' marker
        should NOT be classified as error via _has_rustc_panic. (#885)"""
        output = (
            "thread 'rustc' (12345) panicked at ay-dpll/src/api/terms.rs:407\n"
            "sort mismatch in datatype_selector: expected expr sort\n"
            "error: the compiler unexpectedly panicked. this is a bug.\n"
            "trust-wp: ay solver panic during verification: sort mismatch in "
            "datatype_selector: expected expr sort\n"
            "trust-wp: proof_assert in fib_memo unknown (ay solver panic: sort "
            "mismatch in datatype_selector)\n"
            "trust-wp: proof_assert: 0 verified, 0 failed, 1 errors\n"
            "trust-wp: Found 4 functions with contracts:\n"
            "trust-wp: 8 verified, 0 failed, 0 errors\n"
        )
        status, reason = harness.classify_failure(
            output=output,
            source="#[requires(true)]\nfn fib() -> i32 { 1 }",
        )
        # Should be classified as 'unknown' (caught panic), not 'error' (crash)
        assert status != "error", (
            f"caught ay panic should not be 'error', got status={status}"
        )

    def test_genuine_rustc_panic_without_ay_marker_still_error(self):
        """Genuine rustc panic without ay marker is still classified as error."""
        output = (
            "thread 'rustc' panicked at 'index out of bounds'\n"
            "error: the compiler unexpectedly panicked. this is a bug.\n"
        )
        status, reason = harness.classify_failure(
            output=output,
            source="fn foo() {}",
        )
        assert status == "error"

    def test_has_rustc_panic_false_when_ay_marker_present(self):
        """_has_rustc_panic returns False when ay catch marker is in output."""
        output = (
            "thread 'rustc' panicked at ay-dpll\n"
            "trust-wp: ay solver panic during verification: BUG: mk_eq\n"
        )
        assert harness._has_rustc_panic(output) is False

    def test_has_rustc_panic_true_without_ay_marker(self):
        """_has_rustc_panic returns True for genuine panic without ay marker."""
        output = "thread 'rustc' panicked at 'assertion failed'\n"
        assert harness._has_rustc_panic(output) is True


# ---------------------------------------------------------------------------
# classify_failure: unknown vs fail separation (#1163)
# ---------------------------------------------------------------------------


class TestClassifyFailureUnknown:
    """Tests for separating solver-unknown from genuine fail (#1163)."""

    def test_pure_unknown_per_function_marker(self):
        """Output with only 'unknown (' markers (no FAILED ✗) → 'unknown'."""
        output = (
            "trust-wp: Found 1 functions with contracts:\n"
            "  foo\n"
            "trust-wp: verifying foo\n"
            "trust-wp: foo unknown (quantifiers)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        status, reason = harness.classify_failure(output=output, source="fn foo() {}")
        assert status == "unknown", f"expected 'unknown', got '{status}'"
        assert reason is None

    def test_failed_marker_is_fail(self):
        """Output with 'FAILED ✗' per-function marker → 'fail'."""
        output = (
            "trust-wp: Found 1 functions with contracts:\n"
            "  bar\n"
            "trust-wp: verifying bar\n"
            "trust-wp: bar FAILED \u2717\n"
            "trust-wp: 0 verified, 1 failed, 0 errors\n"
        )
        status, reason = harness.classify_failure(output=output, source="fn bar() {}")
        assert status == "fail"
        assert reason is None

    def test_lra_unsupported_failed_marker_is_unknown(self):
        """Spurious LRA-unsupported failures are solver unknowns, not compile errors."""
        output = (
            "trust-wp: Found 1 functions with contracts:\n"
            "  len\n"
            "LRA check_impl simplex=Sat but unsupported, returning Unknown "
            "unsupported_count=2 asserted_unsupported=2\n"
            "trust-wp: List::<T>::len FAILED \u2717 (loop invariant)\n"
            "error: could not compile `creusot_test` (lib); 1 warning emitted\n"
            + _wire_line(base_exit_code=1, failed=1, errors=2, warnings=1)
        )
        status, reason = harness.classify_failure(output=output, source="fn len() {}")
        assert status == "unknown", f"expected 'unknown', got {status!r}"
        assert reason is None, f"expected no skip/error reason, got {reason!r}"

    def test_mixed_failed_and_unknown_is_fail(self):
        """Output with both FAILED ✗ and unknown → 'fail' (has genuine failure)."""
        output = (
            "trust-wp: Found 2 functions with contracts:\n"
            "  foo\n"
            "  bar\n"
            "trust-wp: verifying foo\n"
            "trust-wp: foo FAILED \u2717\n"
            "trust-wp: verifying bar\n"
            "trust-wp: bar unknown (quantifiers)\n"
            "trust-wp: 0 verified, 1 failed, 1 errors\n"
        )
        status, reason = harness.classify_failure(output=output, source="fn foo() {}\nfn bar() {}")
        assert status == "fail"
        assert reason is None

    def test_counterexample_keyword_is_fail(self):
        """Output with 'counterexample' keyword → 'fail' even without ✗ marker."""
        output = "FAILED: verification counterexample found"
        status, reason = harness.classify_failure(output=output, source="fn f() {}")
        assert status == "fail"
        assert reason is None

    def test_unknown_via_summary_only(self):
        """When no per-function markers but summary has errors only → 'unknown'."""
        output = (
            "trust-wp: Found 1 functions with contracts:\n"
            "  baz\n"
            "trust-wp: 0 verified, 0 failed, 2 errors\n"
        )
        status, reason = harness.classify_failure(output=output, source="fn baz() {}")
        assert status == "unknown", f"expected 'unknown', got '{status}'"
        assert reason is None

    def test_unknown_in_summary_in_new_status(self):
        """Summary dict should include 'unknown' key."""
        results = [
            harness.TestResult(
                name="tests/should_succeed/foo.rs",
                status="unknown",
                message="solver incomplete",
                duration_ms=100,
            ),
            harness.TestResult(
                name="tests/should_succeed/bar.rs",
                status="fail",
                message="counterexample found",
                duration_ms=200,
            ),
        ]
        summary = harness.summarize_results(results)
        assert summary["unknown"] == 1
        assert summary["fail"] == 1

    def test_should_fail_unknown_is_unknown(self):
        """In should_fail lane, solver-unknown remains visible as unknown."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "trust-wp: Found 1 functions with contracts:\n"
                "  bad\n"
                "trust-wp: verifying bad\n"
                "trust-wp: bad unknown (quantifiers)\n"
                "trust-wp: 0 verified, 0 failed, 1 errors\n"
            ),
            source="fn bad() {}",
        )
        assert status == "unknown", f"Expected solver unknown to remain unknown, got {status!r}"
        assert reason is None, f"Expected no skip reason for no-contract error, got {reason!r}"

    def test_should_fail_parse_error_rejection_is_pass(self):
        """Frontend parse diagnostics are valid rejections in should_fail."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=(
                "trust-wp: frontend diagnostic: failed to parse requires '[0; 4] == x': "
                "parse error at position 0: expected expression\n"
                "trust-wp: 0 verified, 0 failed, 1 errors\n"
                + _wire_line(base_exit_code=2, errors=1, parse_errors=1)
            ),
            source="#[requires([0; 4] == x)] fn f(x: [u32; 4]) {}",
            test_name="tests/should_fail/array.rs",
            exit_code=2,
        )
        assert status == "pass", (
            f"Expected frontend parse rejection to be 'pass', got {status!r}"
        )
        assert reason is None, f"Expected no skip reason for parse rejection, got {reason!r}"

    def test_proof_assert_only_unknown_not_function_unknown(self):
        """proof_assert unknown should NOT trigger function-level unknown (#1315).

        When all user functions verify but proof_assert is unknown, the test
        should NOT be classified as 'unknown'.
        """
        output = (
            "trust-wp: Found 1 functions with contracts:\n"
            "  foo\n"
            "trust-wp: verifying foo\n"
            "trust-wp: foo verified\n"
            "trust-wp: proof_assert in foo unknown (incomplete)\n"
            "trust-wp: 1 verified, 0 failed, 0 errors\n"
        )
        status, reason = harness.classify_failure(output=output, source="fn foo() {}")
        assert status != "unknown", (
            f"proof_assert-only unknown should not cause function-level unknown, got '{status}'"
        )

    def test_function_unknown_still_detected(self):
        """Function-level unknown markers still correctly detected (#1315)."""
        output = (
            "trust-wp: Found 1 functions with contracts:\n"
            "  foo\n"
            "trust-wp: verifying foo\n"
            "trust-wp: foo unknown (quantifiers)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        status, reason = harness.classify_failure(output=output, source="fn foo() {}")
        assert status == "unknown"
        assert reason is None

    def test_mixed_function_and_proof_assert_unknown_is_unknown(self):
        """When both function-level AND proof_assert are unknown → 'unknown' (#1315)."""
        output = (
            "trust-wp: Found 1 functions with contracts:\n"
            "  foo\n"
            "trust-wp: verifying foo\n"
            "trust-wp: foo unknown (quantifiers)\n"
            "trust-wp: proof_assert in foo unknown (incomplete)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        status, reason = harness.classify_failure(output=output, source="fn foo() {}")
        assert status == "unknown"
        assert reason is None


# ---------------------------------------------------------------------------
# proof_assert exclusion from summary counts and failure detection (#1315)
# ---------------------------------------------------------------------------


class TestProofAssertSummaryExclusion:
    """Verify proof_assert lines are excluded from function-level summaries (#1315)."""

    def test_summary_counts_exclude_proof_assert(self):
        """_last_verification_summary_counts skips proof_assert summary lines."""
        output = (
            "trust-wp: 1 verified, 0 failed, 0 errors, 1 skipped\n"
            "trust-wp: proof_assert: 0 verified, 0 failed, 1 errors\n"
        )
        counts = harness._last_verification_summary_counts(output)
        assert counts == (1, 0, 0), (
            f"should return function-level (1,0,0), not proof_assert (0,0,1); got {counts}"
        )

    def test_has_verification_failures_excludes_proof_assert_unknown(self):
        """_has_verification_failures ignores proof_assert-only unknown lines."""
        output = (
            "trust-wp: 1 verified, 0 failed, 0 errors\n"
            "trust-wp: proof_assert in foo unknown (incomplete)\n"
            "trust-wp: proof_assert: 0 verified, 0 failed, 1 errors\n"
        )
        assert not harness._has_verification_failures(output), (
            "proof_assert-only unknown should not count as function-level failure"
        )


# ---------------------------------------------------------------------------
# proof_assert-aware classification (#2255)
# ---------------------------------------------------------------------------


class TestProofAssertSummaryCounts:
    """Verify _last_proof_assert_summary_counts parses PA summary lines (#2255)."""

    def test_parses_pa_summary(self):
        output = (
            "trust-wp: 0 verified, 0 failed, 0 errors\n"
            "trust-wp: proof_assert: 6 verified, 1 failed, 0 errors\n"
        )
        counts = harness._last_proof_assert_summary_counts(output)
        assert counts == (6, 1, 0), f"expected (6,1,0), got {counts}"

    def test_returns_none_when_no_pa(self):
        output = "trust-wp: 1 verified, 0 failed, 0 errors\n"
        counts = harness._last_proof_assert_summary_counts(output)
        assert counts is None, f"expected None when no PA line, got {counts}"

    def test_parses_all_pass_pa(self):
        output = (
            "trust-wp: 0 verified, 0 failed, 0 errors\n"
            "trust-wp: proof_assert: 11 verified, 0 failed, 0 errors\n"
        )
        counts = harness._last_proof_assert_summary_counts(output)
        assert counts == (11, 0, 0), f"expected (11,0,0), got {counts}"


class TestProofAssertClassification:
    """PA-only tests should be classified based on PA results (#2255)."""

    def test_pa_all_pass_classifies_as_pass(self):
        """All proof_asserts verified, no function-level results → pass."""
        output = (
            "functions with contracts found count=2\n"
            "trust-wp: proof_assert in foo verified ✓\n"
            "trust-wp: proof_assert in bar verified ✓\n"
            "trust-wp: 0 verified, 0 failed, 0 errors\n"
            "trust-wp: proof_assert: 2 verified, 0 failed, 0 errors\n"
            "error: could not compile `creusot_test` (lib)\n"
        )
        source = "proof_assert!(x > 0);\n"
        status, reason = harness.classify_failure(output, source)
        assert status == "pass", (
            f"PA all-pass should classify as pass, got '{status}' (reason={reason})"
        )

    def test_pa_with_failures_classifies_as_fail(self):
        """Some proof_asserts failed → fail."""
        output = (
            "functions with contracts found count=1\n"
            "trust-wp: proof_assert in foo verified ✓\n"
            "trust-wp: proof_assert in foo FAILED ✗\n"
            "trust-wp: 0 verified, 0 failed, 0 errors\n"
            "trust-wp: proof_assert: 1 verified, 1 failed, 0 errors\n"
            "error: could not compile `creusot_test` (lib)\n"
        )
        source = "proof_assert!(x > 0);\n"
        status, reason = harness.classify_failure(output, source)
        assert status == "fail", (
            f"PA with failures should classify as fail, got '{status}'"
        )

    def test_pa_pass_with_panic_exit_defers(self):
        """PA all-pass output cannot mask a non-zero process result."""
        output = (
            "functions with contracts found count=1\n"
            "trust-wp: proof_assert in foo verified ✓\n"
            "trust-wp: 0 verified, 0 failed, 0 errors\n"
            "trust-wp: proof_assert: 1 verified, 0 failed, 0 errors\n"
            "error: could not compile `creusot_test` (lib)\n"
            "(exit status: 101)\n"
        )
        source = "proof_assert!(x > 0);\n"
        status, reason = harness.classify_failure(output, source, exit_code=101)
        assert status == "error", (
            f"PA all-pass with exit 101 should be error, got '{status}'"
        )

    def test_no_pa_no_fn_is_error(self):
        """No PA results and no function results fail closed."""
        output = (
            "functions with contracts found count=1\n"
            "trust-wp: 0 verified, 0 failed, 0 errors\n"
            "error: could not compile `creusot_test` (lib)\n"
        )
        source = "#[requires(x > 0)]\nfn foo(x: i32) {}\n"
        status, reason = harness.classify_failure(output, source)
        assert status == "error", f"No PA, no fn results should be error, got '{status}'"
        assert reason is None, f"Expected no skip reason for no PA/no fn error, got {reason!r}"


# ---------------------------------------------------------------------------
# classify_failure: proof_assert isolation from function-level results (#2700)
# ---------------------------------------------------------------------------


class TestProofAssertIsolation:
    """Function contracts verified + proof_assert fails → pass (#2700).

    When all function-level contracts verify successfully, proof_assert
    failures should not downgrade the compat classification to "fail".
    proof_assert failures reflect encoding gaps, not wrong behavior.
    """

    def test_function_pass_pa_fail_classifies_as_pass(self):
        """Function verified + proof_assert FAILED → still pass (#2700)."""
        output = (
            "functions with contracts found count=1\n"
            "trust-wp: my_fn verified \u2713\n"
            "trust-wp: proof_assert in my_fn FAILED \u2717\n"
            "trust-wp: 1 verified, 0 failed, 0 errors\n"
            "trust-wp: proof_assert: 0 verified, 1 failed, 0 errors\n"
            "error: could not compile `creusot_test` (lib)\n"
        )
        source = "#[requires(x > 0)]\n#[ensures(result > 0)]\nfn my_fn(x: i32) -> i32 { x }\nproof_assert!(x > 0);\n"
        status, reason = harness.classify_failure(output, source)
        assert status == "pass", (
            f"Function pass + PA fail should be pass (#2700), got '{status}' (reason={reason})"
        )

    def test_function_pass_pa_unknown_classifies_as_pass(self):
        """Function verified + proof_assert unknown → still pass (#2700)."""
        output = (
            "functions with contracts found count=1\n"
            "trust-wp: my_fn verified \u2713\n"
            "trust-wp: proof_assert in my_fn unknown (timeout)\n"
            "trust-wp: 1 verified, 0 failed, 0 errors\n"
            "trust-wp: proof_assert: 0 verified, 0 failed, 1 errors\n"
            "error: could not compile `creusot_test` (lib)\n"
        )
        source = "#[requires(x > 0)]\n#[ensures(result > 0)]\nfn my_fn(x: i32) -> i32 { x }\nproof_assert!(x > 0);\n"
        status, reason = harness.classify_failure(output, source)
        assert status == "pass", (
            f"Function pass + PA unknown should be pass (#2700), got '{status}' (reason={reason})"
        )

    def test_function_fail_pa_fail_still_classifies_as_fail(self):
        """Function FAILED + proof_assert FAILED → fail (function-level failure dominates)."""
        output = (
            "functions with contracts found count=1\n"
            "trust-wp: my_fn FAILED \u2717\n"
            "trust-wp: proof_assert in my_fn FAILED \u2717\n"
            "trust-wp: 1 verified, 1 failed, 0 errors\n"
            "trust-wp: proof_assert: 0 verified, 1 failed, 0 errors\n"
        )
        source = "#[requires(x > 0)]\nfn my_fn(x: i32) -> i32 { x }\nproof_assert!(x > 0);\n"
        status, reason = harness.classify_failure(output, source)
        assert status == "fail", (
            f"Function fail + PA fail should be fail, got '{status}'"
        )

    def test_multiple_functions_pass_pa_fail_classifies_as_pass(self):
        """Multiple functions verified + proof_assert failures → pass (#2700)."""
        output = (
            "functions with contracts found count=2\n"
            "trust-wp: fn_a verified \u2713\n"
            "trust-wp: fn_b verified \u2713\n"
            "trust-wp: proof_assert in fn_a FAILED \u2717\n"
            "trust-wp: proof_assert in fn_b FAILED \u2717\n"
            "trust-wp: 2 verified, 0 failed, 0 errors\n"
            "trust-wp: proof_assert: 0 verified, 2 failed, 0 errors\n"
            "error: could not compile `creusot_test` (lib)\n"
        )
        source = "#[requires(x > 0)]\nfn fn_a(x: i32) -> i32 { x }\n#[ensures(result > 0)]\nfn fn_b(x: i32) -> i32 { x }\nproof_assert!(x > 0);\n"
        status, reason = harness.classify_failure(output, source)
        assert status == "pass", (
            f"Multiple fn pass + PA fail should be pass (#2700), got '{status}' (reason={reason})"
        )


# ---------------------------------------------------------------------------
# Wire-line proof_assert isolation (#2700)
# ---------------------------------------------------------------------------


class TestWireLineProofAssertIsolation:
    """TRUST_WP_RESULT wire line-based PA hardening.

    When the aggregated wire telemetry shows function-level success
    (verified>0, failed=0, errors=0) with proof_assert-only failures,
    the compat classifier should not return a plain "pass".
    """

    def test_wire_line_pa_only_failure_detected(self):
        """_wire_line_shows_pa_only_failure returns True for PA-only wire line."""
        output = (
            "trust-wp: 6 verified, 0 failed, 0 errors\n"
            "trust-wp: proof_assert: 0 verified, 3 failed, 0 errors\n"
            + _wire_line(
                base_exit_code=1,
                verified=6,
                trusted=30,
                skipped=3,
                proof_assert_failed=3,
            )
        )
        assert harness._wire_line_shows_pa_only_failure(output), (
            "should detect PA-only failure in wire line with verified=6, pa_failed=3"
        )

    def test_wire_line_function_failure_not_detected(self):
        """_wire_line_shows_pa_only_failure returns False when failed>0."""
        output = (
            _wire_line(
                base_exit_code=1,
                verified=5,
                failed=1,
                trusted=30,
                skipped=3,
                proof_assert_failed=1,
            )
        )
        assert not harness._wire_line_shows_pa_only_failure(output), (
            "should not detect PA-only when function-level failed=1"
        )

    def test_wire_line_function_errors_not_detected(self):
        """_wire_line_shows_pa_only_failure returns False when errors>0."""
        output = (
            _wire_line(
                base_exit_code=1,
                verified=21,
                errors=6,
                warnings=1,
                trusted=30,
                skipped=3,
                proof_assert_failed=1,
            )
        )
        assert not harness._wire_line_shows_pa_only_failure(output), (
            "should not detect PA-only when function-level errors=6"
        )

    def test_wire_line_no_verified_not_detected(self):
        """_wire_line_shows_pa_only_failure returns False when verified=0."""
        output = (
            _wire_line(base_exit_code=1, proof_assert_failed=2)
        )
        assert not harness._wire_line_shows_pa_only_failure(output), (
            "should not detect PA-only when verified=0 (no function contracts verified)"
        )

    def test_wire_line_no_pa_failure_not_detected(self):
        """_wire_line_shows_pa_only_failure returns False when no PA failures."""
        output = (
            _wire_line(verified=6, trusted=30, skipped=3)
        )
        assert not harness._wire_line_shows_pa_only_failure(output), (
            "should not detect PA-only when pa_failed=0 and pa_errors=0"
        )

    def test_wire_line_missing_pa_fields_not_detected(self):
        """Telemetry without proof_assert fields is not treated as valid PA data."""
        output = (
            "TRUST_WP_RESULT:v1 base_exit_code=0 verified=6 failed=0 errors=0 "
            "warnings=0 assumed=0 trusted=30 skipped=3 "
            "verified_with_axiom_deps=0 unverified_axioms=0 vacuous=0 "
            "evidence_gaps=0 panics=0 demoted=0 parse_errors=0 "
            "termination_errors=0 logic_recursion_errors=0\n"
        )
        assert not harness._wire_line_shows_pa_only_failure(output), (
            "should not detect PA-only issues when proof_assert telemetry is absent"
        )

    def test_wire_line_pa_errors_also_detected(self):
        """_wire_line_shows_pa_only_failure returns True for PA errors too."""
        output = (
            _wire_line(
                base_exit_code=2,
                verified=6,
                trusted=30,
                skipped=3,
                proof_assert_errors=2,
            )
        )
        assert harness._wire_line_shows_pa_only_failure(output), (
            "should detect PA-only when pa_errors=2 (not just pa_failed)"
        )

    def test_classify_failure_uses_wire_line_for_multi_crate(self):
        """Multi-crate output: std crate verified, test crate PA-only → fail closed.

        This models the cc/arithmetic.rs pattern: the std crate has verified
        functions but the test crate only has proof_asserts. The last
        function-level summary is (0,0,0) from the test crate, and the
        TRUST_WP_RESULT aggregates to verified=6, pa_failed=3.
        """
        output = (
            "functions with contracts found count=39\n"
            "trust-wp: ghost::perm::Container::is_disjoint verified \u2713\n"
            "trust-wp: 6 verified, 0 failed, 0 errors, 30 trusted, 3 skipped\n"
            "functions with contracts found count=3\n"
            "trust-wp: proof_assert in creusot_test::test FAILED \u2717\n"
            "  at src/lib.rs:7:5: 7:44\n"
            "  assertion: 0u8.nth_bit(42) == false\n"
            "trust-wp: 0 verified, 0 failed, 0 errors\n"
            "trust-wp: proof_assert: 0 verified, 3 failed, 0 errors\n"
            "error: could not compile `creusot_test` (lib)\n"
            + _wire_line(
                base_exit_code=1,
                verified=6,
                trusted=30,
                skipped=3,
                proof_assert_failed=3,
            )
        )
        source = "proof_assert!(0u8.nth_bit(42) == false);\n"
        status, reason = harness.classify_failure(output, source)
        assert status == "fail", (
            f"Wire-line PA-only failure should fail closed, got '{status}' (reason={reason})"
        )

    def test_classify_failure_uses_wire_line_for_pa_errors(self):
        """Valid wire telemetry with proof_assert_errors does not plain-pass."""
        output = (
            "functions with contracts found count=1\n"
            "trust-wp: my_fn verified \u2713\n"
            "trust-wp: 1 verified, 0 failed, 0 errors\n"
            "trust-wp: proof_assert: 0 verified, 0 failed, 2 errors\n"
            + _wire_line(
                base_exit_code=2,
                verified=1,
                proof_assert_errors=2,
            )
        )
        source = "#[ensures(result > 0)]\nfn my_fn() -> i32 { 1 }\nproof_assert!(false);\n"
        status, reason = harness.classify_failure(output, source)
        assert status == "fail", (
            f"Wire-line PA errors should fail closed, got '{status}' (reason={reason})"
        )

    def test_panics_block_pa_only_classification(self):
        """Panics in wire line prevent PA-only pass classification."""
        output = (
            _wire_line(
                base_exit_code=1,
                verified=6,
                trusted=30,
                skipped=3,
                proof_assert_failed=1,
                panics=1,
            )
        )
        assert not harness._wire_line_shows_pa_only_failure(output), (
            "should not detect PA-only when panics=1"
        )


# ---------------------------------------------------------------------------
# classify_failure: documented spurious-PA-counterexample reclassification
# ---------------------------------------------------------------------------


class TestSpuriousPaCounterexampleReclassification:
    """Known spurious proof_assert counterexamples classify as unknown.

    Tests on ``_KNOWN_SPURIOUS_PA_COUNTEREXAMPLE_TESTS`` (semantically true
    asserts, no genuine refuting model exists) are demoted from "fail" to
    "unknown" when the wire-line PA-only-failure signature fires. This
    matches the LRA spurious-SAT precedent (#2674) and deliberately does
    NOT restore the pre-hardening #2700 "pass" credit.
    """

    _LISTED_TEST = "tests/should_succeed/closures/09_fnonce_resolve.rs"

    def _pa_only_output(self) -> str:
        return (
            "functions with contracts found count=1\n"
            "trust-wp: f::{closure#0} verified ✓\n"
            "trust-wp: proof_assert in creusot_test::f FAILED ✗\n"
            "  at src/lib.rs:26:5: 26:30\n"
            "  assertion: x@+y@ == 3\n"
            "trust-wp: 1 verified, 0 failed, 0 errors\n"
            "trust-wp: proof_assert: 0 verified, 1 failed, 4 errors\n"
            "error: could not compile `creusot_test` (lib)\n"
            + _wire_line(
                base_exit_code=1,
                verified=1,
                proof_assert_failed=1,
                proof_assert_errors=4,
            )
        )

    _SOURCE = (
        "pub fn f(c: bool) {\n"
        "    let mut x = 1i32;\n"
        "    proof_assert!(x@+y@ == 3);\n"
        "}\n"
    )

    def test_listed_test_classifies_as_unknown_with_reason(self):
        """Listed test + PA-only wire signature → unknown, documented reason."""
        status, reason = harness.classify_failure(
            self._pa_only_output(),
            self._SOURCE,
            test_name=self._LISTED_TEST,
        )
        assert status == "unknown", (
            f"Listed spurious-PA test should be unknown, got '{status}'"
        )
        assert reason is not None and "spurious proof_assert counterexample" in reason, (
            f"Expected documented spurious-counterexample reason, got {reason!r}"
        )

    def test_unlisted_test_still_fails_closed(self):
        """Unlisted test with the same signature keeps the fail-closed verdict."""
        status, reason = harness.classify_failure(
            self._pa_only_output(),
            self._SOURCE,
            test_name="tests/should_succeed/closures/07_mutable_capture.rs",
        )
        assert status == "fail", (
            f"Unlisted PA-only failure must stay fail, got '{status}' (reason={reason})"
        )

    def test_missing_test_name_still_fails_closed(self):
        """No test_name (e.g. reclassify tooling without names) → fail closed."""
        status, _reason = harness.classify_failure(
            self._pa_only_output(), self._SOURCE
        )
        assert status == "fail", (
            f"PA-only failure without test_name must stay fail, got '{status}'"
        )

    def test_listed_test_function_level_failure_not_demoted(self):
        """A function-level failure on a listed test is NOT demoted to unknown.

        The table is consulted only when the PA-only-failure signature fires
        (function-level clean); a genuine contract failure must surface.
        """
        output = (
            "functions with contracts found count=1\n"
            "trust-wp: f::{closure#0} FAILED ✗\n"
            "trust-wp: 0 verified, 1 failed, 0 errors\n"
            "trust-wp: proof_assert: 0 verified, 1 failed, 0 errors\n"
            + _wire_line(
                base_exit_code=1,
                failed=1,
                proof_assert_failed=1,
            )
        )
        status, _reason = harness.classify_failure(
            output, self._SOURCE, test_name=self._LISTED_TEST
        )
        assert status == "fail", (
            f"Function-level failure must stay fail even when listed, got '{status}'"
        )

    def test_nonzero_process_result_overrides_pa_reclassification(self):
        """Semantic PA policy cannot mask an outer command failure."""
        status, reason = harness.classify_failure(
            self._pa_only_output(),
            self._SOURCE,
            exit_code=1,
            test_name=self._LISTED_TEST,
        )
        assert status == "error"
        assert reason is None

    def test_listed_test_clean_run_passes_normally(self):
        """A fixed listed test (no PA issues) takes the normal pass path.

        Guards the table's exit criterion: a stale entry cannot mask a
        genuinely fixed test.
        """
        output = (
            "functions with contracts found count=1\n"
            "trust-wp: f::{closure#0} verified ✓\n"
            "trust-wp: 1 verified, 0 failed, 0 errors\n"
            "trust-wp: proof_assert: 5 verified, 0 failed, 0 errors\n"
            + _wire_line(base_exit_code=0, verified=1)
        )
        status, reason = harness.classify_failure(
            output, self._SOURCE, exit_code=0, test_name=self._LISTED_TEST
        )
        assert status == "pass", (
            f"Fixed listed test should pass normally, got '{status}' (reason={reason})"
        )

    def test_table_entries_are_documented(self):
        """Every table entry carries a non-empty justification string."""
        from tests.creusot_compat.harness_classify_succeed import (
            _KNOWN_SPURIOUS_PA_COUNTEREXAMPLE_TESTS,
        )

        assert _KNOWN_SPURIOUS_PA_COUNTEREXAMPLE_TESTS, "table should not be empty"
        for name, why in _KNOWN_SPURIOUS_PA_COUNTEREXAMPLE_TESTS.items():
            assert name.startswith("tests/should_succeed/"), (
                f"table is scoped to the should_succeed lane, got {name!r}"
            )
            assert isinstance(why, str) and len(why) > 40, (
                f"entry {name!r} needs a substantive justification"
            )


# ---------------------------------------------------------------------------
# classify_failure: no-contract bucket exit-code split
# ---------------------------------------------------------------------------


class TestNoContractClassification:
    """Tests for clean vs failed no-contract crates."""

    def test_no_contract_nonzero_exit_is_error(self):
        """No-contract crates with a non-zero exit fail closed."""
        output = "trust-wp: Found 0 functions with contracts:\ntrust_wp: 0 verified, 0 failed, 0 errors"
        status, reason = harness.classify_failure(
            output=output,
            source="fn no_contract() {}",
            exit_code=1,
        )
        assert status == "error", f"expected non-zero no-contract run to error, got {status!r}"
        assert reason is None, f"Expected no skip reason for no-contract error, got {reason!r}"

    def test_no_contract_zero_exit_is_pass(self):
        """Clean no-contract crates remain pass for actionable metrics."""
        output = "trust-wp: Found 0 functions with contracts:\ntrust_wp: 0 verified, 0 failed, 0 errors"
        status, reason = harness.classify_failure(
            output=output,
            source="fn no_contract() {}",
            exit_code=0,
        )
        assert status == "pass", f"expected clean no-contract run to pass, got {status!r}"
        assert reason is None, f"expected no skip reason for clean no-contract pass, got {reason!r}"


# ---------------------------------------------------------------------------
# extern_spec / trusted-only classification (#2675)
# ---------------------------------------------------------------------------


class TestExternSpecTrustedOnlyClassification:
    """Tests where source has contracts only inside extern_spec! or #[trusted].

    When trust-wp exits cleanly (code 0) and found 0 verifiable contracts,
    the source's contract annotations are in non-verifiable contexts.
    These should classify as "pass", not "skip". (#2675)
    """

    def test_extern_spec_only_contracts_classified_as_pass(self):
        """Source with #[ensures] only inside extern_spec!, exit_code=0 → pass."""
        output = (
            "trust-wp: 0 verified, 0 failed, 0 errors, 1 trusted\n"
            + _wire_line(trusted=1)
        )
        source = (
            'extern_spec! {\n'
            '    impl UseSelf for i32 {\n'
            '        #[ensures(result == (*self == 1i32))]\n'
            '        fn func(&self, s: &Self) -> bool;\n'
            '    }\n'
            '}\n'
        )
        status, reason = harness.classify_failure(output, source, exit_code=0)
        assert status == "pass", (
            f"extern_spec-only contracts with exit 0 should be pass, got '{status}'"
        )

    def test_extern_spec_contracts_with_nonzero_exit_is_error(self):
        """Source with extern_spec! contracts, exit_code=2 → error."""
        output = (
            "trust-wp: 0 verified, 0 failed, 0 errors\n"
            + _wire_line(base_exit_code=2, assumed=3)
        )
        source = (
            'extern_spec! {\n'
            '    #[ensures(result == x + 1)]\n'
            '    fn add_one(x: i32) -> i32;\n'
            '}\n'
        )
        status, reason = harness.classify_failure(output, source, exit_code=2)
        assert status == "error", (
            f"extern_spec with exit 2 should be error, got '{status}'"
        )

    def test_trusted_only_nonzero_exit_is_error(self):
        """Trusted markers cannot override a failed verifier process."""
        output = (
            "trust-wp: Found 1 functions with contracts:\n"
            "trust-wp: f trusted (skipped)\n"
            "trust-wp: 0 verified, 0 failed, 0 errors, 1 trusted\n"
            + _wire_line(base_exit_code=2, trusted=1)
        )
        status, reason = harness.classify_failure(
            output,
            "#[trusted]\nfn f() {}",
            exit_code=2,
        )
        assert status == "error"
        assert reason is None

    def test_logic_only_nonzero_exit_is_error(self):
        """A logic source marker is not success evidence for exit 2."""
        output = (
            "trust-wp: Found 0 functions with contracts:\n"
            "trust-wp: 0 verified, 0 failed, 0 errors\n"
            + _wire_line(base_exit_code=2)
        )
        status, reason = harness.classify_failure(
            output,
            "#[logic]\nfn f() -> bool { true }",
            exit_code=2,
        )
        assert status == "error"
        assert reason is None

    def test_proof_assert_only_requires_proof_summary(self):
        """Source text plus an all-zero wire line cannot prove an assertion ran."""
        output = (
            "trust-wp: Found 0 functions with contracts:\n"
            "trust-wp: 0 verified, 0 failed, 0 errors\n"
            + _wire_line()
        )
        status, reason = harness.classify_failure(
            output,
            "fn f() { proof_assert!(true); }",
            exit_code=0,
        )
        assert status == "error"
        assert reason is None

    def test_proof_assert_only_nonzero_exit_is_error(self):
        """A proof_assert source marker cannot override a failed process."""
        output = (
            "trust-wp: Found 0 functions with contracts:\n"
            "trust-wp: 0 verified, 0 failed, 0 errors\n"
            + _wire_line(base_exit_code=2)
        )
        status, reason = harness.classify_failure(
            output,
            "fn f() { proof_assert!(true); }",
            exit_code=2,
        )
        assert status == "error"
        assert reason is None

    def test_source_has_user_contracts_excludes_extern_spec(self):
        """_source_has_user_contracts returns False when contracts are only in extern_spec!."""
        source = (
            'extern_spec! {\n'
            '    impl UseSelf for i32 {\n'
            '        #[ensures(result == (*self == 1i32))]\n'
            '        fn func(&self, s: &Self) -> bool;\n'
            '    }\n'
            '}\n'
        )
        result = harness._source_has_user_contracts(source)
        assert not result, (
            "_source_has_user_contracts should return False for extern_spec-only contracts"
        )

    def test_source_has_user_contracts_detects_contracts_outside_extern_spec(self):
        """_source_has_user_contracts returns True when contracts exist outside extern_spec!."""
        source = (
            'extern_spec! {\n'
            '    #[ensures(result == x)]\n'
            '    fn identity(x: i32) -> i32;\n'
            '}\n'
            '#[requires(x > 0)]\n'
            'fn positive(x: i32) -> i32 { x }\n'
        )
        result = harness._source_has_user_contracts(source)
        assert result, (
            "_source_has_user_contracts should return True when contracts exist outside extern_spec!"
        )


# ---------------------------------------------------------------------------
# Dropped obligation safety net (#1739)
# ---------------------------------------------------------------------------


class TestDroppedObligationWarningCount:
    """Tests for _dropped_obligation_warning_count parser."""

    def test_no_warnings_returns_zero(self):
        output = "trust-wp: 1 verified, 0 failed, 0 errors\n"
        result = harness._dropped_obligation_warning_count(output)
        assert result == 0, f"expected 0 for clean summary, got {result}"

    def test_single_warning_parsed(self):
        output = "trust-wp: 0 verified, 0 failed, 0 errors, 1 warnings (obligations dropped)\n"
        result = harness._dropped_obligation_warning_count(output)
        assert result == 1, f"expected 1, got {result}"

    def test_multiple_warnings_parsed(self):
        output = "trust-wp: 0 verified, 2 failed, 0 errors, 5 warnings (obligations dropped)\n"
        result = harness._dropped_obligation_warning_count(output)
        assert result == 5, f"expected 5, got {result}"

    def test_singular_warning_parsed(self):
        output = "trust-wp: 0 verified, 0 failed, 0 errors, 1 warning (obligation dropped)\n"
        result = harness._dropped_obligation_warning_count(output)
        assert result == 1, f"expected 1 for singular form, got {result}"

    def test_proof_assert_lines_excluded(self):
        output = (
            "trust-wp: proof_assert: 0 verified, 0 failed, 1 errors, "
            "2 warnings (obligations dropped)\n"
        )
        result = harness._dropped_obligation_warning_count(output)
        assert result == 0, f"proof_assert lines should be excluded, got {result}"


class TestDroppedObligationClassification:
    """Fail-closed safety net: dropped obligation warnings classify as error (#1739)."""

    def test_dropped_warnings_classify_as_error(self):
        """Summary with dropped obligations should classify as error, not skip or pass."""
        output = (
            "trust-wp: Found 1 functions with contracts:\n"
            "  foo\n"
            "trust-wp: verifying foo at src/lib.rs:1:1\n"
            "trust-wp: 0 verified, 0 failed, 0 errors, "
            "2 warnings (obligations dropped)\n"
        )
        status, reason = harness.classify_failure(
            output=output,
            source="#[requires(x > 0)]\nfn foo(x: i32) {}",
        )
        assert status == "error", f"dropped obligations should be error, got {status}"
        assert reason is not None, "error reason should not be None"
        assert "obligations dropped" in reason, f"reason should mention obligations, got {reason}"

    def test_dropped_warnings_are_verification_failures(self):
        """_has_verification_failures returns True for dropped obligations."""
        output = "trust-wp: 1 verified, 0 failed, 0 errors, 1 warnings (obligations dropped)\n"
        assert harness._has_verification_failures(output), (
            "dropped obligation warnings should count as verification failures"
        )

    def test_clean_summary_is_not_failure(self):
        """A clean summary without warnings is not a failure."""
        output = "trust-wp: 1 verified, 0 failed, 0 errors\n"
        assert not harness._has_verification_failures(output), (
            "clean summary without warnings should not be a failure"
        )


# ---------------------------------------------------------------------------
# classify_failure: contract-only bucket should use test-crate contract count
# ---------------------------------------------------------------------------


class TestContractBucketDiscoveryParsing:
    """Regression tests for contract-bearing 0-verified should_succeed cases (#822)."""

    OUTPUT_WITH_DEP_ZERO_AND_TEST_ONE = """\
trust-wp: Found 0 functions with contracts:
trust-wp: 0 MIR bodies available
trust-wp: Found 0 functions with contracts:
trust-wp: 0 MIR bodies available
    Checking creusot_test v0.1.0 (/tmp/test_project)
trust-wp: track_level=Auto

trust-wp: Found 1 functions with contracts:
  omg
    ensures: result@ == n@ * (n@ + 1) / 2

trust-wp: verifying omg at src/lib.rs:8:1: 8:30
trust-wp: omg unknown (incomplete)
trust-wp: 0 verified, 0 failed, 1 errors
"""

    def test_last_contract_count_prefers_test_crate_summary(self):
        """Dependency crate zero-count lines must not override test crate discovery."""
        assert harness._last_contract_count(self.OUTPUT_WITH_DEP_ZERO_AND_TEST_ONE) == 1

    def test_contract_only_failure_not_classified_as_no_contracts(self):
        """Contract-bearing tests with solver-unknown output are 'unknown', not skip (#1163)."""
        status, reason = harness.classify_failure(
            output=self.OUTPUT_WITH_DEP_ZERO_AND_TEST_ONE,
            source="#[ensures(result@ == n@ * (n@ + 1) / 2)]\nfn omg(n: usize) -> usize { n }",
        )
        # The output has "unknown (incomplete)" with 0 failed, 1 errors in the
        # summary — this is a solver-unknown result, not a genuine failure.
        assert status == "unknown"
        assert reason is None


# ---------------------------------------------------------------------------
# _last_contract_count: tracing structured format support (#1474)
# ---------------------------------------------------------------------------


class TestContractCountTracingFormat:
    """Tests for tracing structured output format: 'functions with contracts found count=N'."""

    TRACING_OUTPUT_ONE = """\
functions with contracts found count=1
trust-wp::verify_crate{contracts_total=1 track_level=Auto verify_enabled=true}:trust-wp::verify_function{fn_name=increment}
trust-wp: increment verified
trust-wp: 1 verified, 0 failed, 0 errors
"""

    TRACING_OUTPUT_MULTI_CRATE = """\
functions with contracts found count=0
functions with contracts found count=0
functions with contracts found count=2
trust-wp: verifying foo at src/lib.rs:1:1: 1:20
trust-wp: foo verified
trust-wp: verifying bar at src/lib.rs:5:1: 5:20
trust-wp: bar unknown (incomplete)
trust-wp: 1 verified, 0 failed, 1 errors
"""

    def test_tracing_format_single_crate(self):
        """Tracing structured format 'count=N' is parsed correctly."""
        count = harness._last_contract_count(self.TRACING_OUTPUT_ONE)
        assert count == 1, f"Expected 1 contract from tracing format, got {count}"

    def test_tracing_format_multi_crate_prefers_last(self):
        """Last tracing count=N line wins over earlier zero-count lines."""
        count = harness._last_contract_count(self.TRACING_OUTPUT_MULTI_CRATE)
        assert count == 2, f"Expected 2 contracts from last tracing line, got {count}"

    def test_tracing_format_not_classified_as_skip(self):
        """Tests with tracing contract output must not be classified as 'skip: no contracts'."""
        status, reason = harness.classify_failure(
            output=self.TRACING_OUTPUT_MULTI_CRATE,
            source="#[ensures(result > 0)]\nfn foo() -> i32 { 1 }",
        )
        assert status != "skip" or reason != "no contracts", (
            f"Tracing format misclassified as skip/no-contracts: status={status}, reason={reason}"
        )


# ---------------------------------------------------------------------------
# _all_contracts_axiomatized: last contract block only (#893 follow-up)
# ---------------------------------------------------------------------------


class TestAllContractsAxiomatizedCounting:
    """Regression tests for logic-function-only classification counting."""

    OUTPUT_DEP_LOGIC_TEST_NO_LOGIC = """\
trust-wp: Found 2 functions with contracts:
trust-wp: dep::a is a logic function (axiomatized, not verified)
trust-wp: dep::b is a logic function (postcondition will be verified)
trust-wp: 0 verified, 0 failed, 0 errors
    Checking creusot_test v0.1.0 (/tmp/test_project)
trust-wp: Found 1 functions with contracts:
trust-wp: 0 verified, 0 failed, 0 errors
"""

    OUTPUT_TEST_LOGIC_POSTCONDITION = """\
trust-wp: Found 1 functions with contracts:
trust-wp: test::inv is a logic function (postcondition will be verified)
trust-wp: 0 verified, 0 failed, 0 errors
"""

    def test_ignores_dependency_logic_function_messages(self):
        """Dependency logic messages must not classify test crate as logic-only pass."""
        assert harness._all_contracts_axiomatized(self.OUTPUT_DEP_LOGIC_TEST_NO_LOGIC, 1) is False

    def test_counts_postcondition_verified_logic_message(self):
        """Logic functions with postcondition-verification marker count as logic-only."""
        assert harness._all_contracts_axiomatized(self.OUTPUT_TEST_LOGIC_POSTCONDITION, 1) is True


# ---------------------------------------------------------------------------
# _has_verified_contracts: dependency crate scoping (#1325)
# ---------------------------------------------------------------------------


class TestHasVerifiedContractsDependencyScoping:
    """Regression tests: dependency crate 'verified ✓' must not affect test crate classification."""

    OUTPUT_DEP_VERIFIED_TEST_EMPTY = """\
trust-wp: Found 1 functions with contracts:
trust-wp: dep::func verified ✓
trust-wp: 1 verified, 0 failed, 0 errors
    Checking creusot_test v0.1.0 (/tmp/test_project)
trust-wp: Found 1 functions with contracts:
trust-wp: test::logic_fn is a logic function (axiomatized, not verified)
trust-wp: 0 verified, 0 failed, 0 errors
"""

    OUTPUT_TEST_CRATE_VERIFIED = """\
trust-wp: Found 1 functions with contracts:
trust-wp: test::my_func verified ✓
trust-wp: 1 verified, 0 failed, 0 errors
"""

    OUTPUT_NO_CONTRACT_BLOCKS = """\
    Compiling creusot_test v0.1.0 (/tmp/test_project)
"""

    def test_dep_verified_marker_does_not_count_for_test_crate(self):
        """Dependency crate 'verified ✓' must not make test crate look verified (#1325)."""
        assert harness._has_verified_contracts(self.OUTPUT_DEP_VERIFIED_TEST_EMPTY) is False, (
            "dependency crate 'verified ✓' leaked into test crate classification"
        )

    def test_test_crate_verified_marker_still_detected(self):
        """Test crate 'verified ✓' in the last contract block is still detected."""
        assert harness._has_verified_contracts(self.OUTPUT_TEST_CRATE_VERIFIED) is True, (
            "test crate 'verified ✓' should be detected in the last contract block"
        )

    def test_no_contract_blocks_returns_false(self):
        """Output with no contract discovery blocks returns False."""
        assert harness._has_verified_contracts(self.OUTPUT_NO_CONTRACT_BLOCKS) is False, (
            "output with no contract blocks should not report verified contracts"
        )


# ---------------------------------------------------------------------------
# _get_dirty_files porcelain parsing (#776)
# ---------------------------------------------------------------------------


class TestGetDirtyFiles:
    """_get_dirty_files correctly parses git status --porcelain output."""

    def test_leading_space_in_porcelain_preserves_first_path(self, monkeypatch):
        """Regression: first path must not be truncated when porcelain line starts with space.

        `git status --porcelain` outputs lines like ' M crates/foo.rs' (space + status + space + path).
        Previously, strip() on the full output removed the leading space from the first line,
        causing line[3:] to over-trim by one character (e.g., 'rates/foo.rs' instead of 'crates/foo.rs').
        """
        porcelain_output = " M crates/trust-wp-ay/src/lib.rs\n M crates/trust-wp/src/lib.rs\n"
        mock_result = subprocess.CompletedProcess(
            args=[], returncode=0, stdout=porcelain_output, stderr=""
        )
        monkeypatch.setattr(
            subprocess, "run", lambda *args, **kwargs: mock_result
        )
        files = harness._get_dirty_files(Path("/fake/workspace"))
        assert files == [
            "crates/trust-wp-ay/src/lib.rs",
            "crates/trust-wp/src/lib.rs",
        ]
        # Specifically verify first path is not truncated
        assert files[0].startswith("crates/"), f"First path truncated: {files[0]}"


# ---------------------------------------------------------------------------
# Output artifact filtering for provenance (#679)
# ---------------------------------------------------------------------------


class TestFilterSourceDirtyFiles:
    """_filter_source_dirty_files excludes output artifacts from provenance."""

    def test_filters_reports_prefix(self):
        dirty = ["reports/baseline.json", "src/lib.rs"]
        assert harness._filter_source_dirty_files(dirty) == ["src/lib.rs"]

    def test_preserves_source_only_list(self):
        dirty = ["crates/trust-wp-ay/src/lib.rs", "Cargo.toml"]
        assert harness._filter_source_dirty_files(dirty) == dirty

    def test_empty_when_all_artifacts(self):
        dirty = ["reports/a.json", "reports/b.json"]
        assert harness._filter_source_dirty_files(dirty) == []

    def test_empty_input(self):
        assert harness._filter_source_dirty_files([]) == []

    def test_nested_reports_path(self):
        dirty = ["reports/research/reflection.md", "src/main.rs"]
        assert harness._filter_source_dirty_files(dirty) == ["src/main.rs"]

    def test_filters_canonical_lane_outputs(self):
        dirty = [
            "tests/creusot_compat/results.json",
            "tests/creusot_compat/results-should-fail.json",
            "tests/creusot_compat/results-examples.json",
            "src/main.rs",
        ]
        assert harness._filter_source_dirty_files(dirty) == ["src/main.rs"], (
            "Canonical lane outputs should not count as source-dirty files"
        )

    def test_filters_exploratory_lane_outputs(self):
        dirty = [
            "tests/creusot_compat/results-targeted.json",
            "tests/creusot_compat/results-prover-head-sample.json",
            "Cargo.toml",
        ]
        assert harness._filter_source_dirty_files(dirty) == ["Cargo.toml"]

    def test_filters_lock_and_binary_artifacts(self):
        dirty = [
            ".test_state.json.lock",
            ".ownership_conflicts.log.lock",
            "libhashmap_iter_test.rlib",
            "test_doc_closure",
            "tests/fixtures/proof_assert/test_multi_field",
            "crates/trust-wp-ay/src/lib.rs",
        ]
        assert harness._filter_source_dirty_files(dirty) == [
            "crates/trust-wp-ay/src/lib.rs"
        ]

    def test_preserves_source_file_with_test_prefix(self):
        dirty = [
            "tests/fixtures/proof_assert/src/test_multi_field.rs",
            "src/lib.rs",
        ]
        assert harness._filter_source_dirty_files(dirty) == dirty


# ---------------------------------------------------------------------------
# Clean-tree gating for canonical baseline writes (#636)
# ---------------------------------------------------------------------------


class TestCleanTreeGating:
    """Canonical baseline writes require a clean working tree."""

    def test_dirty_canonical_run_exits_3_without_allow_dirty(self, monkeypatch, capsys):
        """Dirty canonical runs should fail closed with usage exit code 3."""
        monkeypatch.setattr(sys, "argv", ["harness.py"])
        monkeypatch.setattr(harness, "find_workspace_root", lambda: WORKSPACE_ROOT)
        monkeypatch.setattr(
            harness, "_get_dirty_files", lambda _workspace: ["crates/trust-wp-ay/src/lib.rs"]
        )

        exit_code = harness.main()
        captured = capsys.readouterr()

        assert exit_code == 3
        assert "Working tree is dirty" in captured.err
        assert "canonical baseline would be non-reproducible" in captured.err

    def test_report_artifacts_do_not_block_canonical_run(self, monkeypatch, tmp_path):
        """Output artifacts in reports/ should not block canonical baseline writes (#679)."""
        canonical_output = tmp_path / "results.json"
        canonical_should_fail_output = tmp_path / "results-should-fail.json"

        monkeypatch.setattr(harness, "CANONICAL_OUTPUT", str(canonical_output))
        monkeypatch.setattr(
            harness, "CANONICAL_SHOULD_FAIL_OUTPUT", str(canonical_should_fail_output)
        )
        monkeypatch.setattr(sys, "argv", ["harness.py", "--output", str(canonical_output)])
        monkeypatch.setattr(harness, "find_workspace_root", lambda: WORKSPACE_ROOT)
        # Only dirty file is a prior lane's output in reports/
        monkeypatch.setattr(
            harness,
            "_get_dirty_files",
            lambda _workspace: ["reports/creusot-compat-baseline-should-fail.json"],
        )
        monkeypatch.setattr(
            harness, "find_creusot_tests", lambda _workspace, lane="should_succeed": []
        )
        monkeypatch.setattr(harness, "run_harness", lambda **_kwargs: [])
        monkeypatch.setattr(harness, "compute_lane_pair_freshness", lambda **_kwargs: None)

        exit_code = harness.main()

        # Should succeed (exit 0), not be blocked by the reports/ artifact
        assert exit_code == 0
        payload = json.loads(canonical_output.read_text())
        # Provenance should be clean (no -dirty suffix)
        assert not payload["metadata"]["git_commit"].endswith("-dirty")

    def test_lock_and_binary_artifacts_do_not_block_canonical_run(
        self, monkeypatch, tmp_path
    ):
        """Transient harness lock/build artifacts should not require --allow-dirty."""
        canonical_output = tmp_path / "results.json"
        canonical_should_fail_output = tmp_path / "results-should-fail.json"

        monkeypatch.setattr(harness, "CANONICAL_OUTPUT", str(canonical_output))
        monkeypatch.setattr(
            harness, "CANONICAL_SHOULD_FAIL_OUTPUT", str(canonical_should_fail_output)
        )
        monkeypatch.setattr(sys, "argv", ["harness.py", "--output", str(canonical_output)])
        monkeypatch.setattr(harness, "find_workspace_root", lambda: WORKSPACE_ROOT)
        monkeypatch.setattr(
            harness,
            "_get_dirty_files",
            lambda _workspace: [
                ".test_state.json.lock",
                ".ownership_conflicts.log.lock",
                "libhashmap_iter_test.rlib",
                "test_doc_closure",
                "tests/fixtures/proof_assert/test_multi_field",
            ],
        )
        monkeypatch.setattr(
            harness, "find_creusot_tests", lambda _workspace, lane="should_succeed": []
        )
        monkeypatch.setattr(harness, "run_harness", lambda **_kwargs: [])
        monkeypatch.setattr(harness, "compute_lane_pair_freshness", lambda **_kwargs: None)

        exit_code = harness.main()

        assert exit_code == 0
        payload = json.loads(canonical_output.read_text())
        assert payload["metadata"]["lane"] == "should_succeed"

    def test_prior_canonical_lane_output_does_not_block_other_lane(
        self, monkeypatch, tmp_path
    ):
        """Sequential canonical lane refresh should not require --allow-dirty.

        Regression: running should_succeed first dirties
        tests/creusot_compat/results.json. That output artifact must not block a
        subsequent canonical should_fail run (#352 baseline refresh workflow).
        """
        canonical_output = tmp_path / "results.json"
        canonical_should_fail_output = tmp_path / "results-should-fail.json"

        monkeypatch.setattr(harness, "CANONICAL_OUTPUT", str(canonical_output))
        monkeypatch.setattr(
            harness, "CANONICAL_SHOULD_FAIL_OUTPUT", str(canonical_should_fail_output)
        )
        monkeypatch.setattr(
            sys,
            "argv",
            [
                "harness.py",
                "--lane",
                "should_fail",
                "--output",
                str(canonical_should_fail_output),
            ],
        )
        monkeypatch.setattr(harness, "find_workspace_root", lambda: WORKSPACE_ROOT)
        monkeypatch.setattr(
            harness,
            "_get_dirty_files",
            lambda _workspace: ["tests/creusot_compat/results.json"],
        )
        monkeypatch.setattr(
            harness, "find_creusot_tests", lambda _workspace, lane="should_fail": []
        )
        monkeypatch.setattr(harness, "run_harness", lambda **_kwargs: [])
        monkeypatch.setattr(harness, "compute_lane_pair_freshness", lambda **_kwargs: None)

        exit_code = harness.main()

        assert exit_code == 0
        payload = json.loads(canonical_should_fail_output.read_text())
        assert payload["metadata"]["lane"] == "should_fail"

    def test_report_artifacts_excluded_from_provenance_but_recorded(
        self, monkeypatch, tmp_path
    ):
        """Reports/ artifacts should not cause -dirty provenance but still appear in metadata (#679)."""
        canonical_output = tmp_path / "results.json"
        canonical_should_fail_output = tmp_path / "results-should-fail.json"

        monkeypatch.setattr(harness, "CANONICAL_OUTPUT", str(canonical_output))
        monkeypatch.setattr(
            harness, "CANONICAL_SHOULD_FAIL_OUTPUT", str(canonical_should_fail_output)
        )
        monkeypatch.setattr(
            sys,
            "argv",
            ["harness.py", "--allow-dirty", "--output", str(canonical_output)],
        )
        monkeypatch.setattr(harness, "find_workspace_root", lambda: WORKSPACE_ROOT)
        monkeypatch.setattr(
            harness,
            "_get_dirty_files",
            lambda _workspace: ["reports/baseline-should-fail.json", "src/lib.rs"],
        )
        monkeypatch.setattr(
            harness, "find_creusot_tests", lambda _workspace, lane="should_succeed": []
        )
        monkeypatch.setattr(harness, "run_harness", lambda **_kwargs: [])
        monkeypatch.setattr(harness, "compute_lane_pair_freshness", lambda **_kwargs: None)

        exit_code = harness.main()

        assert exit_code == 0
        payload = json.loads(canonical_output.read_text())
        # git_commit is always a clean SHA; dirty state in separate fields (#705)
        assert not payload["metadata"]["git_commit"].endswith("-dirty")
        # Full dirty list in metadata for audit transparency
        assert payload["metadata"]["dirty_file_count"] == 2
        assert "reports/baseline-should-fail.json" in payload["metadata"]["dirty_files"]
        assert "src/lib.rs" in payload["metadata"]["dirty_files"]

    def test_allow_dirty_bypasses_gate_for_canonical_output(self, monkeypatch, tmp_path):
        """--allow-dirty should allow canonical writes and record dirty metadata."""
        canonical_output = tmp_path / "results.json"
        canonical_should_fail_output = tmp_path / "results-should-fail.json"

        monkeypatch.setattr(harness, "CANONICAL_OUTPUT", str(canonical_output))
        monkeypatch.setattr(
            harness, "CANONICAL_SHOULD_FAIL_OUTPUT", str(canonical_should_fail_output)
        )
        monkeypatch.setattr(
            sys,
            "argv",
            ["harness.py", "--allow-dirty", "--output", str(canonical_output)],
        )
        monkeypatch.setattr(harness, "find_workspace_root", lambda: WORKSPACE_ROOT)
        monkeypatch.setattr(harness, "_get_dirty_files", lambda _workspace: ["foo.rs"])
        monkeypatch.setattr(
            harness, "find_creusot_tests", lambda _workspace, lane="should_succeed": []
        )
        monkeypatch.setattr(harness, "run_harness", lambda **_kwargs: [])
        monkeypatch.setattr(harness, "compute_lane_pair_freshness", lambda **_kwargs: None)

        exit_code = harness.main()

        assert exit_code == 0
        payload = json.loads(canonical_output.read_text())
        assert payload["metadata"]["dirty_file_count"] == 1
        assert payload["metadata"]["dirty_files"] == ["foo.rs"]

    def test_dirty_files_in_metadata(self):
        """When dirty_files is provided, metadata includes dirty file info."""
        args = argparse.Namespace(
            verbose=False,
            filter=None,
            limit=None,
            output=None,
            baseline=False,
            lane="should_succeed",
        )
        meta = harness.build_run_metadata(
            args,
            WORKSPACE_ROOT,
            discovered_count=10,
            executed_count=10,
            dirty_files=["foo.rs", "bar.py"],
        )
        assert meta["dirty_file_count"] == 2
        assert meta["dirty_files"] == ["foo.rs", "bar.py"]

    def test_clean_tree_metadata_has_no_dirty_fields(self):
        """When tree is clean (no dirty_files), metadata omits dirty fields."""
        args = argparse.Namespace(
            verbose=False,
            filter=None,
            limit=None,
            output=None,
            baseline=False,
            lane="should_succeed",
        )
        meta = harness.build_run_metadata(
            args,
            WORKSPACE_ROOT,
            discovered_count=10,
            executed_count=10,
            dirty_files=[],
        )
        assert "dirty_file_count" not in meta
        assert "dirty_files" not in meta

    def test_pinned_commit_overrides_git_query(self):
        """When pinned_commit is provided, it becomes git_commit (#647)."""
        args = argparse.Namespace(
            verbose=False,
            filter=None,
            limit=None,
            output=None,
            baseline=False,
            lane="should_succeed",
        )
        meta = harness.build_run_metadata(
            args,
            WORKSPACE_ROOT,
            discovered_count=10,
            executed_count=10,
            pinned_commit="abc1234",
        )
        assert meta["git_commit"] == "abc1234"

    def test_head_drift_recorded_when_positive(self):
        """head_drift_commits appears in metadata when >0 (#647)."""
        args = argparse.Namespace(
            verbose=False,
            filter=None,
            limit=None,
            output=None,
            baseline=False,
            lane="should_succeed",
        )
        meta = harness.build_run_metadata(
            args,
            WORKSPACE_ROOT,
            discovered_count=10,
            executed_count=10,
            pinned_commit="abc1234",
            head_drift_commits=5,
        )
        assert meta["head_drift_commits"] == 5

    def test_head_drift_policy_metadata(self):
        """Metadata records drift policy threshold and exceeded flag."""
        args = argparse.Namespace(
            verbose=False,
            filter=None,
            limit=None,
            output=None,
            baseline=False,
            lane="should_succeed",
        )
        meta = harness.build_run_metadata(
            args,
            WORKSPACE_ROOT,
            discovered_count=10,
            executed_count=10,
            pinned_commit="abc1234",
            head_drift_commits=5,
            head_drift_max_commits=3,
        )
        assert meta["head_drift_max_commits"] == 3
        assert meta["head_drift_exceeded"] is True

    def test_head_drift_omitted_when_zero(self):
        """head_drift_commits is absent when drift is 0 (#647)."""
        args = argparse.Namespace(
            verbose=False,
            filter=None,
            limit=None,
            output=None,
            baseline=False,
            lane="should_succeed",
        )
        meta = harness.build_run_metadata(
            args,
            WORKSPACE_ROOT,
            discovered_count=10,
            executed_count=10,
            pinned_commit="abc1234",
            head_drift_commits=0,
        )
        assert "head_drift_commits" not in meta

    def test_head_drift_policy_not_exceeded(self):
        """Zero drift still records policy threshold with exceeded=False."""
        args = argparse.Namespace(
            verbose=False,
            filter=None,
            limit=None,
            output=None,
            baseline=False,
            lane="should_succeed",
        )
        meta = harness.build_run_metadata(
            args,
            WORKSPACE_ROOT,
            discovered_count=10,
            executed_count=10,
            pinned_commit="abc1234",
            head_drift_commits=0,
            head_drift_max_commits=3,
        )
        assert "head_drift_commits" not in meta
        assert meta["head_drift_max_commits"] == 3
        assert meta["head_drift_exceeded"] is False


class TestHeadDriftPolicy:
    """CLI policy behavior for run-time HEAD drift thresholding."""

    def _patch_quick_run(
        self,
        monkeypatch,
        tmp_path: Path,
        argv: list[str],
        drift: int | None,
    ):
        output_path = tmp_path / "results.json"
        monkeypatch.setattr(sys, "argv", ["harness.py", *argv, "--output", str(output_path)])
        monkeypatch.setattr(harness, "find_workspace_root", lambda: WORKSPACE_ROOT)
        monkeypatch.setattr(harness, "_get_dirty_files", lambda _workspace: [])
        monkeypatch.setattr(
            harness, "find_creusot_tests", lambda _workspace, lane="should_succeed": []
        )
        monkeypatch.setattr(harness, "run_harness", lambda **_kwargs: [])
        monkeypatch.setattr(
            harness, "_get_git_commit", lambda _workspace, dirty_files=None: "abc1234"
        )
        monkeypatch.setattr(
            harness, "_commit_distance_to_head", lambda _workspace, _commit: drift
        )
        monkeypatch.setattr(harness, "compute_lane_pair_freshness", lambda **_kwargs: None)
        return output_path

    def test_warning_printed_when_drift_exceeds_threshold(
        self, monkeypatch, tmp_path, capsys
    ):
        output_path = self._patch_quick_run(
            monkeypatch,
            tmp_path,
            ["--max-head-drift-commits", "5"],
            drift=6,
        )
        exit_code = harness.main()
        captured = capsys.readouterr()
        metadata = json.loads(output_path.read_text())["metadata"]

        assert exit_code == 0, f"Expected warning-only full run to exit 0, got {exit_code!r}"
        assert "[HEAD DRIFT WARNING]" in captured.out, (
            f"Expected head-drift warning in output, got {captured.out!r}"
        )
        assert "policy max: 5" in captured.out, (
            f"Expected effective policy max 5 in output, got {captured.out!r}"
        )
        assert metadata["head_drift_max_commits"] == 5, (
            f"Expected full-run metadata threshold 5, got {metadata!r}"
        )
        assert "routing_safe" not in metadata, (
            f"Full-run metadata should not include routing_safe, got {metadata!r}"
        )

    def test_no_warning_when_drift_within_threshold(self, monkeypatch, tmp_path, capsys):
        self._patch_quick_run(
            monkeypatch,
            tmp_path,
            ["--max-head-drift-commits", "5"],
            drift=5,
        )
        exit_code = harness.main()
        captured = capsys.readouterr()

        assert exit_code == 0, f"Expected in-policy full run to exit 0, got {exit_code!r}"
        assert "[HEAD DRIFT WARNING]" not in captured.out, (
            f"Did not expect head-drift warning within threshold, got {captured.out!r}"
        )

    def test_partial_run_defaults_to_zero_drift_fail_closed(
        self, monkeypatch, tmp_path, capsys
    ):
        output_path = self._patch_quick_run(
            monkeypatch,
            tmp_path,
            ["--filter", "bug/"],
            drift=1,
        )
        exit_code = harness.main()
        captured = capsys.readouterr()
        metadata = json.loads(output_path.read_text())["metadata"]

        assert exit_code == harness.HEAD_DRIFT_POLICY_EXIT_CODE, (
            f"Expected partial run to fail closed with exit {harness.HEAD_DRIFT_POLICY_EXIT_CODE}, got {exit_code!r}"
        )
        assert "[HEAD DRIFT WARNING]" in captured.out, (
            f"Expected fail-closed partial warning in output, got {captured.out!r}"
        )
        assert "policy max: 0" in captured.out, (
            f"Expected zero-drift policy in output, got {captured.out!r}"
        )
        assert metadata["head_drift_max_commits"] == 0, (
            f"Expected partial default threshold 0, got {metadata!r}"
        )
        assert metadata["head_drift_exceeded"] is True, (
            f"Expected metadata to record exceeded zero-drift policy, got {metadata!r}"
        )
        assert metadata["routing_safe"] is False, (
            f"Expected drifted partial run to be marked non-routing-safe, got {metadata!r}"
        )
        assert metadata["provisional_reason"] == "head_drift", (
            f"Expected head_drift provisional reason, got {metadata!r}"
        )

    def test_partial_run_zero_drift_marks_output_routing_safe(
        self, monkeypatch, tmp_path, capsys
    ):
        output_path = self._patch_quick_run(
            monkeypatch,
            tmp_path,
            ["--filter", "bug/"],
            drift=0,
        )
        exit_code = harness.main()
        captured = capsys.readouterr()
        metadata = json.loads(output_path.read_text())["metadata"]

        assert exit_code == 0, f"Expected zero-drift partial run to exit 0, got {exit_code!r}"
        assert "[PROVISIONAL PARTIAL RUN]" not in captured.out, (
            f"Did not expect provisional banner for zero-drift partial run, got {captured.out!r}"
        )
        assert metadata["head_drift_max_commits"] == 0, (
            f"Expected zero-drift threshold metadata, got {metadata!r}"
        )
        assert metadata["head_drift_exceeded"] is False, (
            f"Expected zero drift not to exceed policy, got {metadata!r}"
        )
        assert metadata["routing_safe"] is True, (
            f"Expected zero-drift partial artifact to be routing-safe, got {metadata!r}"
        )
        assert "provisional_reason" not in metadata, (
            f"Did not expect provisional reason on routing-safe artifact, got {metadata!r}"
        )

    def test_partial_run_allow_head_drift_marks_output_provisional(
        self, monkeypatch, tmp_path, capsys
    ):
        output_path = self._patch_quick_run(
            monkeypatch,
            tmp_path,
            ["--filter", "bug/", "--allow-head-drift"],
            drift=1,
        )
        exit_code = harness.main()
        captured = capsys.readouterr()
        metadata = json.loads(output_path.read_text())["metadata"]

        assert exit_code == 0, f"Expected opt-out partial run to continue, got {exit_code!r}"
        assert "[PROVISIONAL PARTIAL RUN]" in captured.out, (
            f"Expected provisional partial banner in output, got {captured.out!r}"
        )
        assert metadata["head_drift_max_commits"] == harness.HEAD_DRIFT_MAX_COMMITS_DEFAULT, (
            "Expected opt-out partial run to retain the default full-run drift threshold, "
            f"got {metadata!r}"
        )
        assert metadata["head_drift_exceeded"] is False, (
            f"Expected 1-commit drift to remain within opt-out policy, got {metadata!r}"
        )
        assert metadata["routing_safe"] is False, (
            f"Expected mixed-commit opt-out artifact to stay non-routing-safe, got {metadata!r}"
        )
        assert metadata["provisional_reason"] == "head_drift", (
            f"Expected head_drift provisional reason for opt-out run, got {metadata!r}"
        )

    def test_partial_run_unknown_drift_fails_closed(self, monkeypatch, tmp_path, capsys):
        output_path = self._patch_quick_run(
            monkeypatch,
            tmp_path,
            ["--filter", "bug/"],
            drift=None,
        )
        exit_code = harness.main()
        captured = capsys.readouterr()
        metadata = json.loads(output_path.read_text())["metadata"]

        assert exit_code == harness.HEAD_DRIFT_POLICY_EXIT_CODE, (
            "Expected partial run with unknown drift to fail closed until zero drift is confirmed, "
            f"got {exit_code!r}"
        )
        assert "Unable to evaluate HEAD drift" in captured.out, (
            f"Expected explicit unknown-drift warning output, got {captured.out!r}"
        )
        assert metadata["head_drift_max_commits"] == 0, (
            f"Expected partial run to retain zero-drift threshold metadata, got {metadata!r}"
        )
        assert metadata["routing_safe"] is False, (
            f"Expected unknown-drift partial artifact to stay non-routing-safe, got {metadata!r}"
        )
        assert metadata["provisional_reason"] == "head_drift_unavailable", (
            f"Expected head_drift_unavailable provisional reason, got {metadata!r}"
        )

    def test_partial_run_allow_head_drift_keeps_unknown_drift_provisional(
        self, monkeypatch, tmp_path, capsys
    ):
        output_path = self._patch_quick_run(
            monkeypatch,
            tmp_path,
            ["--filter", "bug/", "--allow-head-drift"],
            drift=None,
        )
        exit_code = harness.main()
        captured = capsys.readouterr()
        metadata = json.loads(output_path.read_text())["metadata"]

        assert exit_code == 0, (
            f"Expected unknown-drift opt-out partial run to stay exploratory, got {exit_code!r}"
        )
        assert "[PROVISIONAL PARTIAL RUN]" in captured.out, (
            f"Expected provisional partial banner in output, got {captured.out!r}"
        )
        assert "Unable to evaluate HEAD drift" in captured.out, (
            f"Expected explicit unknown-drift warning output, got {captured.out!r}"
        )
        assert metadata["head_drift_max_commits"] == harness.HEAD_DRIFT_MAX_COMMITS_DEFAULT, (
            f"Expected opt-out partial run to retain default drift threshold metadata, got {metadata!r}"
        )
        assert metadata["routing_safe"] is False, (
            f"Expected unknown-drift opt-out artifact to stay non-routing-safe, got {metadata!r}"
        )
        assert metadata["provisional_reason"] == "head_drift_unavailable", (
            f"Expected head_drift_unavailable provisional reason, got {metadata!r}"
        )

    def test_partial_baseline_run_still_fails_closed_on_drift(
        self, monkeypatch, tmp_path, capsys
    ):
        output_path = self._patch_quick_run(
            monkeypatch,
            tmp_path,
            ["--filter", "bug/", "--baseline"],
            drift=1,
        )
        exit_code = harness.main()
        captured = capsys.readouterr()
        metadata = json.loads(output_path.read_text())["metadata"]

        assert exit_code == harness.HEAD_DRIFT_POLICY_EXIT_CODE, (
            "Expected partial baseline run to keep the zero-drift fail-closed policy, "
            f"got {exit_code!r}"
        )
        assert "[HEAD DRIFT WARNING]" in captured.out, (
            f"Expected partial baseline run to surface drift warning output, got {captured.out!r}"
        )
        assert metadata["head_drift_max_commits"] == 0, (
            f"Expected partial baseline run to keep zero-drift threshold metadata, got {metadata!r}"
        )
        assert metadata["routing_safe"] is False, (
            f"Expected drifted partial baseline artifact to stay non-routing-safe, got {metadata!r}"
        )
        assert metadata["provisional_reason"] == "head_drift", (
            f"Expected head_drift provisional reason for partial baseline run, got {metadata!r}"
        )

    def test_fail_on_head_drift_returns_policy_exit_code(self, monkeypatch, tmp_path):
        self._patch_quick_run(
            monkeypatch,
            tmp_path,
            ["--max-head-drift-commits", "5", "--fail-on-head-drift"],
            drift=6,
        )
        exit_code = harness.main()
        assert exit_code == harness.HEAD_DRIFT_POLICY_EXIT_CODE, (
            "Expected explicit head-drift failure policy to return policy exit code, "
            f"got exit code {exit_code}"
        )

    def test_baseline_mode_keeps_explicit_head_drift_fail_policy(
        self, monkeypatch, tmp_path
    ):
        self._patch_quick_run(
            monkeypatch,
            tmp_path,
            ["--baseline", "--max-head-drift-commits", "5", "--fail-on-head-drift"],
            drift=6,
        )
        exit_code = harness.main()
        assert exit_code == harness.HEAD_DRIFT_POLICY_EXIT_CODE, (
            "Expected baseline mode to honor explicit head-drift failure policy, "
            f"got exit code {exit_code}"
        )

    def test_negative_threshold_is_usage_error(self, monkeypatch, capsys):
        monkeypatch.setattr(sys, "argv", ["harness.py", "--max-head-drift-commits", "-1"])
        exit_code = harness.main()
        captured = capsys.readouterr()
        assert exit_code == 3
        assert "--max-head-drift-commits must be >= 0" in captured.err


# ---------------------------------------------------------------------------
# Cargo-lock contention detection (#1074)
# ---------------------------------------------------------------------------


class TestCargoLockContention:
    """Tests for cargo-lock contention detection and classification."""

    def test_has_cargo_lock_contention_positive(self):
        output = (
            "[cargo-lock] Waiting for build lock on trust-wp "
            "(held by slot 0: trust-wp (WORKER) [build])...\n"
            "error: could not compile `creusot_test`\n"
        )
        assert harness._has_cargo_lock_contention(output) is True

    def test_has_cargo_lock_contention_negative(self):
        output = "error[E0001]: something went wrong\ncould not compile `creusot_test`\n"
        assert harness._has_cargo_lock_contention(output) is False

    def test_classify_failure_contention_is_error_with_reason(self):
        """Cargo-lock contention should classify as error with skip_reason."""
        output = (
            "[cargo-lock] Waiting for build lock on trust-wp "
            "(held by slot 0: trust-wp (WORKER) [build])...\n"
            "error: could not compile `creusot_test`\n"
        )
        status, reason = harness.classify_failure(
            output=output,
            source="fn foo() {}",
        )
        assert status == "error"
        assert reason == "cargo-lock contention"

    def test_contention_does_not_mask_rustc_panic(self):
        """Rustc panic takes priority over cargo-lock contention."""
        output = (
            "[cargo-lock] Waiting for build lock on trust-wp "
            "(held by slot 0: trust-wp (WORKER))...\n"
            "thread 'rustc' panicked at something\n"
        )
        status, reason = harness.classify_failure(
            output=output,
            source="fn foo() {}",
        )
        assert status == "error"
        assert reason is None  # Panic error, not contention

    def test_contention_does_not_mask_unsupported_source(self):
        """Source-level unsupported features take priority over contention."""
        # Use `#[open]` as the unsupported feature — prophetic is supported (#2683).
        output = (
            "[cargo-lock] Waiting for build lock on trust-wp "
            "(held by slot 0: trust-wp (WORKER))...\n"
            "error: could not compile\n"
        )
        status, reason = harness.classify_failure(
            output=output,
            source="#[open]\nfn reflexive() {}",
        )
        assert status == "error", f"Expected unsupported source contention to be error, got {status!r}"
        assert reason is None, f"Expected no skip reason for unsupported source contention, got {reason!r}"

    def test_timeout_is_error_not_skip_for_logic_only_source(self):
        """Timeout infrastructure errors should not classify as logic-only skip."""
        status, reason = harness.classify_failure(
            output="Timeout after 60s",
            source="#[logic]\nfn lemma() -> bool { true }",
        )
        assert status == "error"
        assert reason == "timeout"

    def test_network_download_failure_is_error(self):
        """Crates.io download failures must classify as infrastructure errors."""
        output = (
            "error: failed to download from https://index.crates.io/config.json\n"
            "error: could not compile `creusot_test`\n"
        )
        status, reason = harness.classify_failure(
            output=output,
            source="fn foo() {}",
        )
        assert status == "error"
        assert reason == "network download failure"


class TestCouldNotCompileClassification:
    """Tests for #1960: could-not-compile should not mask verification results.

    trust-wp-rustc exits non-zero even for successful verification, causing cargo
    to emit "could not compile". The classifier must look at verification markers
    before treating this as an error.
    """

    def test_failed_marker_takes_priority_over_could_not_compile(self):
        """FAILED marker in output should classify as fail, not error."""
        output = (
            "trust-wp: f FAILED ✗\n"
            "  at src/lib.rs:5:1: 5:11\n"
            "trust-wp: 0 verified, 1 failed, 0 errors\n"
            "error: could not compile `creusot_test`\n"
        )
        status, _ = harness.classify_failure(output=output, source="fn f() {}")
        assert status == "fail", f"Expected 'fail' with FAILED marker, got {status!r}"

    def test_unknown_marker_takes_priority_over_could_not_compile(self):
        """Unknown verification result should classify as unknown, not error."""
        output = (
            "trust-wp: f unknown (loop call obligations: incomplete)\n"
            "  at src/lib.rs:5:1: 5:11\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
            "error: could not compile `creusot_test`\n"
        )
        status, _ = harness.classify_failure(output=output, source="fn f() {}")
        assert status == "unknown", f"Expected 'unknown' with unknown marker, got {status!r}"

    def test_verification_summary_prevents_error_from_could_not_compile(self):
        """All-pass verification with could-not-compile should classify as pass."""
        output = (
            "functions with contracts found count=2\n"
            "trust-wp: f verified ✓\n"
            "trust-wp: g verified ✓\n"
            "trust-wp: 2 verified, 0 failed, 0 errors\n"
            "error: could not compile `creusot_test`\n"
        )
        status, _ = harness.classify_failure(output=output, source="fn f() {}")
        assert status == "pass", f"Expected 'pass' for all-verified summary, got {status!r}"

    def test_genuine_compile_error_still_detected(self):
        """error[E codes without verification output should still be error."""
        output = (
            "error[E0433]: failed to resolve: use of undeclared type\n"
            "error: could not compile `creusot_test`\n"
        )
        status, _ = harness.classify_failure(output=output, source="fn f() {}")
        assert status == "error", f"Expected 'error' for genuine error[E, got {status!r}"

    def test_could_not_compile_without_verification_is_error(self):
        """could-not-compile with no verification output is a genuine error."""
        output = (
            "Checking creusot_test v0.1.0\n"
            "error: could not compile `creusot_test`\n"
        )
        status, _ = harness.classify_failure(output=output, source="fn f() {}")
        assert status == "error", f"Expected 'error' for could-not-compile only, got {status!r}"


class TestPanicExitStatusClassification:
    """A non-zero process result must dominate earlier verifier output."""

    @pytest.mark.parametrize("exit_code", [7, 101])
    def test_nonzero_exit_with_matching_all_pass_wire_is_error(self, exit_code):
        """Even matching telemetry may precede a later cargo/wrapper failure."""
        output = (
            "functions with contracts found count=1\n"
            "trust-wp: use_foo verified ✓\n"
            "trust-wp: 1 verified, 0 failed, 0 errors, 1 skipped\n"
            "error: could not compile `creusot_test`\n"
            f"process didn't exit successfully (exit status: {exit_code})\n"
            + _wire_line(base_exit_code=exit_code, verified=1)
        )
        status, _ = harness.classify_failure(
            output=output, source="fn use_foo() {}", exit_code=exit_code
        )
        assert status == "error"

    def test_arbitrary_nonzero_exit_with_summary_only_is_error(self):
        """Human success text cannot mask an unexplained outer process failure."""
        output = (
            "functions with contracts found count=1\n"
            "trust-wp: use_foo verified ✓\n"
            "trust-wp: 1 verified, 0 failed, 0 errors\n"
        )
        status, _ = harness.classify_failure(
            output=output, source="fn use_foo() {}", exit_code=7
        )
        assert status == "error"

    def test_nonzero_exit_rejects_mismatched_clean_wire(self):
        """A clean driver wire cannot hide a later cargo or wrapper failure."""
        output = (
            "functions with contracts found count=1\n"
            "trust-wp: use_foo verified ✓\n"
            "trust-wp: 1 verified, 0 failed, 0 errors\n"
            + _wire_line(base_exit_code=0, verified=1)
        )
        status, _ = harness.classify_failure(
            output=output, source="fn use_foo() {}", exit_code=7
        )
        assert status == "error"

    def test_exit_101_without_summary_is_error(self):
        """Exit code 101 without any verification summary is a real crash."""
        output = (
            "error: could not compile `creusot_test`\n"
            "process didn't exit successfully (exit status: 101)\n"
        )
        status, _ = harness.classify_failure(
            output=output, source="fn f() {}", exit_code=101
        )
        assert status == "error", f"Expected 'error' for exit 101 without summary, got {status!r}"

    def test_exit_101_with_failure_summary_is_error(self):
        """A verifier failure summary cannot override a process failure."""
        output = (
            "functions with contracts found count=1\n"
            "trust-wp: f FAILED ✗\n"
            "trust-wp: 0 verified, 1 failed, 0 errors\n"
            "process didn't exit successfully (exit status: 101)\n"
        )
        status, _ = harness.classify_failure(
            output=output, source="fn f() {}", exit_code=101
        )
        assert status == "error"

    def test_exit_101_with_unknown_result_is_error(self):
        """An unknown summary cannot override a process failure."""
        output = (
            "functions with contracts found count=1\n"
            "trust-wp: f unknown (incomplete)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
            "process didn't exit successfully (exit status: 101)\n"
        )
        status, _ = harness.classify_failure(
            output=output, source="fn f() {}", exit_code=101
        )
        assert status == "error"

    def test_exit_101_with_panic_text_and_no_summary_is_error(self):
        """Exit code 101 with explicit panic text and no summary is error."""
        output = (
            "thread 'rustc' panicked at 'internal error'\n"
            "process didn't exit successfully (exit status: 101)\n"
        )
        status, _ = harness.classify_failure(
            output=output, source="fn f() {}", exit_code=101
        )
        assert status == "error", f"Expected 'error' for panic with no summary, got {status!r}"


class TestAssumedAxiomOnlyClassification:
    """Tests for #1474: axiom-only assumed functions should count as non-verifiable."""

    def test_all_assumed_axiom_only_nonzero_exit_is_error(self):
        """Assumed axioms cannot override a failed verifier process."""
        output = (
            "functions with contracts found count=3\n"
            "trust-wp: map_spec assumed (axiom-only function: 1 universal postcondition(s) with trivial body)\n"
            "trust-wp: filter_spec assumed (axiom-only function: 1 universal postcondition(s) with trivial body)\n"
            "trust-wp: interval_spec assumed (axiom-only function: 1 universal postcondition(s) with trivial body)\n"
            "trust-wp: 0 verified, 0 failed, 0 errors, 3 assumed\n"
        )
        source = '#[ensures(result == true)]\nfn map_spec() -> bool { true }'
        status, _ = harness.classify_failure(output=output, source=source, exit_code=1)
        assert status == "error", (
            f"Expected 'error' for nonzero all-assumed run, got {status!r}"
        )

    def test_mixed_assumed_and_verified_counts_correctly(self):
        """Mixed positive counts cannot override a failed verifier process."""
        output = (
            "functions with contracts found count=2\n"
            "trust-wp: f assumed (axiom-only function: 1 universal postcondition(s) with trivial body)\n"
            "trust-wp: g verified ✓\n"
            "trust-wp: 1 verified, 0 failed, 0 errors, 1 assumed\n"
        )
        source = '#[ensures(true)]\nfn f() {}\n#[ensures(true)]\nfn g() {}'
        status, _ = harness.classify_failure(output=output, source=source, exit_code=1)
        assert status == "error"


# ---------------------------------------------------------------------------
# _invalidate_test_crate_cache (#1959)
# ---------------------------------------------------------------------------

harness_runner_spec = importlib.util.spec_from_file_location(
    "harness_runner", HARNESS_DIR / "harness_runner.py"
)
harness_runner = importlib.util.module_from_spec(harness_runner_spec)
sys.modules["harness_runner"] = harness_runner
harness_runner_spec.loader.exec_module(harness_runner)


class TestInvalidateTestCrateCache:
    """Tests for _invalidate_test_crate_cache (#1959)."""

    def test_removes_creusot_test_fingerprints(self, tmp_path):
        """Fingerprint dirs matching creusot_test-* are removed."""
        fp_dir = tmp_path / "debug" / ".fingerprint"
        fp_dir.mkdir(parents=True)
        (fp_dir / "creusot_test-abc123").mkdir()
        (fp_dir / "creusot_test-abc123" / "lib-creusot_test.json").write_text("{}")
        (fp_dir / "creusot_test-def456").mkdir()
        # Dependency fingerprints must survive
        (fp_dir / "trust-wp-abc123").mkdir()

        harness_runner._invalidate_test_crate_cache(tmp_path)

        assert not (fp_dir / "creusot_test-abc123").exists(), \
            "creusot_test-abc123 fingerprint should be removed"
        assert not (fp_dir / "creusot_test-def456").exists(), \
            "creusot_test-def456 fingerprint should be removed"
        assert (fp_dir / "trust-wp-abc123").exists(), \
            "trust-wp-abc123 fingerprint should be preserved"

    def test_removes_creusot_test_artifacts(self, tmp_path):
        """Compiled artifacts for creusot_test are removed from deps/."""
        deps_dir = tmp_path / "debug" / "deps"
        deps_dir.mkdir(parents=True)
        (deps_dir / "libcreusot_test-abc123.rmeta").write_text("")
        (deps_dir / "creusot_test-abc123.d").write_text("")
        # Dependency artifacts must survive
        (deps_dir / "libtrust_wp-abc123.rmeta").write_text("")

        harness_runner._invalidate_test_crate_cache(tmp_path)

        assert not (deps_dir / "libcreusot_test-abc123.rmeta").exists(), \
            "libcreusot_test rmeta should be removed"
        assert not (deps_dir / "creusot_test-abc123.d").exists(), \
            "creusot_test dep-info should be removed"
        assert (deps_dir / "libtrust_wp-abc123.rmeta").exists(), \
            "libtrust_wp rmeta should be preserved"

    def test_noop_on_empty_target(self, tmp_path):
        """No error when shared target has no debug/ dir yet."""
        harness_runner._invalidate_test_crate_cache(tmp_path)

    def test_noop_on_no_fingerprints(self, tmp_path):
        """No error when debug/.fingerprint/ exists but has no creusot_test entries."""
        fp_dir = tmp_path / "debug" / ".fingerprint"
        fp_dir.mkdir(parents=True)
        (fp_dir / "trust-wp-abc123").mkdir()

        harness_runner._invalidate_test_crate_cache(tmp_path)

        assert (fp_dir / "trust-wp-abc123").exists(), \
            "trust-wp-abc123 fingerprint should be preserved when no creusot_test entries exist"

    def test_removes_incremental_cache(self, tmp_path):
        """Incremental compilation dirs for creusot_test are removed (#2107)."""
        inc_dir = tmp_path / "debug" / "incremental"
        inc_dir.mkdir(parents=True)
        (inc_dir / "creusot_test-abc123").mkdir()
        (inc_dir / "creusot_test-abc123" / "s-abc-working").mkdir()
        # Dependency incremental dirs must survive
        (inc_dir / "trust-wp-abc123").mkdir()

        harness_runner._invalidate_test_crate_cache(tmp_path)

        assert not (inc_dir / "creusot_test-abc123").exists(), \
            "creusot_test incremental dir should be removed"
        assert (inc_dir / "trust-wp-abc123").exists(), \
            "trust-wp incremental dir should be preserved"

    def test_removes_build_script_output(self, tmp_path):
        """Build script output dirs for creusot_test are removed (#2107)."""
        build_dir = tmp_path / "debug" / "build"
        build_dir.mkdir(parents=True)
        (build_dir / "creusot_test-abc123").mkdir()
        (build_dir / "creusot_test-abc123" / "output").write_text("")
        # Dependency build dirs must survive
        (build_dir / "trust-wp-abc123").mkdir()

        harness_runner._invalidate_test_crate_cache(tmp_path)

        assert not (build_dir / "creusot_test-abc123").exists(), \
            "creusot_test build dir should be removed"
        assert (build_dir / "trust-wp-abc123").exists(), \
            "trust-wp build dir should be preserved"

    def test_removes_the_package_units_of_the_build_dir_layout(self, tmp_path):
        """Cargo's build-dir layout keeps a package's units in build/<package>/."""
        build_dir = tmp_path / "debug" / "build"
        unit = build_dir / "creusot_test" / "0123abcd"
        (unit / "fingerprint").mkdir(parents=True)
        (unit / "out").mkdir()
        (unit / "out" / "libcreusot_test-0123abcd.rlib").write_text("")
        dependency = build_dir / "trust-wp" / "4567ef01" / "out"
        dependency.mkdir(parents=True)

        harness_runner._invalidate_test_crate_cache(tmp_path)

        assert not (build_dir / "creusot_test").exists(), \
            "creusot_test's units should be removed"
        assert dependency.exists(), "trust-wp's units should be preserved"


class TestWarmupSharedTarget:
    """Tests for _warmup_shared_target runner orchestration."""

    def test_uses_dedicated_warmup_project(self, monkeypatch, tmp_path):
        workspace = tmp_path / "workspace"
        workspace.mkdir()
        shared_target = tmp_path / "shared_target"
        shared_target.mkdir()
        selected_test = tmp_path / "selected.rs"
        selected_test.write_text("fn selected_test_fixture() {}\n")
        warmup_dir = tmp_path / "warmup_dir"
        warmup_project = warmup_dir / "test_project"
        warmup_calls: list[tuple[Path, Path]] = []
        run_calls: list[tuple[list[str], Path]] = []
        removed_dirs: list[tuple[Path, bool]] = []

        def create_warmup_project(workspace_arg: Path, temp_dir_arg: Path) -> Path:
            warmup_calls.append((workspace_arg, temp_dir_arg))
            warmup_project.mkdir(parents=True, exist_ok=True)
            return warmup_project

        def create_test_project(*_args, **_kwargs) -> Path:
            raise AssertionError("warmup must not depend on the first selected test")

        class FakeSubprocess:
            TimeoutExpired = subprocess.TimeoutExpired

            @staticmethod
            def run(
                cmd: list[str],
                *,
                cwd: Path,
                capture_output: bool,
                text: bool,
                timeout: int,
                env: dict[str, str],
            ) -> subprocess.CompletedProcess[str]:
                run_calls.append((cmd, cwd))
                assert capture_output is True, (
                    f"Expected warmup subprocess to capture output, got {capture_output!r}"
                )
                assert text is True, (
                    f"Expected warmup subprocess text mode, got {text!r}"
                )
                assert timeout == 1200, (
                    f"Expected 1200s warmup timeout, got {timeout!r}"
                )
                assert env["CARGO_TARGET_DIR"] == str(shared_target), (
                    "Expected warmup subprocess to target the shared target dir, "
                    f"got {env['CARGO_TARGET_DIR']!r}"
                )
                assert env["AIT_ALLOW_LOCKLESS_CARGO"] == "1", (
                    "Expected lockless cargo bypass in warmup env, "
                    f"got {env['AIT_ALLOW_LOCKLESS_CARGO']!r}"
                )
                return subprocess.CompletedProcess(cmd, 0, "", "")

        monkeypatch.setattr(
            harness_runner.tempfile,
            "mkdtemp",
            lambda prefix: str(warmup_dir),
        )
        monkeypatch.setattr(
            harness_runner.shutil,
            "rmtree",
            lambda path, ignore_errors=False: removed_dirs.append((Path(path), ignore_errors)),
        )

        fake_harness = SimpleNamespace(
            create_test_project=create_test_project,
            create_warmup_project=create_warmup_project,
            subprocess=FakeSubprocess,
        )

        harness_runner._warmup_shared_target(
            fake_harness,
            workspace,
            [selected_test],
            shared_target,
            verbose=False,
        )

        assert warmup_calls == [(workspace, warmup_dir)], (
            f"Expected dedicated warmup project call, got {warmup_calls!r}"
        )
        assert run_calls == [
            (harness_targets.build_tool_argv("check", "--locked"), warmup_project)
        ], (
            f"Expected targo check in warmup project, got {run_calls!r}"
        )
        assert removed_dirs == [(warmup_dir, True)], (
            f"Expected warmup dir cleanup, got {removed_dirs!r}"
        )


# ---------------------------------------------------------------------------
# classify_error_category (#2690)
# ---------------------------------------------------------------------------


class TestDriverResultErrorCategory:
    """A Cargo trailer cannot erase a typed verifier outcome."""

    @pytest.mark.parametrize("counter", ["failed", "proof_assert_failed"])
    def test_driver_failure_is_not_rust_compilation_failure(self, counter):
        output = (
            "trust-wp: f FAILED (postcondition)\n"
            "error: could not compile `creusot_test` (lib)\n"
            + _wire_line(base_exit_code=1, **{counter: 1})
        )
        assert harness.classify_error_category(output, exit_code=1) == "verification"
        assert harness.classify_failure(output, "#[ensures(result)] fn f() {}", exit_code=1)[0] == "error"

    def test_driver_unknown_is_not_rust_compilation_failure(self):
        output = (
            "trust-wp: f unknown (proof-trusted)\n"
            "error: could not compile `creusot_test` (lib)\n"
            + _wire_line(base_exit_code=2, errors=1)
        )
        assert harness.classify_error_category(output, exit_code=2) == "unknown"

    @pytest.mark.parametrize("counter", ["parse_errors", "termination_errors", "logic_recursion_errors", "erasure_errors"])
    def test_frontend_driver_counter_stays_encoding(self, counter):
        output = "error: could not compile `creusot_test` (lib)\n" + _wire_line(
            base_exit_code=3, errors=1, **{counter: 1}
        )
        assert harness.classify_error_category(output, exit_code=1) == "encoding"

    @pytest.mark.parametrize("diagnostic", [
        "error: trust-wp: `old_x` is reserved; rename it",
        "error: ghost type escape: unread Ghost body",
    ])
    def test_rustc_rendered_frontend_refusal_is_not_compile(self, diagnostic):
        output = diagnostic + "\nerror: could not compile `creusot_test` (lib)\n" + _wire_line(base_exit_code=1)
        assert harness.classify_error_category(output, exit_code=1) == "encoding"
        assert harness.classify_failure(output, "fn f() {}", exit_code=1)[0] == "error"

    def test_actual_rust_error_code_wins_over_driver_counters(self):
        output = "error[E0382]: use of moved value\n" + _wire_line(base_exit_code=1, failed=1)
        assert harness.classify_error_category(output, exit_code=1) == "compile"

    def test_successful_driver_does_not_mask_later_cargo_failure(self):
        output = "error: could not compile `creusot_test` (lib)\n" + _wire_line(verified=1)
        assert harness.classify_error_category(output, exit_code=1) == "compile"
        assert harness.classify_failure(output, "#[ensures(result)] fn f() {}", exit_code=1)[0] == "error"

    def test_malformed_driver_record_cannot_override_compile_fallback(self):
        output = (
            "error: could not compile `creusot_test` (lib)\n"
            "TRUST_WP_RESULT:v1 base_exit_code=1 failed=1\n"
        )
        assert harness.classify_error_category(output, exit_code=1) == "compile"

    @pytest.mark.parametrize("diagnostic, wire", [
        ("trust-wp: f FAILED (postcondition)", _wire_line(base_exit_code=1, failed=1)),
        ("trust-wp: f unknown (proof-trusted)", _wire_line(base_exit_code=2, errors=1)),
        ("error: trust-wp: `old_x` is reserved; rename it", _wire_line(base_exit_code=1)),
        ("error: ghost type escape: unread Ghost body", _wire_line(base_exit_code=1)),
    ])
    def test_richer_category_cannot_grant_backend_superseded_credit(self, diagnostic, wire):
        output = diagnostic + "\nerror: could not compile `creusot_test` (lib)\n" + wire
        status, reason, credit = harness.classify_should_fail_result_with_credit(
            success=False,
            output=output,
            source="fn bad() {}",
            test_name="tests/should_fail/unsupported/char_pattern.rs",
            exit_code=1,
        )
        assert (status, reason, credit) == ("error", None, None)


class TestClassifyErrorCategory:
    """Tests for error sub-classification into specific failure categories."""

    def test_timeout_category(self):
        """Harness-level timeout output is classified as 'timeout'."""
        cat = harness.classify_error_category("Timeout after 120s\npartial output")
        assert cat == "timeout", f"expected 'timeout', got {cat!r}"

    def test_ay_panic_category(self):
        """Caught ay solver panics are classified as 'ay_panic'."""
        output = (
            "thread 'rustc' panicked at ay-dpll/src/api/terms.rs:407\n"
            "trust-wp: ay solver panic during verification: sort mismatch\n"
            "trust-wp: 1 verified, 0 failed, 0 errors\n"
        )
        cat = harness.classify_error_category(output)
        assert cat == "ay_panic", f"expected 'ay_panic', got {cat!r}"

    def test_caught_panic_category(self):
        """Per-function caught panics (#1975) are classified as 'caught_panic'."""
        output = (
            "trust-wp: nested_borrows panicked during verification: "
            "val_at: index 86 out of bounds\n"
            "trust-wp: 0 verified, 1 failed, 0 errors, 1 panicked\n"
        )
        cat = harness.classify_error_category(output)
        assert cat == "caught_panic", f"expected 'caught_panic', got {cat!r}"

    def test_driver_panic_via_rustc_thread(self):
        """Genuine rustc panics (no ay or caught marker) are 'driver_panic'."""
        output = (
            "thread 'rustc' panicked at 'index out of bounds'\n"
            "error: the compiler unexpectedly panicked. this is a bug.\n"
        )
        cat = harness.classify_error_category(output)
        assert cat == "driver_panic", f"expected 'driver_panic', got {cat!r}"

    def test_driver_panic_via_exit_status_101(self):
        """Exit status 101 with panic text is 'driver_panic'."""
        output = (
            "panicked at src/main.rs:42\n"
            "(exit status: 101)\n"
        )
        cat = harness.classify_error_category(output, exit_code=101)
        assert cat == "driver_panic", f"expected 'driver_panic', got {cat!r}"

    def test_obligations_dropped_category(self):
        """Dropped obligation warnings are classified as 'obligations_dropped'."""
        output = "trust-wp: 0 verified, 0 failed, 0 errors, 2 warnings (obligations dropped)\n"
        cat = harness.classify_error_category(output)
        assert cat == "obligations_dropped", f"expected 'obligations_dropped', got {cat!r}"

    def test_compile_error_category(self):
        """Rust compile errors are classified as 'compile'."""
        output = "error[E0308]: mismatched types\ntrust_wp: 0 verified, 0 failed, 0 errors\n"
        cat = harness.classify_error_category(output)
        assert cat == "compile", f"expected 'compile', got {cat!r}"

    def test_compile_error_via_cannot_find(self):
        """'cannot find' errors are classified as 'compile'."""
        output = "error: cannot find type `Foo` in this scope\n"
        cat = harness.classify_error_category(output)
        assert cat == "compile", f"expected 'compile', got {cat!r}"

    def test_encoding_error_category(self):
        """trust-wp encoding errors are classified as 'encoding'."""
        output = "trust-wp: error: sort conflict: variable '_x': declared as Int\n"
        cat = harness.classify_error_category(output)
        assert cat == "encoding", f"expected 'encoding', got {cat!r}"

    def test_compile_via_could_not_compile(self):
        """'could not compile' without error[E is classified as 'compile'."""
        output = "error: could not compile `creusot_test` (lib)\n"
        cat = harness.classify_error_category(output)
        assert cat == "compile", f"expected 'compile', got {cat!r}"

    def test_unknown_category_fallback(self):
        """Unrecognized error output falls through to 'unknown'."""
        output = "some unrecognized error\ntrust_wp: 0 verified, 0 failed, 0 errors\n"
        cat = harness.classify_error_category(output)
        assert cat == "unknown", f"expected 'unknown', got {cat!r}"

    def test_infrastructure_category(self):
        """Non-timeout infrastructure failures are classified as 'infrastructure'."""
        output = "error: failed to download from https://index.crates.io/config.json\n"
        cat = harness.classify_error_category(output)
        assert cat == "infrastructure", f"expected 'infrastructure', got {cat!r}"

    def test_caught_panic_takes_priority_over_compile(self):
        """When output has both caught panic and compile errors, caught_panic wins (#2690).

        The caught_panic check precedes compile error checks in the priority chain
        because a caught panic indicates the driver detected and handled an internal
        error — the compile error is a consequence, not the root cause.
        """
        output = (
            "trust-wp: foo panicked during verification: sort mismatch\n"
            "error[E0277]: the trait bound is not satisfied\n"
            "error: could not compile `creusot_test`\n"
        )
        cat = harness.classify_error_category(output)
        assert cat == "caught_panic", f"expected 'caught_panic', got {cat!r}"

    def test_ay_panic_takes_priority_over_caught_panic(self):
        """ay solver panic marker takes priority over generic caught panic.

        The ay_panic category is more specific: it means the ay solver itself
        panicked (sort mismatch, etc.), vs a generic encoding/driver panic.
        """
        output = (
            "trust-wp: ay solver panic during verification: sort mismatch\n"
            "trust-wp: foo panicked during verification: sort mismatch\n"
        )
        cat = harness.classify_error_category(output)
        assert cat == "ay_panic", f"expected 'ay_panic', got {cat!r}"

    def test_per_function_ay_panic_classified_as_ay_panic(self):
        """Per-function ay solver panics use the ay_panic category (#2687).

        After #2687, the driver prints "ay solver panic during verification"
        for ay-internal panics (prefetch OOB, sort mismatch, etc.) instead of
        the generic "panicked during verification:". This ensures ay panics
        get the ay_panic category regardless of whether they're caught at the
        trust-wp-ay level or the per-function boundary.
        """
        output = (
            "trust-wp: nested_borrows ay solver panic during verification: "
            "val_at: index 48 out of bounds for vals of length 22\n"
            "  (continuing with remaining functions)\n"
            "trust-wp: 0 verified, 1 failed, 0 errors, 1 panicked\n"
        )
        cat = harness.classify_error_category(output)
        assert cat == "ay_panic", f"expected 'ay_panic', got {cat!r}"

    def test_ay_panic_during_check_sat_phase(self):
        """Ay panic during check_sat phase is classified as ay_panic (#2690).

        The ay library itself emits ``ay solver panic during check_sat`` when
        it crashes inside the SAT loop (e.g., sort mismatch in mk_eq).
        Matching only the ``during verification`` variant lets a
        check_sat-phase panic fall through to caught_panic or driver_panic
        (the binary_search_list.rs shape).
        """
        output = (
            "thread 'rustc' panicked at 'sort mismatch'\n"
            "ay solver panic during check_sat: BUG: mk_eq expects same sort\n"
            "trust-wp: binary_search panicked during verification: invalid\n"
            "trust-wp: 0 verified, 1 failed, 0 errors, 1 panicked\n"
        )
        cat = harness.classify_error_category(output)
        assert cat == "ay_panic", (
            f"check_sat ay panic should take priority over caught_panic, got {cat!r}"
        )

    def test_ay_panic_during_loop_verification_phase(self):
        """Ay panic during loop verification is classified as ay_panic (#2690)."""
        output = (
            "trust-wp: ay solver panic during loop verification: sort fallback\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        cat = harness.classify_error_category(output)
        assert cat == "ay_panic", f"expected 'ay_panic', got {cat!r}"

    def test_ay_panic_during_proof_assert_phase(self):
        """Ay panic during proof_assert is classified as ay_panic (#2690)."""
        output = (
            "trust-wp: foo ay solver panic during proof_assert: bad sort\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        cat = harness.classify_error_category(output)
        assert cat == "ay_panic", f"expected 'ay_panic', got {cat!r}"

    def test_ay_solver_panicked_per_function_marker(self):
        """Per-function ``ay solver panicked:`` marker is ay_panic (#2690).

        The solver tail emits ``ay solver panicked: <reason>`` inside a
        per-function unknown status line. This form has no ``during
        <phase>`` suffix but still signals a solver-internal crash.
        """
        output = (
            "thread 'rustc' panicked at 'sort mismatch'\n"
            "trust-wp: List::<T>::index unknown (ay solver panicked: BUG: mk_eq)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        cat = harness.classify_error_category(output)
        assert cat == "ay_panic", (
            f"'ay solver panicked' per-function marker should be ay_panic, got {cat!r}"
        )

    def test_ay_panic_suppresses_rustc_panic_detection(self):
        """Any ``ay solver panic during <phase>`` variant suppresses rustc panic (#2690).

        Prior to this fix ``_has_rustc_panic`` only suppressed on the
        ``during verification`` variant, meaning ay panics emitted during
        ``check_sat``, ``loop verification``, ``proof_assert``, or
        ``loop_entry_may_execute`` would trigger driver_panic
        misclassification when the default panic hook's ``thread 'rustc'
        panicked`` message was present in the output.
        """
        output_variants = [
            "ay solver panic during check_sat: BUG\n",
            "ay solver panic during loop verification: BUG\n",
            "ay solver panic during proof_assert: BUG\n",
            "ay solver panic in loop_entry_may_execute: BUG\n",
            "trust-wp: foo unknown (ay solver panicked: BUG)\n",
        ]
        for variant in output_variants:
            output = "thread 'rustc' panicked at 'sort mismatch'\n" + variant
            assert harness._has_rustc_panic(output) is False, (
                f"ay panic variant should suppress rustc panic detection: {variant!r}"
            )
            cat = harness.classify_error_category(output)
            assert cat == "ay_panic", (
                f"variant {variant!r} expected ay_panic, got {cat!r}"
            )


# ---------------------------------------------------------------------------
# classify_failure: caught per-function panics (#1975, #2690)
# ---------------------------------------------------------------------------


class TestCaughtPerFunctionPanic:
    """Tests for caught per-function panics being classified as error, not fail."""

    def test_caught_panic_classified_as_error_in_should_succeed(self):
        """Output with 'panicked during verification:' should be error, not fail (#2690)."""
        output = (
            "trust-wp: Found 3 functions with contracts:\n"
            "trust-wp: foo verified ✓\n"
            "trust-wp: bar panicked during verification: index out of bounds\n"
            "trust-wp: warning: 1 function(s) panicked during verification (#1975)\n"
            "trust-wp: 1 verified, 1 failed, 0 errors, 1 panicked\n"
        )
        status, reason = harness.classify_failure(
            output=output,
            source="#[requires(true)]\nfn foo() {}\nfn bar() {}\nfn baz() {}",
        )
        assert status == "error", (
            f"caught per-function panic should be 'error', got '{status}'"
        )

    def test_caught_panic_not_classified_as_rustc_crash(self):
        """'panicked during verification:' should suppress _has_rustc_panic (#2687)."""
        output = (
            "thread 'rustc' panicked at ay-dpll/src/api/terms.rs:407\n"
            "trust-wp: nested_borrows panicked during verification: val_at error\n"
            "trust-wp: 0 verified, 1 failed, 0 errors\n"
        )
        assert harness._has_rustc_panic(output) is False, (
            "caught per-function panic marker should suppress rustc panic detection"
        )

    def test_should_fail_caught_panic_is_error_not_pass(self):
        """In should_fail lane, caught panics are errors, not 'correctly rejected' (#2690)."""
        output = (
            "trust-wp: bad panicked during verification: index out of bounds\n"
            "trust-wp: 0 verified, 0 failed, 0 errors, 1 panicked\n"
        )
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=output,
            source="fn bad() {}",
        )
        # Caught panics are internal errors — they should not count as
        # "correctly rejected" (pass) in the should_fail lane.
        assert status == "error", (
            f"caught panic in should_fail lane should be 'error', got '{status}'"
        )

    def test_should_fail_false_accept_guard_with_verified_output(self):
        """Should-fail test with verified output and success=False still flagged (#2690).

        When reclassifying stored results, the success flag may be False (inferred
        from exit code) but the output shows clean verification. The false-accept
        guard catches this and returns 'fail' instead of 'pass'.
        """
        output = (
            "trust-wp: Found 1 functions with contracts:\n"
            "  bad\n"
            "trust-wp: bad verified ✓\n"
            "trust-wp: 1 verified, 0 failed, 0 errors\n"
        )
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=output,
            source="fn bad() {}",
        )
        assert status == "fail", (
            f"should-fail with verified output should be 'fail' (false-accept), got '{status}'"
        )

    def test_final_borrows_proof_assert_count_alone_is_unknown(self):
        """final_borrows.rs: a proof_assert failed COUNT is not a refutation.

        The driver counts unvalidated failures (no model check) in ``M failed``,
        so 0 function failures + 2 counted proof_assert failures with no
        validated diagnostic record is inconclusive (D-28).
        """
        output = (
            "trust-wp: 0 verified, 0 failed, 0 errors, 2 trusted\n"
            "trust-wp: proof_assert: 5 verified, 2 failed, 0 errors\n"
        )
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=output,
            source="fn foo() {}\nfn bar() {}",
            test_name="tests/should_fail/final_borrows.rs",
        )
        assert status == "unknown", status

    def test_validated_proof_assert_refutation_is_pass(self):
        """proof_assert failures backed by a validated model are a rejection."""
        output = (
            _diag_line("creusot_test::foo", "proof_assert")
            + "trust-wp: proof_assert in creusot_test::foo FAILED ✗\n"
            "trust-wp: 0 verified, 0 failed, 0 errors, 2 trusted\n"
            "trust-wp: proof_assert: 5 verified, 2 failed, 0 errors\n"
        )
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=output,
            source="fn foo() {}\nfn bar() {}",
            test_name="tests/should_fail/final_borrows.rs",
        )
        assert status == "pass", status


# ---------------------------------------------------------------------------
# Timeout-vs-unknown boundary (#2690)
# ---------------------------------------------------------------------------


class TestTimeoutCausedUnknownReclassification:
    """Tests for reclassifying timeout-caused solver unknowns as errors (#2690).

    When the solver returns Unknown due to a timeout (hard timeout, solver
    timeout, loop invariant timeout), the test should be classified as "error"
    with category "timeout" rather than "unknown".  This prevents timeout-caused
    results from inflating the genuine unknown count.
    """

    def test_hard_timeout_unknown_becomes_error(self):
        """Hard timeout expired + unknown (timeout) -> error/timeout."""
        output = (
            "hard timeout expired while waiting for solver result "
            "outer_timeout=120.1s remaining_timeout=120.099888541s\n"
            "trust-wp: fib_memo unknown (timeout)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        status, reason = harness.classify_failure(output, source="fn foo() {}")
        assert status == "error", (
            f"hard timeout unknown should be 'error', got '{status}'"
        )
        cat = harness.classify_error_category(output)
        assert cat == "timeout", (
            f"hard timeout unknown category should be 'timeout', got {cat!r}"
        )

    def test_solver_level_timeout_unknown_becomes_error(self):
        """Per-function 'unknown (timeout)' without hard timeout -> error/timeout."""
        output = (
            "trust-wp: fib_memo unknown (timeout)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        status, reason = harness.classify_failure(output, source="fn foo() {}")
        assert status == "error", (
            f"solver timeout unknown should be 'error', got '{status}'"
        )
        cat = harness.classify_error_category(output)
        assert cat == "timeout", (
            f"solver timeout unknown category should be 'timeout', got {cat!r}"
        )

    def test_loop_invariant_timeout_unknown_becomes_error(self):
        """Per-function 'unknown (loop invariant: timeout)' -> error/timeout."""
        output = (
            "trust-wp: test_invariant_move unknown (loop invariant: timeout)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        status, reason = harness.classify_failure(output, source="fn foo() {}")
        assert status == "error", (
            f"loop invariant timeout unknown should be 'error', got '{status}'"
        )
        cat = harness.classify_error_category(output)
        assert cat == "timeout", (
            f"loop invariant timeout category should be 'timeout', got {cat!r}"
        )

    def test_loop_call_timeout_unknown_becomes_error(self):
        """Per-function 'unknown (loop call obligations: timeout)' -> error/timeout."""
        output = (
            "trust-wp: resolves unknown (loop call obligations: timeout)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        status, reason = harness.classify_failure(output, source="fn foo() {}")
        assert status == "error", (
            f"loop call timeout unknown should be 'error', got '{status}'"
        )

    def test_incomplete_timeout_pattern(self):
        """Per-function 'incomplete (timeout)' -> error/timeout."""
        output = (
            "trust-wp: resolves loop invariant incomplete (timeout) "
            "-- continuing to postcondition verification\n"
            "hard timeout expired while waiting for solver result "
            "outer_timeout=19s remaining_timeout=19s\n"
            "trust-wp: resolves unknown (incomplete)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        status, reason = harness.classify_failure(output, source="fn foo() {}")
        assert status == "error", (
            f"incomplete (timeout) should be 'error', got '{status}'"
        )

    def test_genuine_incomplete_stays_unknown(self):
        """Non-timeout 'unknown (incomplete)' stays as 'unknown'."""
        output = (
            "trust-wp: f unknown (incomplete)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        status, reason = harness.classify_failure(output, source="fn foo() {}")
        assert status == "unknown", (
            f"genuine incomplete should stay 'unknown', got '{status}'"
        )

    def test_quantifier_unhandled_stays_unknown(self):
        """Non-timeout 'unknown (quantifier-unhandled)' stays as 'unknown'."""
        output = (
            "trust-wp: ex unknown (quantifier-unhandled)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        status, reason = harness.classify_failure(output, source="fn foo() {}")
        assert status == "unknown", (
            f"quantifier-unhandled should stay 'unknown', got '{status}'"
        )

    def test_sort_mismatch_stays_unknown(self):
        """Non-timeout 'unknown (Ite branch sort mismatch: ...)' stays 'unknown'."""
        output = (
            "trust-wp: try_option unknown "
            "(Ite branch sort mismatch: then=Uninterpreted(\"Option\"))\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        status, reason = harness.classify_failure(output, source="fn foo() {}")
        assert status == "unknown", (
            f"sort mismatch should stay 'unknown', got '{status}'"
        )

    def test_mixed_timeout_and_non_timeout_becomes_error(self):
        """When output has both timeout and non-timeout unknowns, timeout wins.

        This is the conservative choice: if ANY function timed out, the overall
        result is timeout-affected and should be classified as error/timeout
        rather than unknown.
        """
        output = (
            "trust-wp: f1 unknown (incomplete)\n"
            "trust-wp: f2 unknown (timeout)\n"
            "trust-wp: 0 verified, 0 failed, 2 errors\n"
        )
        status, reason = harness.classify_failure(
            output, source="fn f1() {}\nfn f2() {}"
        )
        assert status == "error", (
            f"mixed timeout/incomplete should be 'error', got '{status}'"
        )
        cat = harness.classify_error_category(output)
        assert cat == "timeout", (
            f"mixed timeout/incomplete category should be 'timeout', got {cat!r}"
        )

    def test_fail_takes_priority_over_timeout(self):
        """When output has failed > 0, classify as fail even with timeout markers."""
        output = (
            "trust-wp: f1 FAILED\n"
            "hard timeout expired\n"
            "trust-wp: 1 verified, 1 failed, 0 errors\n"
        )
        status, reason = harness.classify_failure(
            output, source="#[requires(true)]\nfn f1() {}"
        )
        assert status == "fail", (
            f"fail should take priority over timeout, got '{status}'"
        )

    def test_harness_timeout_still_error_timeout(self):
        """Harness-level 'Timeout after 120s' remains error/timeout (unchanged)."""
        output = "Timeout after 120s\npartial output"
        cat = harness.classify_error_category(output)
        assert cat == "timeout", (
            f"harness timeout should still be 'timeout', got {cat!r}"
        )

    def test_has_timeout_caused_errors_false_for_no_timeout(self):
        """_has_timeout_caused_errors returns False when no timeout markers present."""
        output = (
            "trust-wp: f unknown (incomplete)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        assert harness._has_timeout_caused_errors(output) is False, (
            "expected False for non-timeout unknown output"
        )

    def test_has_timeout_caused_errors_true_for_hard_timeout(self):
        """_has_timeout_caused_errors detects hard timeout in output."""
        output = (
            "hard timeout expired while waiting for solver result\n"
            "trust-wp: f unknown (incomplete)\n"
        )
        assert harness._has_timeout_caused_errors(output) is True, (
            "expected True when hard timeout expired is in output"
        )

    def test_has_timeout_caused_errors_true_for_per_function_timeout(self):
        """_has_timeout_caused_errors detects per-function timeout reason."""
        output = "trust-wp: fib_memo unknown (timeout)\n"
        assert harness._has_timeout_caused_errors(output) is True, (
            "expected True for per-function unknown (timeout)"
        )

    def test_has_timeout_caused_errors_true_for_loop_timeout(self):
        """_has_timeout_caused_errors detects loop invariant timeout."""
        output = "trust-wp: test unknown (loop invariant: timeout)\n"
        assert harness._has_timeout_caused_errors(output) is True, (
            "expected True for loop invariant timeout"
        )

    def test_has_timeout_caused_errors_true_for_quantifier_round_limit(self):
        """_has_timeout_caused_errors detects quantifier-round-limit as timeout-adjacent.

        The solver exhausted its quantifier instantiation budget, which is a
        resource limit analogous to a timeout (#2690).
        """
        output = "trust-wp: m unknown (loop call obligations: quantifier-round-limit)\n"
        assert harness._has_timeout_caused_errors(output) is True, (
            "expected True for quantifier-round-limit"
        )

    def test_classify_error_category_solver_timeout(self):
        """classify_error_category returns 'timeout' for solver-level timeouts.

        Solver-level timeouts (#2690) must not fall through to 'unknown'.
        """
        output = (
            "trust-wp: fib_memo unknown (timeout)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        cat = harness.classify_error_category(output)
        assert cat == "timeout", (
            f"solver timeout should be 'timeout' category, got {cat!r}"
        )

    def test_classify_error_category_hard_timeout(self):
        """classify_error_category returns 'timeout' for hard timeout expired."""
        output = (
            "hard timeout expired while waiting for solver result\n"
            "trust-wp: f unknown (incomplete)\n"
        )
        cat = harness.classify_error_category(output)
        assert cat == "timeout", (
            f"hard timeout should be 'timeout' category, got {cat!r}"
        )


class TestGhostValidationErrorCategory:
    """Tests for the ghost_validation error category."""

    def test_ghost_validation_category(self):
        """Outputs with a ghost validation marker classify as ghost_validation."""
        from harness_classify import classify_error_category

        output = "trust-wp: ghost validation error(s) found\n"
        cat = classify_error_category(output)
        assert cat == "ghost_validation", (
            f"ghost validation marker should classify as 'ghost_validation', got {cat!r}"
        )

    def test_ghost_validation_with_lower_case(self):
        """Mixed-case ghost validation output still matches via lower-casing."""
        from harness_classify import classify_error_category

        output = "trust-wp: Ghost validation error(s) found\n"
        cat = classify_error_category(output)
        assert cat == "ghost_validation", (
            f"mixed-case ghost validation marker should classify as 'ghost_validation', got {cat!r}"
        )

    def test_ghost_validation_priority_below_timeout(self):
        """Timeout markers take priority over ghost validation markers."""
        from harness_classify import classify_error_category

        output = (
            "hard timeout expired while waiting for solver result\n"
            "trust-wp: ghost validation error(s) found\n"
        )
        cat = classify_error_category(output)
        assert cat == "timeout", (
            f"timeout should win over ghost validation, got {cat!r}"
        )

    def test_ghost_validation_priority_above_unknown(self):
        """Ghost validation output should not fall through to unknown."""
        from harness_classify import classify_error_category

        output = "trust-wp: ghost validation error(s) found in synthetic test\n"
        cat = classify_error_category(output)
        assert cat == "ghost_validation", (
            f"ghost validation output should classify before unknown fallback, got {cat!r}"
        )


class TestFalseAcceptDocumentation:
    """Tests for false-accept counting and documentation helpers."""

    def test_count_known_false_accepts_returns_int(self):
        """The false-accept counter returns a non-negative integer."""
        from harness_classify import count_known_false_accepts

        count = count_known_false_accepts()
        assert isinstance(count, int), (
            f"false-accept count should be an int, got {type(count).__name__}"
        )
        assert count >= 0, f"false-accept count should be non-negative, got {count}"

    def test_get_false_accept_summary_returns_dict(self):
        """The false-accept summary helper returns a dict."""
        from harness_classify import get_false_accept_summary

        summary = get_false_accept_summary()
        assert isinstance(summary, dict), (
            f"false-accept summary should be a dict, got {type(summary).__name__}"
        )

    def test_false_accept_summary_excludes_resolved_snapshot_self_reference(self):
        """bug/436_2.rs is not a known false-accept."""
        from harness_classify import get_false_accept_summary

        summary = get_false_accept_summary()
        # bug/436_2.rs is caught by snapshot self-reference validation, so it
        # is not a known false accept.
        assert "tests/should_fail/bug/436_2.rs" not in summary, (
            "bug/436_2.rs should not appear in the false-accept summary"
        )

    def test_false_accept_count_matches_summary_length(self):
        """The false-accept count should match the summary size exactly."""
        from harness_classify import (
            count_known_false_accepts,
            get_false_accept_summary,
        )

        count = count_known_false_accepts()
        summary = get_false_accept_summary()
        assert count == len(summary), (
            f"false-accept count {count} should match summary length {len(summary)}"
        )

    def test_false_accept_summary_is_copy(self):
        """Mutating a returned summary should not affect later calls."""
        from harness_classify import get_false_accept_summary

        summary = get_false_accept_summary()
        summary["tests/should_fail/synthetic_false_accept.rs"] = "synthetic mutation"
        fresh_summary = get_false_accept_summary()
        assert "tests/should_fail/synthetic_false_accept.rs" not in fresh_summary, (
            "get_false_accept_summary should return a copy, not the original dict"
        )


class TestResidualSummary:
    """Tests for get_residual_summary() structured residual reporting (#2686)."""

    def test_residual_summary_returns_dict_of_dicts(self):
        """The residual summary returns a dict with category keys."""
        from harness_classify import get_residual_summary

        summary = get_residual_summary()
        assert isinstance(summary, dict), (
            f"residual summary should be a dict, got {type(summary).__name__}"
        )
        expected_keys = {"false_accept", "api_divergence", "spec_infrastructure", "backend_superseded"}
        assert set(summary.keys()) == expected_keys, (
            f"residual summary keys should be {expected_keys}, got {set(summary.keys())}"
        )

    def test_residual_summary_false_accept_matches_known(self):
        """The false_accept category should contain exactly the known false-accepts."""
        from harness_classify import get_residual_summary, count_known_false_accepts

        summary = get_residual_summary()
        assert len(summary["false_accept"]) == count_known_false_accepts(), (
            f"false_accept count {len(summary['false_accept'])} should match "
            f"known count {count_known_false_accepts()}"
        )

    def test_residual_summary_api_divergence_count(self):
        """The api_divergence category should be empty (all moved to backend-superseded)."""
        from harness_classify import get_residual_summary

        summary = get_residual_summary()
        assert len(summary["api_divergence"]) == 0, (
            f"expected 0 API divergence entries, got {len(summary['api_divergence'])}"
        )

    def test_residual_summary_spec_infrastructure_count(self):
        """The spec_infrastructure category should be empty."""
        from harness_classify import get_residual_summary

        summary = get_residual_summary()
        assert len(summary["spec_infrastructure"]) == 0, (
            f"expected 0 spec infrastructure entries, got {len(summary['spec_infrastructure'])}"
        )

    def test_residual_summary_backend_superseded_matches_known(self):
        """The backend_superseded category should match count_backend_superseded."""
        from harness_classify import get_residual_summary, count_backend_superseded

        summary = get_residual_summary()
        assert len(summary["backend_superseded"]) == count_backend_superseded(), (
            f"backend_superseded count {len(summary['backend_superseded'])} should match "
            f"known count {count_backend_superseded()}"
        )

    def test_r4_false_accept_ledger_is_exact_and_other_residuals_are_empty(self):
        """The R4 false-accept ledger is EMPTY: the baseline-20260706 rows are
        caught (int-shift-full by the shift-amount-in-range obligation;
        impl_arg, trait_where and trait_where_supertrait by the illegal-
        recursive-trait bound check; trait_impl_where by self-named
        self-dispatch callgraph threading). The exact ratchet stays so any
        future false-accept must be ledgered explicitly, never silently."""
        from harness_classify import get_residual_summary

        summary = get_residual_summary()
        assert set(summary["false_accept"]) == set(), (
            "the R4 false-accept ledger changed without updating its exact "
            f"ratchet: {set(summary['false_accept'])!r}"
        )
        assert summary["api_divergence"] == {}
        assert summary["spec_infrastructure"] == {}


class TestClassifyErrorCategoryGhostValidation:
    """Additional coverage for ghost_validation classification."""

    def test_ghost_validation_without_other_markers(self):
        """A standalone ghost validation marker should classify as ghost_validation."""
        from harness_classify import classify_error_category

        output = "trust-wp: ghost validation error(s) found\n"
        cat = classify_error_category(output)
        assert cat == "ghost_validation", (
            f"standalone ghost validation output should classify as 'ghost_validation', got {cat!r}"
        )

    def test_compile_error_takes_priority_over_ghost(self):
        """Compile markers should take priority over ghost validation markers."""
        from harness_classify import classify_error_category

        output = (
            "error[E0001]: synthetic compile error\n"
            "trust-wp: ghost validation error(s) found\n"
        )
        cat = classify_error_category(output)
        assert cat == "compile", (
            f"compile error should win over ghost validation, got {cat!r}"
        )


class TestClassifyUnknownCategory:
    """Tests for classify_unknown_category sub-classification of unknown results (#2690)."""

    def test_incomplete_category(self):
        """Per-function 'unknown (incomplete)' maps to 'incomplete' category."""
        from harness_classify import classify_unknown_category

        output = (
            "trust-wp: pair_bor_mut unknown (incomplete)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        cat = classify_unknown_category(output)
        assert cat == "incomplete", (
            f"expected 'incomplete' category, got {cat!r}"
        )

    def test_quantifier_unhandled_category(self):
        """Per-function 'unknown (quantifier-unhandled)' maps correctly."""
        from harness_classify import classify_unknown_category

        output = (
            "trust-wp: ex unknown (quantifier-unhandled)\n"
            "trust-wp: u2 verified\n"
            "trust-wp: 1 verified, 0 failed, 1 errors\n"
        )
        cat = classify_unknown_category(output)
        assert cat == "quantifier_unhandled", (
            f"expected 'quantifier_unhandled' category, got {cat!r}"
        )

    def test_quantifier_cegqi_category(self):
        """Per-function 'unknown (quantifier-cegqi-incomplete)' maps correctly."""
        from harness_classify import classify_unknown_category

        output = (
            "trust-wp: splits_up unknown (quantifier-cegqi-incomplete)\n"
            "trust-wp: 0 verified, 0 failed, 1 errors\n"
        )
        cat = classify_unknown_category(output)
        assert cat == "quantifier_cegqi", (
            f"expected 'quantifier_cegqi' category, got {cat!r}"
        )

    def test_demoted_category(self):
        """Per-function 'unknown (demoted: ...)' maps to 'demoted' category."""
        from harness_classify import classify_unknown_category

        output = (
            "trust-wp: CellInv::<T>::read unknown (demoted: encoding approximations may affect soundness: sort_fallback_to_int_from_logic_fn(1))\n"
            "trust-wp: CellInv::<T>::write unknown (demoted: encoding approximations may affect soundness: sort_fallback_to_int_from_logic_fn(1))\n"
            "trust-wp: 0 verified, 0 failed, 2 errors, 2 skipped, 2 demoted\n"
        )
        cat = classify_unknown_category(output)
        assert cat == "demoted", (
            f"expected 'demoted' category, got {cat!r}"
        )

    def test_demoted_takes_priority_over_incomplete(self):
        """When both demoted and incomplete signals exist, demoted wins."""
        from harness_classify import classify_unknown_category

        output = (
            "trust-wp: u8::test_mul unknown (incomplete)\n"
            "trust-wp: u8::test_from_bool unknown (demoted: encoding approximations may affect soundness: integer_cast_identity(2))\n"
            "trust-wp: 0 verified, 0 failed, 2 errors\n"
        )
        cat = classify_unknown_category(output)
        assert cat == "demoted", (
            f"demoted should take priority over incomplete, got {cat!r}"
        )

    def test_solver_unknown_fallback(self):
        """No recognized per-function unknown pattern falls back to solver_unknown."""
        from harness_classify import classify_unknown_category

        output = "trust-wp: 0 verified, 0 failed, 1 errors\n"
        cat = classify_unknown_category(output)
        assert cat == "solver_unknown", (
            f"expected 'solver_unknown' fallback, got {cat!r}"
        )

    def test_proof_assert_unknown_not_counted(self):
        """proof_assert unknown lines are ignored (secondary signals)."""
        from harness_classify import classify_unknown_category

        output = (
            "trust-wp: f verified\n"
            "trust-wp: proof_assert in creusot_test::f unknown (incomplete)\n"
            "trust-wp: 1 verified, 0 failed, 0 errors\n"
        )
        cat = classify_unknown_category(output)
        assert cat == "solver_unknown", (
            f"proof_assert unknown should be ignored, got {cat!r}"
        )

    def test_runner_classifies_unknown_category(self):
        """The runner's _classify_error_or_unknown_category handles unknown status."""
        from harness_runner import _classify_error_or_unknown_category

        class FakeHarness:
            def classify_error_category(self, output, exit_code=None):
                return "timeout"
            def classify_unknown_category(self, output):
                return "incomplete"

        h = FakeHarness()
        result_error = _classify_error_or_unknown_category(h, "error", "output", None)
        assert result_error == "timeout", (
            f"error status should delegate to classify_error_category, got {result_error!r}"
        )
        result_unknown = _classify_error_or_unknown_category(h, "unknown", "output", None)
        assert result_unknown == "incomplete", (
            f"unknown status should delegate to classify_unknown_category, got {result_unknown!r}"
        )
        result_fail = _classify_error_or_unknown_category(h, "fail", "output", None)
        assert result_fail is None, (
            f"fail status should return None, got {result_fail!r}"
        )
        result_pass = _classify_error_or_unknown_category(h, "pass", "output", None)
        assert result_pass is None, (
            f"pass status should return None, got {result_pass!r}"
        )


class TestFalseAcceptReclassification:
    """Tests for false-accept reclassification from skip to fail (#2690)."""

    def test_resolved_snapshot_self_reference_rejection_classified_as_pass(self):
        """bug/436_2.rs has a real snapshot self-reference rejection.

        generic_deref_ghost.rs and generic_deref_snap.rs are detected by
        check_ghost_type_escape (#2686) and classified as valid rejections
        ("pass"), so none of the three is a known false accept.
        """
        output = (
            "error: trust-wp: snapshot self-reference: type Bad contains Snapshot<&mut T>\n"
            + _wire_line(base_exit_code=2, errors=1)
        )
        status, reason = harness.classify_should_fail_result(
            success=False,
            output=output,
            source="struct Bad<'a, T>(Snapshot<&'a mut T>);",
            test_name="tests/should_fail/bug/436_2.rs",
            exit_code=2,
        )
        assert status == "pass", (
            f"Snapshot self-reference rejection should be 'pass', got {status!r}"
        )
        assert reason is None, (
            f"Snapshot self-reference rejection should not report a residual reason, got {reason!r}"
        )

    def test_resolved_snapshot_self_reference_clean_accept_still_fails(self):
        """Clean verification of bug/436_2.rs would still be a false accept."""
        status, reason = harness.classify_should_fail_result(
            success=True,
            output="verified \u2713",
            source="fn bad() {}",
            test_name="tests/should_fail/bug/436_2.rs",
        )
        assert status == "fail", (
            f"Cleanly accepted bug/436_2.rs should still be 'fail', got {status!r}"
        )
        assert reason is None, (
            f"Clean false accept should not report a skip reason, got {reason!r}"
        )

    def test_resolved_expected_divergence_no_longer_skipped(self):
        """Resolved expected-divergence tests are not skipped.

        bug/1544_2.rs and bug/603.rs are backend-superseded (#2686) —
        trust-wp-std deliberately does not gate standard Rust traits on spec
        traits. bug/1762.rs is rejected by trusted contract validation.
        """
        for test_name in [
            "tests/should_fail/bug/1762.rs",
        ]:
            status, _ = harness.classify_should_fail_result(
                success=True,
                output="verified \u2713",
                source="fn bad() {}",
                test_name=test_name,
            )
            assert status == "fail", (
                f"Cleanly accepted resolved divergence {test_name} should be 'fail', got {status!r}"
            )

    def test_backend_superseded_classified_as_pass(self):
        """Backend-superseded tests (including former API divergences) are 'pass'."""
        for test_name in [
            "tests/should_fail/bug/1544_2.rs",
            "tests/should_fail/bug/603.rs",
            "tests/should_fail/bug/1610-crash.rs",
        ]:
            status, _ = harness.classify_should_fail_result(
                success=True,
                output="verified \u2713",
                source="fn bad() {}",
                test_name=test_name,
            )
            assert status == "pass", (
                f"Backend-superseded {test_name} should be 'pass', got {status!r}"
            )

    def test_ghost_escape_classified_as_pass(self):
        """Ghost type escape errors are classified as valid rejections (pass)."""
        for test_name in [
            "tests/should_fail/generic_deref_ghost.rs",
            "tests/should_fail/generic_deref_snap.rs",
        ]:
            status, _ = harness.classify_should_fail_result(
                success=False,
                output="ghost type escape: function `deref` accepts Ghost/Snapshot parameter(s)",
                source="fn bad() {}",
                test_name=test_name,
            )
            assert status == "pass", (
                f"Ghost escape {test_name} should be 'pass', got {status!r}"
            )


class TestSummaryCategorySplit:
    """Tests for the error_categories/unknown_categories split in summaries (#2690)."""

    def test_summary_splits_error_and_unknown_categories(self):
        """_summarize_subset should split error_categories from unknown_categories."""
        from types import SimpleNamespace

        results = [
            SimpleNamespace(
                name="test_error", status="error", message="timeout",
                skip_reason=None, error_category="timeout",
                message_truncated=False, verification_tier="tier0",
            ),
            SimpleNamespace(
                name="test_unknown", status="unknown", message="incomplete",
                skip_reason=None, error_category="incomplete",
                message_truncated=False, verification_tier="tier0",
            ),
            SimpleNamespace(
                name="test_pass", status="pass", message="ok",
                skip_reason=None, error_category=None,
                message_truncated=False, verification_tier="tier2",
            ),
        ]
        summary = harness._summarize_subset(results)
        error_cats = summary.get("error_categories", {})
        unknown_cats = summary.get("unknown_categories", {})
        assert "timeout" in error_cats, (
            f"Expected 'timeout' in error_categories, got {error_cats}"
        )
        assert "incomplete" in unknown_cats, (
            f"Expected 'incomplete' in unknown_categories, got {unknown_cats}"
        )
        assert "incomplete" not in error_cats, (
            f"'incomplete' should not appear in error_categories (it is unknown)"
        )
        assert "timeout" not in unknown_cats, (
            f"'timeout' should not appear in unknown_categories (it is error)"
        )


# ---------------------------------------------------------------------------
# Caught-panic phase-variant classification (#2690)
# ---------------------------------------------------------------------------


class TestCaughtPanicPhaseVariants:
    """Regression tests for phase-qualified caught-panic detection (#2690).

    A literal ``panicked during verification:`` substring check misses the
    phase-qualified variants the driver emits for other code paths, e.g.:

    - ``panicked during proof_assert:`` — proof_assert driver catch
      (the ``mapping_test.rs`` shape)
    - ``panicked during loop verification:`` — loop body catch
    - ``panicked during check_sat:`` — check_sat wrapper catch

    Missed, they fall through the rustc panic path to ``driver_panic``
    instead of ``caught_panic``.  The regex-based ``_has_caught_panic_marker``
    helper recognizes every phase variant without colliding with ay's
    ``ay solver panic during <phase>`` form (different verb: ``panic`` vs
    ``panicked``).
    """

    def test_panicked_during_proof_assert_is_caught_panic(self):
        """Reproduces the mapping_test.rs proof_assert-phase panic (#2690)."""
        from harness_classify import classify_error_category

        output = (
            "thread 'rustc' panicked at internal assertion\n"
            "trust-wp: error: panicked during proof_assert: None was unwrapped\n"
            "error: exit status: 101\n"
        )
        result = classify_error_category(output, exit_code=101)
        assert result == "caught_panic", (
            f"Expected 'caught_panic' for proof_assert phase, got {result!r}"
        )

    def test_panicked_during_loop_verification_is_caught_panic(self):
        """Loop-body catch_unwind emission must classify as caught_panic."""
        from harness_classify import classify_error_category

        output = (
            "thread 'rustc' panicked at loop invariant failure\n"
            "trust-wp: error: panicked during loop verification: index out of range\n"
            "error: exit status: 101\n"
        )
        result = classify_error_category(output, exit_code=101)
        assert result == "caught_panic", (
            f"Expected 'caught_panic' for loop-verification phase, got {result!r}"
        )

    def test_panicked_during_check_sat_is_caught_panic(self):
        """check_sat wrapper catch must classify as caught_panic."""
        from harness_classify import classify_error_category

        output = (
            "thread 'rustc' panicked at solver callback\n"
            "trust-wp: error: panicked during check_sat: assertion failed\n"
            "error: exit status: 101\n"
        )
        result = classify_error_category(output, exit_code=101)
        assert result == "caught_panic", (
            f"Expected 'caught_panic' for check_sat phase, got {result!r}"
        )

    def test_caught_panic_marker_suppresses_rustc_panic_all_phases(self):
        """_has_rustc_panic must return False for every phase-qualified catch."""
        from harness_classify import _has_rustc_panic

        for phase in (
            "verification",
            "proof_assert",
            "loop verification",
            "check_sat",
            "setup",
            "postcondition",
        ):
            output = (
                f"thread 'rustc' panicked at internal failure\n"
                f"trust-wp: error: panicked during {phase}: something\n"
            )
            assert _has_rustc_panic(output) is False, (
                f"rustc panic should be suppressed when caught during {phase!r}"
            )

    def test_ay_panic_marker_takes_priority_over_caught_panic(self):
        """ay solver panics must win when both markers are present (#2690)."""
        from harness_classify import classify_error_category

        output = (
            "ay solver panic during check_sat: sort mismatch\n"
            "trust-wp: error: panicked during verification: wrapper surfaced solver panic\n"
            "error: exit status: 101\n"
        )
        result = classify_error_category(output, exit_code=101)
        assert result == "ay_panic", (
            f"ay_panic must take priority over caught_panic, got {result!r}"
        )

    def test_should_fail_caught_panic_proof_assert_is_error(self):
        """Should-fail lane must classify phase-qualified caught panic as error."""
        from harness_classify import classify_should_fail_result

        output = (
            "trust-wp: error: panicked during proof_assert: internal invariant violated\n"
            "error: exit status: 101\n"
        )
        status, reason = classify_should_fail_result(
            success=False,
            output=output,
            source="fn main() {}",
            test_name="tests/should_fail/bug/example.rs",
            exit_code=101,
        )
        assert status == "error", (
            "should_fail lane must not count caught panics as valid rejection; "
            f"got status={status!r} reason={reason!r}"
        )
        assert reason is None, (
            f"Expected reason=None for caught-panic error, got {reason!r}"
        )

    def test_has_caught_panic_marker_helper(self):
        """Direct test of the _has_caught_panic_marker helper."""
        from harness_classify import _has_caught_panic_marker

        for phase in (
            "verification",
            "proof_assert",
            "loop verification",
            "check_sat",
            "setup",
        ):
            output = f"trust-wp: error: panicked during {phase}: foo"
            assert _has_caught_panic_marker(output), (
                f"_has_caught_panic_marker should match phase {phase!r}; output={output!r}"
            )

    def test_has_caught_panic_marker_no_false_positives(self):
        """_has_caught_panic_marker must not match ay's panic-noun form."""
        from harness_classify import _has_caught_panic_marker

        # ay solver uses noun "panic", not past-tense "panicked"
        ay_check_sat = "ay solver panic during check_sat: sort mismatch"
        assert not _has_caught_panic_marker(ay_check_sat), (
            f"_has_caught_panic_marker must not match ay panic-noun form: {ay_check_sat!r}"
        )
        ay_verification = "ay solver panic during verification: foo"
        assert not _has_caught_panic_marker(ay_verification), (
            f"_has_caught_panic_marker must not match ay panic-noun form: {ay_verification!r}"
        )
        # No phase word after "during" must not match
        assert not _has_caught_panic_marker("panicked during "), (
            "Empty-phase text must not match caught-panic regex"
        )
        # Unrelated text must not match
        unrelated = "thread 'rustc' panicked at internal"
        assert not _has_caught_panic_marker(unrelated), (
            f"Unrelated panic text must not match: {unrelated!r}"
        )
        assert not _has_caught_panic_marker(""), (
            "Empty string must not match caught-panic regex"
        )


class TestNoReplayTelemetryClean:
    """Regression tests for the NO_REPLAY clean-telemetry pass-through.

    The strict gate must remain fail-closed when verification produced any
    failure, error, panic, or non-zero base_exit_code.  When the wire line
    shows a fully clean run (no failures, errors, panics, proof_assert
    issues, parse_errors, termination_errors, logic_recursion_errors, or
    erasure_errors, and base_exit_code == 0), the NO_REPLAY marker is
    permitted to pass as a parse-only success.
    """

    @staticmethod
    def _wire(**overrides) -> str:
        """Build a TRUST_WP_RESULT wire line with optional field overrides.

        All fields default to zero so the helper produces a fully clean wire
        line; pass keyword arguments to override individual counters.
        """
        # Mirror TELEMETRY_FIELD_NAMES order via VerificationTelemetry defaults.
        fields = {
            "base_exit_code": 0,
            "verified": 0,
            "failed": 0,
            "errors": 0,
            "warnings": 0,
            "assumed": 0,
            "trusted": 0,
            "skipped": 0,
            "verified_with_axiom_deps": 0,
            "unverified_axioms": 0,
            "vacuous": 0,
            "evidence_gaps": 0,
            "proof_assert_failed": 0,
            "proof_assert_errors": 0,
            "panics": 0,
            "demoted": 0,
            "parse_errors": 0,
            "termination_errors": 0,
            "logic_recursion_errors": 0,
            "erasure_errors": 0,
        }
        fields.update(overrides)
        kv = " ".join(f"{k}={v}" for k, v in fields.items())
        return f"TRUST_WP_RESULT:v1 {kv}"

    def test_clean_wire_line_that_verified_nothing_errors(self):
        """D-21: an all-zero clean wire line proves
        nothing, and off the translate-only allowlist it is not a credit."""
        from harness_classify import classify_no_replay_result

        output = "trust-wp: 0 verified, 0 failed, 0 errors\n" + self._wire()
        status, _reason = classify_no_replay_result(output, exit_code=0)
        assert status == "error"

    def test_verified_only_wire_line_passes(self):
        """verified>0 with no failures/errors/panics → pass."""
        from harness_classify import classify_no_replay_result

        output = "trust-wp: 3 verified, 0 failed, 0 errors\n" + self._wire(verified=3)
        status, reason = classify_no_replay_result(output, exit_code=0)
        assert status == "pass", (
            f"verified>0 with clean state should pass; got status={status!r}"
        )
        assert reason is None

    def test_trusted_only_wire_line_errors(self):
        """trusted>0 with base_exit_code=2 (soundness gap) → error."""
        from harness_classify import classify_no_replay_result

        output = "trust-wp: 0 verified, 0 failed, 0 errors, 1 trusted\n" + self._wire(
            trusted=1, base_exit_code=2
        )
        status, reason = classify_no_replay_result(output, exit_code=2)
        assert status == "error", (
            "trusted-only soundness gap must fail closed; "
            f"got status={status!r} reason={reason!r}"
        )

    def test_failed_wire_line_errors(self):
        """failed>0 → error regardless of exit code argument."""
        from harness_classify import classify_no_replay_result

        output = "trust-wp: 0 verified, 2 failed, 0 errors\n" + self._wire(
            failed=2, base_exit_code=1
        )
        status, _reason = classify_no_replay_result(output, exit_code=1)
        assert status == "error", (
            f"Verification failures must keep strict gate closed; got {status!r}"
        )

    def test_errors_wire_line_errors(self):
        """errors>0 → error."""
        from harness_classify import classify_no_replay_result

        output = "trust-wp: 0 verified, 0 failed, 1 errors\n" + self._wire(
            errors=1, base_exit_code=2
        )
        status, _reason = classify_no_replay_result(output, exit_code=2)
        assert status == "error", (
            f"Verification errors must keep strict gate closed; got {status!r}"
        )

    def test_panics_wire_line_errors(self):
        """panics>0 → error."""
        from harness_classify import classify_no_replay_result

        output = "trust-wp: 0 verified, 0 failed, 0 errors, 1 panicked\n" + self._wire(
            panics=1, base_exit_code=2
        )
        status, _reason = classify_no_replay_result(output, exit_code=2)
        assert status == "error", (
            f"Panics must keep strict gate closed; got {status!r}"
        )

    def test_proof_assert_failed_wire_line_errors(self):
        """proof_assert_failed>0 → error."""
        from harness_classify import classify_no_replay_result

        output = self._wire(proof_assert_failed=1, base_exit_code=1)
        status, _reason = classify_no_replay_result(output, exit_code=1)
        assert status == "error", (
            f"proof_assert_failed must keep strict gate closed; got {status!r}"
        )

    def test_nonzero_exit_argument_errors(self):
        """Non-zero exit_code argument → error even if wire line is clean."""
        from harness_classify import classify_no_replay_result

        output = self._wire()
        status, _reason = classify_no_replay_result(output, exit_code=1)
        assert status == "error", (
            "Non-zero exit_code from cargo must fail closed even with a "
            f"clean wire line; got {status!r}"
        )

    def test_no_wire_line_errors(self):
        """No TRUST_WP_RESULT line → error (cannot prove clean run)."""
        from harness_classify import classify_no_replay_result

        output = "trust-wp: nothing to verify\n"
        status, _reason = classify_no_replay_result(output, exit_code=0)
        assert status == "error", (
            "Without a wire line we cannot confirm clean telemetry; "
            f"got {status!r}"
        )

    def test_rustc_panic_takes_priority(self):
        """rustc panic surfaces as error even with a clean wire line."""
        from harness_classify import classify_no_replay_result

        output = "thread 'rustc' panicked at internal\n" + self._wire()
        status, _reason = classify_no_replay_result(output, exit_code=0)
        assert status == "error", (
            f"rustc panic must override clean telemetry; got {status!r}"
        )


class TestNoReplayTranslateOnlyAllowlistGenericFnBound:
    """Only a NO_REPLAY test with genuinely ZERO Creusot goals (bug/511) may pass
    translate-only on a zero-examined exit-2 run. Tests whose .coma carries a real
    goal (closures/03/04/05 `call requires` precondition_F, bug/387 and
    syntax/10_mutual_rec_types `UInt64.add` overflow) are NOT allowlisted: a
    counterexample or a zero-examined run is not a pass for them."""

    @staticmethod
    def _wire(**overrides) -> str:
        return TestNoReplayTelemetryClean._wire(**overrides)

    def test_counterexample_on_generic_call_goal_is_not_a_pass(self):
        from harness_classify import classify_no_replay_result

        output = self._wire(failed=1, base_exit_code=1)
        status, _ = classify_no_replay_result(
            output,
            exit_code=1,
            test_name="tests/should_succeed/closures/03_generic_bound.rs",
        )
        assert status != "pass"

    def test_zero_examined_exit_two_is_not_a_pass_for_goal_bearing_test(self):
        from harness_classify import classify_no_replay_result

        for name in (
            "tests/should_succeed/bug/387.rs",
            "tests/should_succeed/syntax/10_mutual_rec_types.rs",
            "tests/should_succeed/closures/05_map.rs",
        ):
            output = self._wire(base_exit_code=2)
            status, _ = classify_no_replay_result(output, exit_code=2, test_name=name)
            assert status != "pass", name

    def test_zero_examined_exit_two_passes_for_zero_goal_test(self):
        from harness_classify import classify_no_replay_result

        output = self._wire(base_exit_code=2)
        status, _ = classify_no_replay_result(
            output, exit_code=2, test_name="tests/should_succeed/bug/511.rs"
        )
        assert status == "pass"

    def test_zero_examined_exit_two_errors_when_not_allowlisted(self):
        from harness_classify import classify_no_replay_result

        output = self._wire(base_exit_code=2)
        status, _ = classify_no_replay_result(
            output, exit_code=2, test_name="tests/should_succeed/bug/5110.rs"
        )
        assert status == "error"

    def test_allowlisted_test_with_panic_still_errors(self):
        from harness_classify import classify_no_replay_result

        output = self._wire(panics=1, base_exit_code=2)
        status, _ = classify_no_replay_result(
            output, exit_code=2, test_name="tests/should_succeed/bug/511.rs"
        )
        assert status == "error"

    def test_allowlisted_test_without_wire_line_errors(self):
        from harness_classify import classify_no_replay_result

        status, _ = classify_no_replay_result(
            "error: could not compile", exit_code=101,
            test_name="tests/should_succeed/bug/511.rs",
        )
        assert status == "error"


# Real cargo-trust-wp output (probe crates run through the harness runner and
# normalized for storage): `lang/empty.rs` as-is, and the same source plus one
# item using the reserved `__trust_wp_spec_tc_` prefix, which the driver refuses
# before discovery. The two wire lines are identical; only the build output
# says that the second crate never compiled.
ZERO_GOAL_WIRE_LINE = (
    "TRUST_WP_RESULT:v1 base_exit_code=2 verified=0 failed=0 errors=0 warnings=0 "
    "assumed=0 trusted=0 skipped=0 verified_with_axiom_deps=0 unverified_axioms=0 "
    "vacuous=0 evidence_gaps=0 proof_assert_verified=0 proof_assert_inconclusive=0 "
    "verified_native_only=0 proof_assert_failed=0 proof_assert_errors=0 panics=0 "
    "demoted=0 parse_errors=0 termination_errors=0 logic_recursion_errors=0 "
    "erasure_errors=0\n"
)
ZERO_GOAL_CLEAN_OUTPUT = (
    "    Checking creusot_test v0.1.0 (<TMPDIR>/test_project)\n"
    "    Finished `dev` profile [unoptimized + debuginfo] target(s) in 1.07s\n"
    + ZERO_GOAL_WIRE_LINE
)
# traits/14_assoc_in_logic's real shape: its only item is `#[trusted] fn test`,
# which Creusot translates to nothing and trust-wp reports trusted (D-158).
ZERO_GOAL_SOURCE_TRUSTED_OUTPUT = (
    "    Checking creusot_test v0.1.0 (<TMPDIR>/test_project)\n"
    "trust-wp: test trusted (skipped)\n\n"
    "trust-wp: (1 trusted, skipped)\n"
    "trust-wp: 0 verified, 0 failed, 0 errors, 1 trusted\n"
    "    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.54s\n"
    + ZERO_GOAL_WIRE_LINE.replace(" trusted=0 ", " trusted=1 ")
)
ZERO_GOAL_SOURCE_TRUSTED_ROW = "tests/should_succeed/traits/14_assoc_in_logic.rs"
ZERO_GOAL_REFUSED_OUTPUT = (
    "    Checking creusot_test v0.1.0 (<TMPDIR>/test_project)\n"
    "error: trust-wp: the name prefix `__trust_wp_spec_tc_` is reserved for specification "
    "type-check helpers generated by trust-wp's contract macros (`__trust_wp_spec_tc_forged`)\n"
    " --> src/lib.rs:9:1\n"
    "  |\n"
    "9 | pub fn __trust_wp_spec_tc_forged() {}\n"
    "  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
    "\n"
    "error: could not compile `creusot_test` (lib) due to 1 previous error\n"
    + ZERO_GOAL_WIRE_LINE
)


class TestZeroGoalZeroExaminedExit:
    """A zero-examined run exits 2 (CLAUDE.md). The ordinary should_succeed lane
    credits it only when Creusot's .coma exists and carries no goal, and the
    build output shows the crate compiled."""

    @staticmethod
    def _wire(**overrides) -> str:
        # Real build output around the wire line: the predicate reads cargo's
        # `Finished` line, so a bare wire line is no longer a zero-examined run.
        return (
            "    Checking creusot_test v0.1.0 (<TMPDIR>/test_project)\n"
            "    Finished `dev` profile [unoptimized + debuginfo] target(s) in 1.07s\n"
            + TestNoReplayTelemetryClean._wire(**overrides)
        )

    def test_zero_goal_coma_passes(self):
        from harness_classify import classify_failure

        status, _ = classify_failure(
            self._wire(base_exit_code=2), "pub fn f() {}", exit_code=2,
            test_name="tests/should_succeed/lang/empty.rs",
        )
        assert status == "pass"

    def test_frontend_refusal_with_the_same_wire_line_errors(self):
        # The isolating twin of test_zero_goal_coma_passes, from the real
        # binary: a crate the driver refuses before discovery reports the SAME
        # all-zero exit-2 wire line; only the build output differs.
        from harness_classify import classify_failure

        clean, refused = ZERO_GOAL_CLEAN_OUTPUT, ZERO_GOAL_REFUSED_OUTPUT
        name = "tests/should_succeed/lang/empty.rs"
        assert clean.splitlines()[-1] == refused.splitlines()[-1]
        assert classify_failure(clean, "pub fn f() {}", exit_code=2, test_name=name)[0] == "pass"
        assert classify_failure(refused, "pub fn f() {}", exit_code=2, test_name=name)[0] == "error"

    def test_goal_bearing_coma_errors(self):
        from harness_classify import classify_failure

        status, _ = classify_failure(
            self._wire(base_exit_code=2), "pub fn f() {}", exit_code=2,
            test_name="tests/should_succeed/result/result.rs",
        )
        assert status == "error"

    def test_a_test_creusot_translated_to_nothing_passes(self):
        # bug/1438 has no .coma because Creusot's output for it is empty, and
        # its ui runner reads the absent file as that empty output (D-157).
        from harness_classify import classify_failure

        status, _ = classify_failure(
            self._wire(base_exit_code=2), "pub fn f() {}", exit_code=2,
            test_name="tests/should_succeed/bug/1438.rs",
        )
        assert status == "pass"

    def test_a_missing_coma_creusot_never_ran_errors(self):
        # The isolating twins of the pass above: the same run, for a test with
        # no .coma that Creusot's ui runner skips (`// UISKIP` header), and for
        # a name that is no corpus file. Neither is evidence of no goal.
        from harness_classify import classify_failure

        for name in (
            "tests/should_succeed/termination/custom_variant.rs",
            "tests/should_succeed/bug/no_such_test.rs",
        ):
            status, _ = classify_failure(
                self._wire(base_exit_code=2), "pub fn f() {}", exit_code=2, test_name=name,
            )
            assert status == "error", name

    def test_a_source_declared_trusted_item_may_be_all_the_run_names(self):
        # D-158: the same run passes when the source declares the item it
        # trusts, and errors when it does not or when the counter counts more
        # items than the run names.
        from harness_classify import classify_failure

        out = ZERO_GOAL_SOURCE_TRUSTED_OUTPUT
        declared = "#[trusted]\n#[ensures(true)]\npub fn test() {}\n"
        undeclared = "#[ensures(true)]\npub fn test() {}\n"
        name = ZERO_GOAL_SOURCE_TRUSTED_ROW
        assert classify_failure(out, declared, exit_code=2, test_name=name)[0] == "pass"
        assert classify_failure(out, undeclared, exit_code=2, test_name=name)[0] == "error"
        miscounted = out.replace(" trusted=1 ", " trusted=2 ")
        assert classify_failure(miscounted, declared, exit_code=2, test_name=name)[0] == "error"
        goals = "tests/should_succeed/result/result.rs"
        assert classify_failure(out, declared, exit_code=2, test_name=goals)[0] == "error"

    def test_any_nonzero_counter_errors(self):
        from harness_classify import classify_failure

        for key in ("warnings", "panics", "parse_errors", "demoted", "trusted"):
            status, _ = classify_failure(
                self._wire(base_exit_code=2, **{key: 1}), "pub fn f() {}",
                exit_code=2, test_name="tests/should_succeed/lang/empty.rs",
            )
            assert status == "error", key

    def test_process_exit_must_be_two(self):
        from harness_classify import classify_failure

        status, _ = classify_failure(
            self._wire(base_exit_code=2), "pub fn f() {}", exit_code=101,
            test_name="tests/should_succeed/lang/empty.rs",
        )
        assert status == "error"

    def test_goals_the_inventory_does_not_count_are_not_zero_goals(self):
        # The grant asks the gate's own oracle question (D-89). closures/01_basic
        # inventories as EMPTY, yet its .coma carries goals in called extspec
        # closures; the SAME all-zero exit-2 run passes only on lang/empty.
        from harness_classify import classify_failure

        gc = _load_goal_coverage()
        basic = "tests/should_succeed/closures/01_basic.rs"
        assert gc.goal_inventory(basic) == [] and gc.zero_goal_oracle_refusals(basic)
        for name, expected in (("tests/should_succeed/lang/empty.rs", "pass"), (basic, "error")):
            status, _ = classify_failure(
                self._wire(base_exit_code=2), "pub fn f() {}", exit_code=2, test_name=name
            )
            assert status == expected, name


class TestSiblingModuleCrateAttrs:
    """Sibling modules must not carry crate-root-only inner attributes.

    `_copy_sibling_modules` reuses the full source transform, which injects
    `#![register_tool(creusot)]` / `#![feature(proc_macro_hygiene)]` intended
    for lib.rs. In a non-root module rustc rejects them ("can only be used at
    the crate root"), which erred every `pub mod common;` fixture (all 19
    iterator examples and termination/loops + simple_recursion) before any
    verification ran.
    """

    def test_sibling_module_has_no_crate_root_attrs(self, tmp_path):
        import harness_project

        fixture_dir = tmp_path / "fixtures"
        fixture_dir.mkdir()
        (fixture_dir / "main_test.rs").write_text(
            "extern crate creusot_std;\npub mod common;\npub fn f() {}\n"
        )
        (fixture_dir / "common.rs").write_text(
            "use creusot_std::prelude::*;\npub trait Iterator {}\n"
        )
        src_dir = tmp_path / "src"
        src_dir.mkdir()

        harness_project._copy_sibling_modules(
            fixture_dir / "main_test.rs",
            src_dir,
            harness_project.transform_creusot_to_trust_wp,
        )

        copied = (src_dir / "common.rs").read_text()
        assert "#![register_tool" not in copied, (
            "crate-root-only #![register_tool] leaked into sibling module: "
            f"{copied!r}"
        )
        assert "#![feature(proc_macro_hygiene)]" not in copied, (
            "crate-root-only #![feature(proc_macro_hygiene)] leaked into "
            f"sibling module: {copied!r}"
        )
        assert "pub trait Iterator" in copied

    def test_lib_rs_transform_still_injects_crate_attrs(self):
        import harness_project

        transformed = harness_project.transform_creusot_to_trust_wp(
            "extern crate creusot_std;\npub fn f() {}\n"
        )
        assert "#![register_tool(creusot)]" in transformed
        assert "#![feature(proc_macro_hygiene)]" in transformed


class TestSoundnessGapOnlyExitProofAssertEvidence:
    """Wire-authenticated gap-only exits with proof_assert-only evidence.

    The carve-out cannot require wire `verified>0` alone: the driver never
    counts proof_assert verifications there, so a proof_assert-only crate
    with one trusted item (bug/negative_int_pats: 7/7 proof_asserts
    verified, trusted=1, exit 2) would hard-error despite a failure-free
    wire line. The carve-out also accepts a verified>0 proof_assert summary
    with zero failed/errored assertions.
    """

    @staticmethod
    def _wire(**overrides: int) -> str:
        telemetry = _complete_telemetry(**overrides)
        pairs = " ".join(f"{k}={v}" for k, v in telemetry.items())
        return f"TRUST_WP_RESULT:v1 {pairs}"

    def test_proof_assert_verified_with_trusted_gap_qualifies(self):
        from harness_classify_succeed import _is_soundness_gap_only_exit

        output = (
            "trust-wp: proof_assert: 7 verified, 0 failed, 0 errors\n"
            + self._wire(base_exit_code=2, trusted=1)
        )
        assert _is_soundness_gap_only_exit(output, 2), (
            "verified proof_asserts + trusted-only gap on a failure-free "
            "wire line must qualify as a gap-only exit"
        )

    def test_zero_proof_assert_verified_still_fails_closed(self):
        from harness_classify_succeed import _is_soundness_gap_only_exit

        output = (
            "trust-wp: proof_assert: 0 verified, 0 failed, 0 errors\n"
            + self._wire(base_exit_code=2, trusted=1)
        )
        assert not _is_soundness_gap_only_exit(output, 2), (
            "zero-proof runs must never qualify"
        )

    def test_missing_proof_assert_summary_fails_closed(self):
        from harness_classify_succeed import _is_soundness_gap_only_exit

        output = self._wire(base_exit_code=2, trusted=1)
        assert not _is_soundness_gap_only_exit(output, 2)

    def test_failed_proof_assert_summary_fails_closed(self):
        from harness_classify_succeed import _is_soundness_gap_only_exit

        output = (
            "trust-wp: proof_assert: 7 verified, 1 failed, 0 errors\n"
            + self._wire(base_exit_code=2, trusted=1)
        )
        assert not _is_soundness_gap_only_exit(output, 2)

    def test_wire_proof_assert_failure_counter_fails_closed(self):
        from harness_classify_succeed import _is_soundness_gap_only_exit

        output = (
            "trust-wp: proof_assert: 7 verified, 0 failed, 0 errors\n"
            + self._wire(base_exit_code=2, trusted=1, proof_assert_failed=1)
        )
        assert not _is_soundness_gap_only_exit(output, 2), (
            "a failure-bearing wire line must never qualify even when the "
            "summary line looks clean"
        )

    def test_function_contract_verified_path_unchanged(self):
        from harness_classify_succeed import _is_soundness_gap_only_exit

        output = self._wire(base_exit_code=2, verified=2, trusted=1)
        assert _is_soundness_gap_only_exit(output, 2)


# --- driver build-profile resolution (#142) ---------------------------------
# The build profile selects a *different verifier*, so it must never be
# implicit. cfg(debug_assertions) reaches into ay and changes the PUBLISHED
# VERDICT: on should_succeed/option.rs a debug driver publishes `sat` -- a
# refutation of a claim that is true -- where a release driver publishes
# `unknown`. Two runs differing only by profile are therefore incomparable,
# and a profile left implicit presents as a phantom pass-count regression.


def _profile_workspace(tmp_path, *, release: bool, debug: bool, companions: bool = False):
    for profile, present in (("release", release), ("debug", debug)):
        if present:
            d = tmp_path / "target" / profile
            d.mkdir(parents=True, exist_ok=True)
            (d / "trust-wp-rustc").write_text("#!/bin/sh\n")
            if companions:
                (d / "cargo-trust-wp").write_text("#!/bin/sh\n")
    return tmp_path


def test_profile_auto_prefers_release_when_present(monkeypatch, tmp_path):
    monkeypatch.delenv(harness_targets.HARNESS_PROFILE_ENV, raising=False)
    ws = _profile_workspace(tmp_path, release=True, debug=True)
    assert harness_targets.resolve_driver_profile(ws)[0] == "release"


def test_profile_auto_falls_back_to_debug(monkeypatch, tmp_path):
    monkeypatch.delenv(harness_targets.HARNESS_PROFILE_ENV, raising=False)
    ws = _profile_workspace(tmp_path, release=False, debug=True)
    assert harness_targets.resolve_driver_profile(ws)[0] == "debug"


def test_profile_explicit_pin_is_honoured(monkeypatch, tmp_path):
    monkeypatch.setenv(harness_targets.HARNESS_PROFILE_ENV, "debug")
    ws = _profile_workspace(tmp_path, release=True, debug=True)
    assert harness_targets.resolve_driver_profile(ws)[0] == "debug"


def test_profile_pin_fails_closed_when_binary_absent(monkeypatch, tmp_path):
    """Never silently substitute the other verifier -- that is the whole fix."""
    monkeypatch.setenv(harness_targets.HARNESS_PROFILE_ENV, "release")
    ws = _profile_workspace(tmp_path, release=False, debug=True)
    with pytest.raises(RuntimeError, match="Refusing to fall back"):
        harness_targets.resolve_driver_profile(ws)


def test_profile_unknown_value_is_refused_not_ignored(monkeypatch, tmp_path):
    monkeypatch.setenv(harness_targets.HARNESS_PROFILE_ENV, "fast")
    ws = _profile_workspace(tmp_path, release=True, debug=True)
    with pytest.raises(RuntimeError):
        harness_targets.resolve_driver_profile(ws)


# --- the pin must cover COMPANION binaries too -------------------------------
# If `resolve_driver_profile` pins only the driver while `cargo-trust-wp`
# resolves with a hardcoded `profile="debug"`, `TRUST_WP_HARNESS_PROFILE=release`
# produces a MIXED-profile run that reports itself as pinned. Two costs, both
# real: the env var's fail-closed promise is only half true, and the release
# lane carries an undeclared dependency on `target/debug` surviving. Pruning
# that directory during a pinned-release run -- a reasonable thing to do --
# then makes most tests error at 0ms with `missing cargo-trust-wp`, which
# reads exactly like a mass regression.


def test_pinned_profile_also_selects_the_companion_binary(monkeypatch, tmp_path):
    monkeypatch.setenv(harness_targets.HARNESS_PROFILE_ENV, "release")
    ws = _profile_workspace(tmp_path, release=True, debug=True, companions=True)
    resolved = harness_targets.resolve_harness_binary(ws, "cargo-trust-wp")
    assert resolved.parent.name == "release", (
        "a pinned run must not silently take its companion from the other profile"
    )


def test_companion_pin_fails_closed_when_absent(monkeypatch, tmp_path):
    """A debug companion is NOT a substitute for the release one that was pinned."""
    monkeypatch.setenv(harness_targets.HARNESS_PROFILE_ENV, "release")
    ws = _profile_workspace(tmp_path, release=True, debug=True, companions=False)
    (tmp_path / "target" / "debug" / "cargo-trust-wp").write_text("#!/bin/sh\n")
    with pytest.raises(RuntimeError, match="Refusing to fall back"):
        harness_targets.resolve_harness_binary(ws, "cargo-trust-wp")


def test_auto_keeps_the_historical_companion_profile(monkeypatch, tmp_path):
    """`auto` must not move: it exists to preserve previously measured numbers.

    Historically the companion always came from `target/debug`, even when the
    driver resolved to release. Making `auto` mirror the driver would be more
    coherent and would silently change which binaries every existing baseline
    was produced with -- so `auto` stays on debug and only an explicit pin moves.
    """
    monkeypatch.delenv(harness_targets.HARNESS_PROFILE_ENV, raising=False)
    ws = _profile_workspace(tmp_path, release=True, debug=True, companions=True)
    assert harness_targets.resolve_driver_profile(ws)[0] == "release"
    assert harness_targets.resolve_harness_binary(ws, "cargo-trust-wp").parent.name == "debug"


def test_prebuild_check_looks_at_the_pinned_profile(monkeypatch, tmp_path):
    """A debug-only build must still count as MISSING under a release pin.

    Otherwise the prebuild step reports everything present, skips the build the
    run actually needs, and the run then fails on a binary that was never built.
    """
    monkeypatch.setenv(harness_targets.HARNESS_PROFILE_ENV, "release")
    ws = _profile_workspace(tmp_path, release=False, debug=True, companions=True)
    missing = harness_targets._missing_harness_binaries(ws)
    assert [p.parent.name for p in missing] == ["release", "release"]
    assert {p.name for p in missing} == {"cargo-trust-wp", "trust-wp-rustc"}


def test_prebuild_check_does_not_raise_before_anything_is_built(monkeypatch, tmp_path):
    """Absent is the NORMAL pre-build state and must stay a build trigger."""
    monkeypatch.setenv(harness_targets.HARNESS_PROFILE_ENV, "release")
    ws = _profile_workspace(tmp_path, release=False, debug=False)
    assert len(harness_targets._missing_harness_binaries(ws)) == 2


# --- source-revision recording (#146) ---------------------------------------
# ay is an unpinned relative path dep (`../ay`): it can move several times a
# day under concurrent agents and silently invalidate a measurement unless the
# result artefact records which backend produced it. The source FINGERPRINT
# already hashes these roots -- that is how drift is detectable -- but a hash
# cannot say WHICH dependency moved, and that check only runs under
# skip-prebuild. These pin the human-readable record.


def test_source_revisions_include_path_dependencies(tmp_path):
    """The backend's sha must be recoverable from any run, not just its hash."""
    revisions = harness_targets.resolved_source_revisions(Path.cwd())
    assert "trust-wp" in revisions
    assert "ay" in revisions, "the ay path dep must be recorded, it moves independently"
    for name, rev in revisions.items():
        head = rev.split("-")[0]
        assert len(head) == 10 or head == "unknown", f"{name}: {rev!r}"



@pytest.mark.parametrize("dirty", [False, True])
@pytest.mark.parametrize("layout", ["checkout", "package", "dotdot"])
def test_source_revision_alias_keeps_the_physical_provider_head(tmp_path, monkeypatch, dirty, layout):
    workspace = tmp_path / "trust-wp"
    workspace.mkdir()
    (workspace / "crates" / "own").mkdir(parents=True)
    (tmp_path / "aa-local-link").symlink_to(workspace / "crates" / "own", target_is_directory=True)
    provider = tmp_path / "qualified-engine-checkout"
    (provider / "crates" / "ay-core").mkdir(parents=True)
    (provider / "crates" / "ay-dpll").mkdir()
    (tmp_path / "ay").symlink_to(provider, target_is_directory=True)
    (tmp_path / "ay-core-link").symlink_to(provider / "crates" / "ay-core", target_is_directory=True)
    (tmp_path / "ay-dpll-link").symlink_to(provider / "crates" / "ay-dpll", target_is_directory=True)
    paths = {
        "checkout": ("../ay/crates/ay-core", "../ay/crates/ay-dpll", "ay"),
        "package": ("../ay-core-link", "../ay-dpll-link", "ay-core-link"),
        "dotdot": ("../ay/crates/../crates/ay-core", "../ay/crates/../crates/ay-dpll", "ay"),
    }
    core_path, dpll_path, label = paths[layout]
    (workspace / "Cargo.toml").write_text(
        '[workspace.dependencies]\n'
        f'ay-core = {{ path = "{core_path}" }}\n'
        f'ay-dpll = {{ path = "{dpll_path}" }}\n'
        'own = { path = "../aa-local-link" }\n'
    )

    def git_root(path):
        physical = path.resolve()
        return provider if physical.is_relative_to(provider) else workspace

    def git_output(repo, *args):
        if args == ("rev-parse", "HEAD"):
            return (("b" if repo == provider else "a") * 40).encode()
        assert args == ("status", "--porcelain")
        return b" M src/lib.rs" if repo == provider and dirty else b""

    monkeypatch.setattr(harness_targets, "_git_root", git_root)
    monkeypatch.setattr(harness_targets, "_git_output", git_output)
    revisions = harness_targets.resolved_source_revisions(workspace)
    assert revisions == {"trust-wp": "a" * 10, label: "b" * 10 + ("-dirty" if dirty else "")}
    assert set(harness_targets._workspace_source_roots(workspace)) == {workspace, provider}


def test_source_revision_alias_collision_cannot_hide_a_physical_provider(tmp_path, monkeypatch):
    workspace = tmp_path / "trust-wp"
    workspace.mkdir()
    first = tmp_path / "first" / "ay"
    second = tmp_path / "second" / "ay"
    first.mkdir(parents=True)
    second.mkdir(parents=True)
    (workspace / "Cargo.toml").write_text(
        '[workspace.dependencies]\n'
        'first = { path = "../first/ay" }\n'
        'second = { path = "../second/ay" }\n'
    )
    monkeypatch.setattr(harness_targets, "_git_root", lambda path: path.resolve())
    with pytest.raises(RuntimeError, match="ambiguous source revision label"):
        harness_targets.resolved_source_revisions(workspace)


def test_source_revisions_flag_a_dirty_root():
    """A dirty root must be visibly dirty -- an uncommitted backend is not a sha."""
    revisions = harness_targets.resolved_source_revisions(Path.cwd())
    for rev in revisions.values():
        assert rev.endswith("-dirty") or "-" not in rev or rev.endswith("-unknown")


def test_provenance_payload_carries_source_revisions(monkeypatch, tmp_path):
    workspace = _seed_harness_provenance_workspace(monkeypatch, tmp_path)
    harness._write_harness_binary_provenance(workspace)
    payload = json.loads(
        harness_targets._harness_provenance_path(workspace).read_text(encoding="utf-8")
    )
    assert "source_revisions" in payload, (
        "provenance must record which revision of each source root built these "
        "binaries, so a moving path dep cannot go unnoticed"
    )
    assert isinstance(payload["source_revisions"], dict)


# ---------------------------------------------------------------------------
# should_fail rejection-evidence hardening, credited pass messages, the
# NO_REPLAY verified tier, and the final-gate policy.
# ---------------------------------------------------------------------------


def _load_compare_baselines():
    spec = importlib.util.spec_from_file_location(
        "compare_baselines_front_j", WORKSPACE_ROOT / "scripts" / "compare_baselines.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _sf(output: str, exit_code: int | None = 2, test_name: str = ""):
    return harness.classify_should_fail_result_with_credit(
        success=False,
        output=output,
        source="fn f() {}",
        test_name=test_name,
        exit_code=exit_code,
    )


class TestShouldFailH1Rules:
    """Every should_fail pass needs positive rejection evidence."""

    def test_timeout_only_run_is_error_not_rejection(self):
        output = (
            "trust-wp: unsound unknown (timeout)\n"
            "proof_assert: 0 verified, 0 failed, 1 errors\n"
            + _wire_line(proof_assert_errors=1, base_exit_code=2)
        )
        assert _sf(output) == ("error", None, None)

    def test_hard_timeout_is_error_not_rejection(self):
        output = "hard timeout expired\n" + _wire_line(errors=1, base_exit_code=2)
        assert _sf(output) == ("error", None, None)

    def test_proof_assert_errors_only_is_unknown(self):
        """``K errors`` counts Unknown/Assumed/encoding errors, not refutations."""
        output = (
            "proof_assert: 0 verified, 0 failed, 1 errors\n"
            + _wire_line(proof_assert_errors=1, base_exit_code=2)
        )
        status, _reason, credit = _sf(output)
        assert (status, credit) == ("unknown", None)

    def test_wire_proof_assert_errors_counter_alone_is_not_pass(self):
        output = _wire_line(proof_assert_errors=2, base_exit_code=2)
        status, _reason, credit = _sf(output)
        assert status != "pass" and credit is None

    def test_proof_assert_failed_count_alone_is_unknown(self):
        output = (
            "proof_assert: 1 verified, 2 failed, 1 errors\n"
            + _wire_line(proof_assert_failed=2, proof_assert_errors=1, base_exit_code=1)
        )
        assert _sf(output) == ("unknown", None, None)

    def test_validated_proof_assert_failure_is_credited(self):
        output = (
            _diag_line("creusot_test::f", "proof_assert")
            + "trust-wp: proof_assert in creusot_test::f FAILED ✗\n"
            "proof_assert: 1 verified, 2 failed, 1 errors\n"
            + _wire_line(proof_assert_failed=2, proof_assert_errors=1, base_exit_code=1)
        )
        assert _sf(output) == (
            "pass",
            None,
            "validated counterexample: creusot_test::f proof_assert",
        )

    def test_wire_failed_without_validated_record_is_unknown(self):
        output = "trust-wp: bad FAILED ✗\n" + _wire_line(failed=3, base_exit_code=1)
        assert _sf(output, exit_code=1) == ("unknown", None, None)

    def test_validated_wire_failure_is_credited(self):
        output = (
            _diag_line("bad", "function_contract")
            + "trust-wp: bad FAILED ✗\n"
            + _wire_line(failed=3, base_exit_code=1)
        )
        assert _sf(output, exit_code=1) == (
            "pass",
            None,
            "validated counterexample: bad function_contract",
        )

    @pytest.mark.parametrize(
        "ay_result,model_validated",
        [
            ("trust-wp-structural-provenance", "false"),
            ("sat", "false"),
            ("none", "unknown"),
            ("unknown", "false"),
        ],
    )
    def test_unvalidated_failed_diagnostic_is_unknown(self, ay_result, model_validated):
        """status=failed reason=counterexample without a validated model: the
        driver's structural-provenance / unvalidated-SAT / no-solver shortcuts
        and solver-limited Unknown promoted to Failed are not refutations."""
        output = (
            _diag_line(
                "bad", "function_contract", ay_result=ay_result,
                model_validated=model_validated,
            )
            + "trust-wp: bad FAILED ✗\n"
            + _wire_line(failed=1, base_exit_code=1)
        )
        assert _sf(output, exit_code=1) == ("unknown", None, None)

    def test_explicit_refutation_validated_field_is_credited(self):
        """Forward compatibility with the driver half of the verdict fix."""
        output = (
            _diag_line(
                "bad", "function_contract", ay_result="none",
                model_validated="unknown", refutation="validated",
            )
            + "trust-wp: bad FAILED ✗\n"
            + _wire_line(failed=1, base_exit_code=1)
        )
        assert _sf(output, exit_code=1)[0] == "pass"

    def test_validated_record_must_match_a_verdict_line(self):
        """A validated record for an obligation with no FAILED ✗ line is not
        the counted failure."""
        output = (
            _diag_line("other", "function_contract")
            + "trust-wp: bad FAILED ✗\n"
            + _wire_line(failed=1, base_exit_code=1)
        )
        assert _sf(output, exit_code=1) == ("unknown", None, None)

    def test_validated_record_must_match_its_counter(self):
        """A validated proof_assert record cannot credit a zero proof_assert
        failed count, and a function record cannot credit wire failed=0."""
        pa_uncounted = (
            _diag_line("creusot_test::f", "proof_assert")
            + "trust-wp: proof_assert in creusot_test::f FAILED ✗\n"
            + "trust-wp: bad FAILED ✗\n"
            + _wire_line(failed=1, base_exit_code=1)
        )
        assert _sf(pa_uncounted, exit_code=1) == ("unknown", None, None)
        fn_uncounted = (
            _diag_line("bad", "function_contract")
            + "trust-wp: bad FAILED ✗\n"
            + "proof_assert: 0 verified, 1 failed, 0 errors\n"
            + _wire_line(proof_assert_failed=1, base_exit_code=1)
        )
        assert _sf(fn_uncounted, exit_code=1) == ("unknown", None, None)

    def test_validated_record_kind_must_match_verdict_shape(self):
        """A proof_assert record does not match a function-contract verdict."""
        output = (
            _diag_line("bad", "proof_assert")
            + "trust-wp: bad FAILED ✗\n"
            + "proof_assert: 0 verified, 1 failed, 0 errors\n"
            + _wire_line(failed=1, proof_assert_failed=1, base_exit_code=1)
        )
        assert _sf(output, exit_code=1) == ("unknown", None, None)

    def test_obligation_qualified_def_paths_match(self):
        variant = (
            _diag_line("f::variant_decrease%5B1%5D", "recursive_variant")
            + "trust-wp: f FAILED ✗ (variant decrease)\n"
            + _wire_line(failed=1, base_exit_code=1)
        )
        assert _sf(variant, exit_code=1)[2] == (
            "validated counterexample: f::variant_decrease[1] recursive_variant"
        )
        refinement = (
            _diag_line(
                "%3C%28%29%20as%20Tr%3E::m::trait%20precondition%20implies%20impl%20precondition",
                "trait_refinement",
            )
            + "trust-wp: <() as Tr>::m trait refinement FAILED ✗\n"
            + _wire_line(failed=1, base_exit_code=1)
        )
        assert _sf(refinement, exit_code=1)[0] == "pass"

    def test_def_path_prefix_needs_a_path_boundary(self):
        output = (
            _diag_line("bad_other", "function_contract")
            + "trust-wp: bad FAILED ✗\n"
            + _wire_line(failed=1, base_exit_code=1)
        )
        assert _sf(output, exit_code=1) == ("unknown", None, None)

    def test_wire_failed_with_timeout_elsewhere_still_credited(self):
        """A validated counterexample is a refutation even if a sibling timed out."""
        output = (
            "trust-wp: good unknown (timeout)\n"
            + _diag_line("bad", "function_contract")
            + "trust-wp: bad FAILED ✗\n"
            + _wire_line(failed=1, errors=1, base_exit_code=1)
        )
        assert _sf(output, exit_code=1) == (
            "pass",
            None,
            "validated counterexample: bad function_contract",
        )

    def test_exit_101_without_compile_diag_or_marker_is_error(self):
        assert _sf("trust-wp: 0 verified, 0 failed, 0 errors\n", exit_code=101) == (
            "error",
            None,
            None,
        )

    def test_wire_base_exit_101_without_marker_is_error(self):
        assert _sf(_wire_line(base_exit_code=101), exit_code=None) == (
            "error",
            None,
            None,
        )

    def test_exit_101_solver_counter_cannot_credit_a_crash(self):
        output = "trust-wp: bad FAILED ✗\n" + _wire_line(failed=1, base_exit_code=101)
        assert _sf(output, exit_code=101) == ("error", None, None)

    def test_exit_101_with_frontend_marker_but_no_abort_line_is_error(self):
        # Without rustc's abort line a 101 is a crash shape; the marker text
        # printed before it is not rejection evidence.
        output = (
            "error: used the `#[trusted]` attribute\n"
            + _wire_line(base_exit_code=101)
        )
        assert _sf(output, exit_code=101) == ("error", None, None)

    def test_exit_101_with_panic_is_error_even_with_marker(self):
        output = (
            "error: used the `#[trusted]` attribute\n"
            "thread 'rustc' panicked at src/lib.rs:1:1\n"
        )
        assert _sf(output, exit_code=101) == ("error", None, None)

    def test_exit_101_compile_failure_goes_through_evidence_gates(self):
        output = (
            "error: trust-wp: termination check failed: `f` recursive without variant\n"
            "error: could not compile `test` (lib) due to 1 previous error\n"
        )
        assert _sf(output, exit_code=101) == (
            "pass",
            None,
            "termination check failed",
        )

    def test_counted_frontend_credit_carries_wire_counter(self):
        output = "error: logic recursion check failed: `g`\n" + _wire_line(
            logic_recursion_errors=2, base_exit_code=2
        )
        assert _sf(output) == (
            "pass",
            None,
            "logic recursion check failed (logic_recursion_errors=2)",
        )

    def test_compile_rejection_without_allowlist_is_error(self):
        output = (
            "error[E0499]: cannot borrow `x` as mutable more than once at a time\n"
            "error: could not compile `test` (lib) due to 1 previous error\n"
        )
        status, _reason, credit = _sf(output, exit_code=101, test_name="tests/should_fail/x.rs")
        assert status == "error" and credit is None

    def test_allowlisted_compile_rejection_names_its_code(self):
        output = (
            "error[E0499]: cannot borrow `x` as mutable more than once at a time\n"
            "error: could not compile `test` (lib) due to 1 previous error\n"
        )
        status, _reason, credit = _sf(
            output, exit_code=101, test_name="tests/should_fail/bad_borrow.rs"
        )
        assert status == "pass" and credit is not None and credit.startswith("compile: ")

    def test_backend_superseded_credit_names_reason(self):
        name = next(iter(harness._KNOWN_BACKEND_SUPERSEDED_TESTS))
        status, _reason, credit = _sf(
            "trust-wp: f verified ✓\n" + _wire_line(verified=1), exit_code=0, test_name=name
        )
        assert status == "pass" and credit.startswith("backend superseded: ")

    def test_wrapper_agrees_with_credited_classifier(self):
        output = (
            _diag_line("creusot_test::f", "proof_assert")
            + "trust-wp: proof_assert in creusot_test::f FAILED ✗\n"
            "proof_assert: 0 verified, 1 failed, 0 errors\n"
        )
        assert harness.classify_should_fail_result(
            False, output, "fn f() {}", exit_code=2
        ) == ("pass", None)

    def test_non_pass_never_carries_credit(self):
        for output in (
            "proof_assert: 0 verified, 0 failed, 1 errors\n",
            "hard timeout expired\n",
            "",
        ):
            status, _reason, credit = _sf(output)
            assert status != "pass" and credit is None


class TestShouldFailH4Messages:
    def test_rejection_pass_message_format(self):
        assert harness.rejection_pass_message("wire failed=2") == (
            "Correctly rejected (wire failed=2)"
        )
        assert harness.rejection_pass_message(None) == "Correctly rejected"

    def test_is_rejection_pass_message(self):
        assert harness.is_rejection_pass_message("Correctly rejected")
        assert harness.is_rejection_pass_message("Correctly rejected (frontend: x)")
        assert not harness.is_rejection_pass_message("Correctly rejectedX")
        assert not harness.is_rejection_pass_message(None)

    def test_runner_pass_message_names_crediting_gate(self, tmp_path):
        output = (
            _diag_line("bad", "function_contract")
            + "trust-wp: bad FAILED ✗\n"
            + _wire_line(failed=1, base_exit_code=1)
        )
        status, message, *_rest = harness_runner._classify_outcome(
            harness, tmp_path, "tests/should_fail/synthetic.rs", "fn f() {}",
            False, output, 1,
        )
        assert (status, message) == (
            "pass",
            "Correctly rejected (validated counterexample: bad function_contract)",
        )

    def test_runner_frontend_pass_message(self, tmp_path):
        output = "error: trust-wp: ghost type escape in `f`\n"
        status, message, *_rest = harness_runner._classify_outcome(
            harness, tmp_path, "tests/should_fail/synthetic.rs", "fn f() {}",
            False, output, 2,
        )
        assert (status, message) == ("pass", "Correctly rejected (ghost type escape)")


class TestNoReplayVerifiedTier:
    SOURCE = "// NO_REPLAY\n#[ensures(result == 1)]\nfn f() -> u32 { 1 }\n"

    def _outcome(self, tmp_path, name, output, exit_code):
        status, message, *_rest = harness_runner._classify_outcome(
            harness, tmp_path, name, self.SOURCE, exit_code == 0, output, exit_code
        )
        tier = harness.classify_verification_tier(name, status, message, None, self.SOURCE)
        return status, message, tier

    def test_verified_clean_no_replay_is_tier2(self, tmp_path):
        output = "trust-wp: f verified ✓\n" + _wire_line(verified=2)
        status, message, tier = self._outcome(
            tmp_path, "tests/should_succeed/lang/float_ops.rs", output, 0
        )
        assert status == "pass"
        assert message.startswith(harness.NO_REPLAY_VERIFIED_PREFIX)
        assert tier == "tier2"

    def test_clean_run_that_verified_nothing_is_not_a_pass(self, tmp_path):
        # D-21: off the allowlist a NO_REPLAY test is credited only as a
        # real proof; a clean run that verified nothing is not a credit.
        status, message, tier = self._outcome(
            tmp_path, "tests/should_succeed/bug/387.rs", _wire_line(), 0
        )
        assert status != "pass"
        assert not message.startswith(harness.NO_REPLAY_PASS_PREFIX)
        assert tier == "tier3"

    def test_allowlisted_translate_only_stays_parse_only(self, tmp_path):
        output = "trust-wp: omg FAILED ✗\n" + _wire_line(failed=1, base_exit_code=1)
        status, message, tier = self._outcome(
            tmp_path, "tests/should_succeed/bug/653.rs", output, 1
        )
        assert status == "pass"
        assert message.startswith(harness.NO_REPLAY_PASS_PREFIX)
        assert tier == "tier3"

    def test_mode_is_none_for_non_pass(self):
        output = _wire_line(errors=1, base_exit_code=2)
        assert harness.classify_no_replay_result_with_mode(output, exit_code=2)[2] is None

    def test_verified_prefix_does_not_override_trusted_marker(self):
        message = f"{harness.NO_REPLAY_VERIFIED_PREFIX} x\n1 trusted (skipped)"
        assert harness.classify_verification_tier(
            "tests/should_succeed/a.rs", "pass", message, None, self.SOURCE
        ) == "tier3"


class TestFinalGatePolicy:
    def _sf_violations(self, **result):
        module = _load_compare_baselines()
        base = {"name": "tests/should_fail/x.rs", "status": "pass"}
        base.update(result)
        return module._should_fail_true_100_violation_reasons(base)

    def _ss_violations(self, **result):
        module = _load_compare_baselines()
        base = {"status": "pass"}
        base.update(result)
        return module._true_100_violation_reasons(base)

    @pytest.mark.parametrize(
        "key", ["parse_errors", "termination_errors", "logic_recursion_errors"]
    )
    def test_frontend_rejection_counters_are_not_violations(self, key):
        # Exempt only on the matching credit channel.
        credit = {
            "parse_errors": "parse_errors=2",
            "termination_errors": "termination check failed",
            "logic_recursion_errors": "logic recursion check failed",
        }[key]
        reasons = self._sf_violations(
            message=f"Correctly rejected ({credit})",
            telemetry=_complete_telemetry(**{key: 2, "base_exit_code": 2}),
        )
        assert reasons == []

    @pytest.mark.parametrize(
        "key", ["trusted", "assumed", "vacuous", "panics", "evidence_gaps", "erasure_errors"]
    )
    def test_soundness_counters_still_violate(self, key):
        reasons = self._sf_violations(
            message="Correctly rejected (wire failed=1)",
            telemetry=_complete_telemetry(**{key: 1, "failed": 1}),
        )
        assert f"telemetry.{key}=1" in reasons

    def test_frontend_rejection_without_wire_line_is_valid(self):
        assert self._sf_violations(
            message="Correctly rejected (compile: error[E0499])", telemetry=None
        ) == []

    def test_solver_credit_without_wire_line_still_violates(self):
        reasons = self._sf_violations(
            message="Correctly rejected (wire failed=1)", telemetry=None
        )
        assert "telemetry missing or malformed" in reasons

    def test_legacy_uncredited_rejection_without_wire_line_still_violates(self):
        reasons = self._sf_violations(message="Correctly rejected", telemetry=None)
        assert "telemetry missing or malformed" in reasons

    def test_frontend_rejection_with_malformed_telemetry_still_violates(self):
        reasons = self._sf_violations(
            message="Correctly rejected (frontend: x)", telemetry={"verified": 0}
        )
        assert any("telemetry missing field" in r for r in reasons)

    def test_non_pass_frontend_message_is_not_exempt(self):
        reasons = self._sf_violations(
            status="error", message="Correctly rejected (frontend: x)", telemetry=None
        )
        assert "telemetry missing or malformed" in reasons

    def test_verified_no_replay_tier2_passes_gate(self):
        assert self._ss_violations(
            name="tests/should_succeed/lang/float_ops.rs",
            message="Verified (NO_REPLAY): verified with clean telemetry",
            verification_tier="tier2",
            telemetry=_complete_telemetry(verified=6),
            driver_report=[
                f"trust-wp: {fn} verified ✓" for fn in ("eq", "lt", "le", "gt", "ge", "neg")
            ],
        ) == []

    def test_verified_no_replay_tier2_missing_an_item_violates(self):
        reasons = self._ss_violations(
            name="tests/should_succeed/lang/float_ops.rs",
            message="Verified (NO_REPLAY): verified with clean telemetry",
            verification_tier="tier2",
            telemetry=_complete_telemetry(verified=5),
            driver_report=[f"trust-wp: {fn} verified ✓" for fn in ("eq", "lt", "le", "gt", "ge")],
        )
        assert any(r.startswith("uncovered Creusot goal item neg [postcondition") for r in reasons)

    def test_allowlisted_parse_only_passes_gate(self):
        assert self._ss_violations(
            name="tests/should_succeed/bug/653.rs",
            message="Parse-only (NO_REPLAY): syntax-only test",
            verification_tier="tier3",
            telemetry=_complete_telemetry(failed=1, proof_assert_failed=1, base_exit_code=1),
            driver_report=["trust-wp: omg FAILED ✗ (postcondition)"],
        ) == []

    def test_allowlisted_parse_only_still_fails_on_trusted(self):
        reasons = self._ss_violations(
            name="tests/should_succeed/spec_tests.rs",
            message="Parse-only (NO_REPLAY): syntax-only test",
            verification_tier="tier3",
            telemetry=_complete_telemetry(trusted=1, base_exit_code=2),
        )
        # The parse-only row does not name the trusted item, so source
        # resolution fails closed too.
        assert "telemetry.trusted=1" in reasons
        assert any(r.startswith("trusted count 1 != 0") for r in reasons)

    def test_non_allowlisted_parse_only_still_violates(self):
        reasons = self._ss_violations(
            name="tests/should_succeed/bug/387.rs",
            message="Parse-only (NO_REPLAY): syntax-only test",
            verification_tier="tier3",
            telemetry=_complete_telemetry(),
        )
        assert "NO_REPLAY parse-only pass" in reasons
        assert "verification_tier='tier3' (expected 'tier2')" in reasons

    def test_allowlist_requires_exact_path_component(self):
        reasons = self._ss_violations(
            name="tests/should_succeed/bug/6530.rs",
            message="Parse-only (NO_REPLAY): syntax-only test",
            verification_tier="tier3",
            telemetry=_complete_telemetry(),
        )
        assert "NO_REPLAY parse-only pass" in reasons

    def test_gate_allowlist_matches_classifier_allowlist(self):
        module = _load_compare_baselines()
        assert tuple(module.NO_REPLAY_TRANSLATE_ONLY_ALLOWLIST) == tuple(
            harness.harness_classify._NO_REPLAY_TRANSLATE_ONLY_ALLOWLIST
        )

    def test_gate_frontend_credits_cover_classifier_frontend_channels(self):
        """Every frontend credit label the classifier can emit is exempt at the gate."""
        module = _load_compare_baselines()
        samples = [
            ("error: termination check failed\n", None),
            ("error: logic recursion check failed\n", None),
            ("parse_errors=1\n", None),
            ("duplicate/conflicting extern_spec\n", None),
            ("trusted contract validation\n", None),
            ("ghost type escape\n", None),
            ("where its run-time body is not the logical operation the verifier reads\n", None),
            ("Cannot divide primitive integers in logic\n", None),
        ]
        for output, _ in samples:
            status, _reason, credit = _sf(output)
            assert status == "pass", output
            assert credit.startswith(module.FRONTEND_REJECTION_CREDIT_PREFIXES), credit


def test_review_compat_timeout_matches_refresh_default():
    review = (WORKSPACE_ROOT / "scripts" / "creusot_replacement_review.sh").read_text()
    refresh = (WORKSPACE_ROOT / "scripts" / "refresh-baselines.sh").read_text()
    import re as _re

    review_default = _re.search(r"^COMPAT_TIMEOUT=(\d+)$", review, _re.M)
    refresh_default = _re.search(r"TRUST_WP_HARNESS_TIMEOUT:-(\d+)", refresh)
    assert review_default and refresh_default
    assert review_default.group(1) == refresh_default.group(1) == "300"


def test_review_examples_lane_is_advisory_but_canonical_lanes_gate():
    review = (WORKSPACE_ROOT / "scripts" / "creusot_replacement_review.sh").read_text()
    body = review[review.index("run_compat_gates() {") :]
    body = body[: body.index("\n}\n")]
    for lane in ("should_succeed", "should_fail"):
        block = body[body.index(f"run_creusot_lane {lane} ") :]
        block = block[: block.index("fi")]
        assert "exit_code=1" in block, f"{lane} must stay a fatal gate"
    examples = body[body.index("run_creusot_lane examples ") :]
    examples = examples[: examples.index("fi")]
    assert "exit_code=1" not in examples
    assert "WARNING" in examples


def test_refresh_baselines_calls_only_existing_python_scripts():
    import re as _re

    refresh = (WORKSPACE_ROOT / "scripts" / "refresh-baselines.sh").read_text()
    code = "\n".join(
        line for line in refresh.splitlines() if not line.lstrip().startswith("#")
    )
    for script in _re.findall(r"python3\s+(scripts/[\w./-]+\.py)", code):
        assert (WORKSPACE_ROOT / script).is_file(), f"refresh calls missing {script}"


def test_reference_pin_files_agree():
    pin = (HARNESS_DIR / "REFERENCE.pin").read_text().split()[0]
    short = (HARNESS_DIR / "CREUSOT_REFERENCE_PIN").read_text().strip()
    assert len(short) >= 7 and pin.startswith(short), (pin, short)


# ---------------------------------------------------------------------------
# #[trusted] parity (D-49): trusted>0 is accepted ONLY when every trusted
# item is declared #[trusted] in the corpus source, graded tier2-source-trusted.
# ---------------------------------------------------------------------------


def _load_trusted_scan():
    spec = importlib.util.spec_from_file_location(
        "trusted_source_scan_parity", WORKSPACE_ROOT / "scripts" / "trusted_source_scan.py"
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module  # dataclasses resolve their module
    spec.loader.exec_module(module)
    return module


_TRUSTED_SRC = """
extern crate creusot_std;
use creusot_std::prelude::*;

#[trusted]
#[ensures(result == 10u32)]
pub fn lie() -> u32 { 5 }

pub fn victim() -> u32 { lie() }

// #[trusted] fn commented_out() {}
pub fn commented_out() {}

#[trusted]
mod foo {
    pub fn inner() -> u32 { 1 }
    pub mod deeper { pub fn deepest() {} }
}

struct Mutex<T>(T);
impl<T> Mutex<T> {
    #[trusted]
    pub fn new(v: T) -> Self { Mutex(v) }
    pub fn get(&self) -> &T { &self.0 }
}

trait UseSelf { fn func(&self) -> bool; }
impl UseSelf for () { fn func(&self) -> bool { true } }
impl UseSelf for i32 {
    #[trusted]
    fn func(&self) -> bool { *self == 1 }
}

extern_spec! {
    #[trusted]
    fn victim() -> u32;
}
"""


class TestTrustedSourceScan:
    @pytest.mark.parametrize(
        "path",
        [
            "lie",
            "creusot_test::lie",
            "foo::inner",
            "foo::deeper::deepest",
            "Mutex::<T>::new",
            "<i32 as UseSelf>::func",
        ],
    )
    def test_source_declared_items_resolve(self, path):
        scan = _load_trusted_scan()
        assert scan.resolve_trusted_def_path(path, _TRUSTED_SRC)

    @pytest.mark.parametrize(
        "path",
        [
            "victim",  # #[trusted] only inside an extern_spec! body
            "commented_out",  # #[trusted] only in a comment
            "Mutex::<T>::get",  # sibling of a trusted method
            "<() as UseSelf>::func",  # same name, untrusted impl
            "<Foo as UseSelf>::func",  # no such impl
            "inner",  # wrong module qualifier
            "f::{closure#0}",  # closures never resolve
            "does_not_exist",
        ],
    )
    def test_undeclared_items_do_not_resolve(self, path):
        scan = _load_trusted_scan()
        assert not scan.resolve_trusted_def_path(path, _TRUSTED_SRC)

    def test_ambiguous_name_with_untrusted_candidate_does_not_resolve(self):
        scan = _load_trusted_scan()
        source = "mod a { #[trusted] pub fn g() {} }\nmod a { pub fn g() {} }\n"
        assert not scan.resolve_trusted_def_path("a::g", source)

    def test_count_must_match_named_items(self):
        scan = _load_trusted_scan()
        assert scan.unresolved_trusted_def_paths(["lie"], _TRUSTED_SRC, 1) == []
        assert scan.unresolved_trusted_def_paths([], _TRUSTED_SRC, 1)
        assert scan.unresolved_trusted_def_paths(["lie", "lie"], _TRUSTED_SRC, 2)

    def test_extract_skips_proof_assert_and_summary_lines(self):
        scan = _load_trusted_scan()
        output = (
            "trust-wp: lie trusted (skipped)\n"
            "trust-wp: proof_assert in creusot_test::assume trusted (skipped)\n"
            "trust-wp: (1 trusted, skipped)\n"
        )
        assert scan.extract_trusted_def_paths(output) == ["lie"]


class TestSummaryPatternsIgnoreWireFields:
    def test_trusted_wire_field_is_not_a_skipped_summary_count(self):
        module = _load_compare_baselines()
        reasons = module._true_100_violation_reasons(
            {
                "status": "pass",
                "message": "ok\nTRUST_WP_RESULT:v1 verified=2 trusted=1 skipped=0",
                "verification_tier": "tier2",
                "telemetry": _complete_telemetry(verified=2),
            }
        )
        assert "skipped summary count" not in reasons

    def test_textual_skipped_summary_still_violates(self):
        module = _load_compare_baselines()
        reasons = module._true_100_violation_reasons(
            {
                "status": "pass",
                "message": "trust-wp: 2 verified, 0 failed, 1 skipped",
                "verification_tier": "tier2",
                "telemetry": _complete_telemetry(verified=2),
            }
        )
        assert "skipped summary count" in reasons


class TestSourceTrustedTierAndGate:
    NAME = "tests/should_succeed/specification/trusted_parity_fixture.rs"

    def _message(self, trusted_paths, verified=2, **wire):
        lines = ["trust-wp: victim verified ✓"] if verified else []
        lines += [f"trust-wp: {p} trusted (skipped)" for p in trusted_paths]
        lines.append(f"trust-wp: ({len(trusted_paths)} trusted, skipped)")
        lines.append(
            f"trust-wp: {verified} verified, 0 failed, 0 errors, {len(trusted_paths)} trusted"
        )
        lines.append(
            _wire_line(verified=verified, trusted=len(trusted_paths), base_exit_code=2, **wire)
        )
        return "\n".join(lines)

    def _tier(self, message, paths=None):
        return harness.classify_verification_tier(
            self.NAME, "pass", message, None, _TRUSTED_SRC, trusted_def_paths=paths
        )

    def test_source_declared_trusted_pass_is_distinct_tier(self):
        assert self._tier(self._message(["lie", "foo::inner"])) == "tier2-source-trusted"

    def test_undeclared_trusted_item_stays_tier3(self):
        assert self._tier(self._message(["lie", "victim"])) == "tier3"

    def test_derive_generated_trusted_item_stays_tier3(self):
        assert self._tier(self._message(["<ETuple as std::default::Default>::default"])) == "tier3"

    def test_other_soundness_marker_still_tier3(self):
        message = self._message(["lie"], vacuous=1) + "\n1 vacuous"
        assert self._tier(message) == "tier3"

    def test_unnamed_trusted_counter_stays_tier3(self):
        message = "trust-wp: victim verified ✓\n" + _wire_line(verified=1, trusted=1)
        assert self._tier(message) == "tier3"

    def test_no_positive_proof_is_not_source_trusted_tier2(self):
        assert self._tier(self._message(["lie"], verified=0)) != "tier2-source-trusted"

    def _gate(self, tmp_path, monkeypatch, **result):
        module = _load_compare_baselines()
        ref = tmp_path / "reference" / "creusot" / self.NAME
        ref.parent.mkdir(parents=True)
        ref.write_text(_TRUSTED_SRC)
        # Creusot's inventory for the fixture: only ``victim`` bears a goal
        # (a trusted callee is a stub; ``lie`` has no VC of its own).
        ref.with_suffix(".coma").write_text(
            "module M_victim\n"
            "  let rec lie (return (x: UInt32.t)) = any\n"
            "    [ return (result: UInt32.t) -> {[@expl:lie ensures] UInt32.t'int result = 10} (! return {result}) ]\n"
            "  \n"
            "  let rec victim (return (x: UInt32.t)) = (! bb0\n"
            "    [ bb0 = s0 [ s0 = UInt32.add {(1: UInt32.t)} {(2: UInt32.t)} (fun (_x: UInt32.t) -> [ &_ret <- _x ] s1) | s1 = return {_ret} ] ]\n"
            "    [ & _ret: UInt32.t = Any.any_l () ]) [ return (result: UInt32.t) -> (! return {result}) ]\n"
            "end\n"
        )
        monkeypatch.setattr(module, "REPO_ROOT", tmp_path)
        base = {"name": self.NAME, "status": "pass"}
        base.update(result)
        return module._true_100_violation_reasons(base)

    def test_gate_accepts_source_declared_trusted(self, tmp_path, monkeypatch):
        reasons = self._gate(
            tmp_path,
            monkeypatch,
            message=self._message(["lie", "Mutex::<T>::new"]),
            verification_tier="tier2-source-trusted",
            trusted_def_paths=["lie", "Mutex::<T>::new"],
            telemetry=_complete_telemetry(verified=2, trusted=2, base_exit_code=2),
            driver_report=["trust-wp: victim verified ✓"],
        )
        assert reasons == []

    def test_gate_rejects_undeclared_trusted(self, tmp_path, monkeypatch):
        reasons = self._gate(
            tmp_path,
            monkeypatch,
            message="Verification succeeded",
            verification_tier="tier2-source-trusted",
            trusted_def_paths=["victim"],
            telemetry=_complete_telemetry(verified=2, trusted=1, base_exit_code=2),
        )
        assert any("not declared #[trusted] in source: victim" in r for r in reasons)
        assert "telemetry.trusted=1" in reasons

    def test_gate_rejects_count_mismatch(self, tmp_path, monkeypatch):
        reasons = self._gate(
            tmp_path,
            monkeypatch,
            message="Verification succeeded",
            verification_tier="tier2-source-trusted",
            trusted_def_paths=["lie"],
            telemetry=_complete_telemetry(verified=2, trusted=2, base_exit_code=2),
        )
        assert "telemetry.trusted=2" in reasons

    def test_gate_rejects_trusted_with_plain_tier3(self, tmp_path, monkeypatch):
        reasons = self._gate(
            tmp_path,
            monkeypatch,
            message="Verification succeeded",
            verification_tier="tier3",
            trusted_def_paths=["lie"],
            telemetry=_complete_telemetry(verified=2, trusted=1, base_exit_code=2),
        )
        assert "telemetry.trusted=1" in reasons

    def test_gate_rejects_missing_source(self, tmp_path, monkeypatch):
        module = _load_compare_baselines()
        monkeypatch.setattr(module, "REPO_ROOT", tmp_path)
        reasons = module._true_100_violation_reasons(
            {
                "name": "tests/should_succeed/missing.rs",
                "status": "pass",
                "message": "Verification succeeded",
                "verification_tier": "tier2-source-trusted",
                "trusted_def_paths": ["lie"],
                "telemetry": _complete_telemetry(verified=2, trusted=1),
            }
        )
        assert any("source for trusted resolution not found" in r for r in reasons)

    def test_gate_does_not_accept_other_counters_on_source_trusted(self, tmp_path, monkeypatch):
        reasons = self._gate(
            tmp_path,
            monkeypatch,
            message="Verification succeeded",
            verification_tier="tier2-source-trusted",
            trusted_def_paths=["lie"],
            telemetry=_complete_telemetry(verified=2, trusted=1, assumed=1),
        )
        assert "telemetry.assumed=1" in reasons

    def test_summary_reports_source_trusted_separately(self):
        results = [
            harness.TestResult(
                name=self.NAME, status="pass", message="m", duration_ms=1,
                verification_tier="tier2-source-trusted",
            )
        ]
        summary = harness.summarize_results(results)
        assert summary["tier2_source_trusted"] == 1
        assert summary["tier2_verified"] == 0


# ---------------------------------------------------------------------------
# Review probes: a driver crash is never a rejection (F1), counter exemptions
# are tied to their credit channel (F2a), trust counters block the NO_REPLAY
# verified mode (N1).
# ---------------------------------------------------------------------------


class TestReviewOf2480c85:
    # F1: driver crash after a frontend marker is never a rejection.
    def test_f1_marker_on_warning_then_sigsegv_is_error(self):
        output = (
            "warning: proof_assert!(false) inside a loop is an unsatisfied proof obligation\n"
            "error: could not compile `probe` (lib)\n\nCaused by:\n"
            "  process didn't exit successfully: `trust-wp-driver ...` "
            "(signal: 11, SIGSEGV: invalid memory reference)\n"
        )
        assert _sf(output, exit_code=101) == ("error", None, None)

    def test_f1_marker_on_note_then_exit_101_is_error(self):
        output = (
            "note: the HashMap/BTreeMap Entry API\n"
            "error: could not compile `probe` (lib)\nCaused by:\n"
            "  process didn't exit successfully (exit status: 101)\n"
        )
        assert _sf(output, exit_code=101) == ("error", None, None)

    def test_f1_guard_span_err_frontend_refusal_still_credited(self):
        output = (
            "error: used the `#[trusted]` attribute\n --> src/lib.rs:6:1\n"
            "error: used the `#[trusted]` attribute\n --> src/lib.rs:12:1\n"
            "error: aborting due to 2 previous errors\n\n"
            "error: could not compile `creusot_test` (lib) due to 2 previous errors\n"
        )
        status, _reason, credit = _sf(output, exit_code=101)
        assert status == "pass"
        assert credit.startswith("frontend: ") and "driver exit 101" not in credit

    # F2a: counter exemptions are tied to the matching credit channel.
    def _sf_gate(self, **result):
        module = _load_compare_baselines()
        base = {"name": "tests/should_fail/probe.rs", "status": "pass"}
        base.update(result)
        return module._should_fail_true_100_violation_reasons(base)

    def test_f2a_solver_credit_with_parse_errors_is_flagged(self):
        reasons = self._sf_gate(
            message="Correctly rejected (wire failed=1)",
            telemetry=_complete_telemetry(failed=1, parse_errors=3, base_exit_code=1),
        )
        assert "telemetry.parse_errors=3" in reasons

    def test_f2a_termination_credit_does_not_exempt_parse_errors(self):
        reasons = self._sf_gate(
            message="Correctly rejected (termination check failed)",
            telemetry=_complete_telemetry(termination_errors=1, parse_errors=2),
        )
        assert reasons == ["telemetry.parse_errors=2"]

    @pytest.mark.parametrize(
        "credit,key",
        [
            ("termination check failed (termination_errors=1)", "termination_errors"),
            ("logic recursion check failed", "logic_recursion_errors"),
            ("parse_errors=1", "parse_errors"),
        ],
    )
    def test_f2a_matching_channel_is_exempt(self, credit, key):
        reasons = self._sf_gate(
            message=f"Correctly rejected ({credit})",
            telemetry=_complete_telemetry(**{key: 1, "base_exit_code": 2}),
        )
        assert reasons == []

    # F2b: missing telemetry only for compile:/frontend: without exit-101.
    def test_f2b_parse_errors_credit_without_telemetry_is_flagged(self):
        reasons = self._sf_gate(message="Correctly rejected (parse_errors=1)", telemetry=None)
        assert "telemetry missing or malformed" in reasons

    def test_f2b_exit_101_frontend_credit_without_telemetry_is_flagged(self):
        reasons = self._sf_gate(
            message="Correctly rejected (frontend: used the `#[trusted]` attribute (driver exit 101))",
            telemetry=None,
        )
        assert "telemetry missing or malformed" in reasons

    def test_f2b_termination_credit_without_telemetry_is_flagged(self):
        reasons = self._sf_gate(
            message="Correctly rejected (termination check failed)", telemetry=None
        )
        assert "telemetry missing or malformed" in reasons

    @pytest.mark.parametrize(
        "credit", ["compile: error[E0499]", "frontend: used the `#[trusted]` attribute"]
    )
    def test_f2b_guard_compile_and_frontend_may_lack_telemetry(self, credit):
        assert self._sf_gate(message=f"Correctly rejected ({credit})", telemetry=None) == []

    # N1: trust counters block the NO_REPLAY verified mode.
    @pytest.mark.parametrize(
        "counter",
        ["trusted", "skipped", "assumed", "vacuous", "unverified_axioms",
         "verified_with_axiom_deps", "evidence_gaps"],
    )
    def test_n1_no_replay_verified_requires_zero_trust_counters(self, counter):
        output = "trust-wp: f verified ✓\n" + _wire_line(verified=1, **{counter: 2})
        status, _skip, mode = harness.classify_no_replay_result_with_mode(
            output, exit_code=0, test_name="tests/should_succeed/bug/387.rs"
        )
        # D-21: a trust counter on a non-allowlisted NO_REPLAY test is
        # neither a verified pass nor a translate-only credit.
        assert status != "pass"
        assert mode is None

    def test_n1_guard_clean_verified_no_replay_is_still_verified(self):
        output = "trust-wp: f verified ✓\n" + _wire_line(verified=1)
        assert harness.classify_no_replay_result_with_mode(
            output, exit_code=0, test_name="tests/should_succeed/bug/387.rs"
        )[2] == "verified"

    # N2: allowlist matches by exact path, like the gate.
    def test_n2_allowlist_prefix_lookalike_is_not_allowed(self):
        output = "trust-wp: user FAILED ✗\n" + _wire_line(failed=1, base_exit_code=1)
        status, _skip, _mode = harness.classify_no_replay_result_with_mode(
            output, exit_code=1, test_name="tests/should_succeed/spec_tests_extra.rs"
        )
        assert status != "pass"

    def test_n2_guard_exact_allowlisted_path_still_allowed(self):
        output = "trust-wp: test_specs FAILED ✗\n" + _wire_line(failed=1, base_exit_code=1)
        status, _skip, mode = harness.classify_no_replay_result_with_mode(
            output, exit_code=1, test_name="tests/should_succeed/spec_tests.rs"
        )
        assert (status, mode) == ("pass", "translate_only")


class TestTranslateOnlyAllowlistBug511:
    def test_bug_511_zero_obligation_parse_only_is_accepted_at_gate(self):
        module = _load_compare_baselines()
        reasons = module._true_100_violation_reasons(
            {
                "name": "tests/should_succeed/bug/511.rs",
                "status": "pass",
                "message": "Parse-only (NO_REPLAY): syntax-only test",
                "verification_tier": "tier3",
                "driver_report": [],
                "telemetry": _complete_telemetry(),
            }
        )
        assert reasons == []

    @pytest.mark.parametrize(
        "name",
        [
            "tests/should_succeed/bug/387.rs",
            "tests/should_succeed/syntax/10_mutual_rec_types.rs",
            "tests/should_succeed/closures/03_generic_bound.rs",
            "tests/should_succeed/closures/04_generic_closure.rs",
            "tests/should_succeed/closures/05_map.rs",
            "tests/should_succeed/traits/04.rs",
            "tests/should_succeed/closures/01_basic.rs",
            "tests/should_succeed/syntax/04_assoc_prec.rs",
            "tests/should_succeed/lang/float_ops.rs",
        ],
    )
    def test_skipped_obligation_no_replay_tests_are_not_allowlisted(self, name):
        module = _load_compare_baselines()
        reasons = module._true_100_violation_reasons(
            {
                "name": name,
                "status": "pass",
                "message": "Parse-only (NO_REPLAY): syntax-only test",
                "verification_tier": "tier3",
                "telemetry": _complete_telemetry(),
            }
        )
        assert "NO_REPLAY parse-only pass" in reasons


class TestProofAssertInconclusiveIsNotAProofPass:
    """An inconclusive proof_assert (solver unknown) is an unproved assertion."""

    SOURCE = "#[trusted]\nfn calls_closure() {}\npub fn f() { proof_assert!(true) }\n"
    NAME = "tests/should_succeed/closures/pa_inconclusive_fixture.rs"

    def _message(self, inconclusive):
        return (
            "trust-wp: f verified ✓\n"
            "trust-wp: calls_closure trusted (skipped)\n"
            "trust-wp: (1 trusted, skipped)\n"
            "trust-wp: 3 verified, 0 failed, 0 errors, 1 trusted\n"
            f"trust-wp: proof_assert: 5 verified, 0 failed, 0 errors, {inconclusive} inconclusive\n"
            + _wire_line(verified=3, trusted=1, proof_assert_verified=5,
                         proof_assert_inconclusive=inconclusive, base_exit_code=2)
        )

    def test_inconclusive_blocks_source_trusted_tier(self):
        tier = harness.classify_verification_tier(
            self.NAME, "pass", self._message(1), None, self.SOURCE
        )
        assert tier == "tier3"

    def test_source_trusted_tier_without_inconclusive(self):
        tier = harness.classify_verification_tier(
            self.NAME, "pass", self._message(0), None, self.SOURCE
        )
        assert tier == "tier2-source-trusted"

    def test_inconclusive_blocks_plain_tier2(self):
        message = "Verification succeeded\n" + _wire_line(
            verified=2, proof_assert_verified=1, proof_assert_inconclusive=1
        )
        assert harness.classify_verification_tier(
            "tests/should_succeed/x.rs", "pass", message, None, "fn f() {}"
        ) == "tier3"

    def test_gate_flags_inconclusive_counter(self):
        module = _load_compare_baselines()
        reasons = module._true_100_violation_reasons(
            {
                "name": "tests/should_succeed/x.rs",
                "status": "pass",
                "message": "Verification succeeded",
                "verification_tier": "tier2",
                "telemetry": _complete_telemetry(verified=2, proof_assert_inconclusive=1),
            }
        )
        assert "telemetry.proof_assert_inconclusive=1" in reasons


class TestWithheldRefutationIsNeverASuccess:
    """The harness-side mirror of withheld refutations (D-27).

    Withholding moves verdicts out of ``failed`` into ``unknown``. The risk it
    creates is not a false accept — it is somebody downstream reading
    ``unknown`` as success. Gate-clean is ``status == "pass"`` AND tier in
    {tier1, tier2, tier2-source-trusted}; these pin that an inconclusive
    reaches neither half.
    """

    NAME = "tests/should_succeed/x.rs"
    SOURCE = "#[ensures(result == x)]\nfn f(x: u32) -> u32 { x }"
    WITHHELD = (
        "trust-wp: f unknown (refutation withheld: goal set carries a "
        "fail-closed `false` trust-wp injected for a construct it could not "
        "model)\ntrust-wp: 0 verified, 0 failed, 1 errors"
    )

    def test_a_withheld_refutation_is_not_tier1_or_tier2(self):
        for status in ("unknown", "error", "fail"):
            tier = harness.classify_verification_tier(
                self.NAME, status, self.WITHHELD, None, self.SOURCE
            )
            assert tier == "tier3", (status, tier)

    def test_a_withheld_refutation_is_not_gate_clean(self):
        # Gate-clean needs BOTH halves. An inconclusive fails the tier half
        # even if some future classifier change were to call it a pass.
        gate_clean_tiers = {"tier1", "tier2", "tier2-source-trusted"}
        tier = harness.classify_verification_tier(
            self.NAME, "error", self.WITHHELD, None, self.SOURCE
        )
        assert tier not in gate_clean_tiers

    def test_a_verified_crate_is_still_gradeable(self):
        # The control: withholding a refutation must not make PROVING harder.
        message = "Verification succeeded\n" + _wire_line(verified=2)
        assert (
            harness.classify_verification_tier(
                self.NAME, "pass", message, None, self.SOURCE
            )
            in {"tier1", "tier2"}
        )


# ---------------------------------------------------------------------------
# Creusot goal coverage: a proof-grade pass must have examined every item
# Creusot generates goals for. Outputs below are recorded driver runs on the
# adversarial review's probes.
# ---------------------------------------------------------------------------


def _load_goal_coverage():
    spec = importlib.util.spec_from_file_location(
        "creusot_goal_coverage_t", WORKSPACE_ROOT / "scripts" / "creusot_goal_coverage.py"
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


_CORPUS_SS = WORKSPACE_ROOT / "reference" / "creusot" / "tests" / "should_succeed"

_ST_OVERFLOW_SRC = """extern crate creusot_std;
use creusot_std::prelude::*;

#[trusted]
#[ensures(result == 5u32)]
fn five() -> u32 {
    5
}

#[ensures(result == 5u32)]
pub fn ok() -> u32 {
    five()
}

pub fn bad(x: u32) -> u32 {
    x + 1
}
"""

# Hand-authored in the exact shape Creusot emits for st_overflow.rs (compare
# erasure.coma M_test_foo): a trusted callee is a stub, `x + 1` is a prelude
# `UInt32.add` call whose precondition is the overflow goal.
_ST_OVERFLOW_OK_COMA = """module M_ok
  use creusot.int.UInt32
  use creusot.prelude.Any
  
  let rec five (return (x: UInt32.t)) = any
    [ return (result: UInt32.t) -> {[@stop_split] [@expl:five ensures] UInt32.t'int result = 5} (! return {result}) ]
  
  meta "compute_max_steps" 1000000
  
  let rec ok (return (x: UInt32.t)) = (! bb0
    [ bb0 = s0 [ s0 = five (fun (_x: UInt32.t) -> [ &_ret <- _x ] s1) | s1 = return {_ret} ] ]
    [ & _ret: UInt32.t = Any.any_l () ])
    [ return (result: UInt32.t) -> {[@stop_split] [@expl:ok ensures] UInt32.t'int result = 5}
      (! return {result}) ]
end
"""
_ST_OVERFLOW_BAD_COMA = """module M_bad
  use creusot.int.UInt32
  use creusot.prelude.Any
  
  meta "compute_max_steps" 1000000
  
  let rec bad (x: UInt32.t) (return (x'0: UInt32.t)) = (! bb0
    [ bb0 = s0
      [ s0 = UInt32.add {x} {(1: UInt32.t)} (fun (_x: UInt32.t) -> [ &_ret <- _x ] s1) | s1 = return {_ret} ] ]
    [ & _ret: UInt32.t = Any.any_l () | & x: UInt32.t = x ])
    [ return (result: UInt32.t) -> (! return {result}) ]
end
"""

_ST_OVERFLOW_OUT = (
    "trust-wp: five trusted (skipped)\n"
    "trust-wp: ok verified ✓\n\n"
    "trust-wp: (1 trusted, skipped)\n"
    "trust-wp: 1 verified, 0 failed, 0 errors, 1 trusted\n"
)

_ST_CLOSURE_PRE_SRC = """extern crate creusot_std;
use creusot_std::prelude::*;

pub fn multi_use<T>(x: &T) {
    let c = #[requires(false)]
    || {
        let _ = x;
        0
    };

    uses_fn(c);
}

#[trusted]
#[requires(f.precondition(()))]
#[ensures(exists<f2: &F, r> *f2 == f && f2.postcondition((), r))]
fn uses_fn<F: Fn() -> u32>(f: F) {
    f();
}
"""

_ST_CLOSURE_PRE_OUT = (
    "trust-wp: multi_use::{closure#0} verified ✓ (vacuous: explicit #[requires(false)])\n"
    "  at src/lib.rs:9:5: 9:7\n"
    "trust-wp: uses_fn trusted (skipped)\n\n"
    "trust-wp: (1 trusted, skipped)\n"
    "trust-wp: 1 verified, 0 failed, 0 errors, 1 trusted\n"
)

_ST_TRUSTED_PRE_SRC = """extern crate creusot_std;
use creusot_std::prelude::*;

#[trusted]
#[requires(x > 10u32)]
#[ensures(result == x)]
fn id_big(x: u32) -> u32 {
    x
}

#[ensures(result == 3u32)]
pub fn caller() -> u32 {
    id_big(3u32)
}
"""

_ST_CONTROL_SRC = """extern crate creusot_std;
use creusot_std::prelude::*;

#[trusted]
#[ensures(result == 5u32)]
fn five() -> u32 {
    5
}

#[ensures(result == 6u32)]
pub fn bad() -> u32 {
    five()
}
"""


class TestCreusotGoalInventory:
    def test_100doors_goal_kinds(self):
        gc = _load_goal_coverage()
        items = gc.goal_inventory("tests/should_succeed/100doors.rs")
        assert [i.item for i in items] == ["f"]
        # 2 for-invariants + 1 outer + 2 inner loop invariants; index + index_mut
        # requires; two `door - 1` subs and one `door += pass` add.
        assert dict(items[0].goal_kinds) == {"loop invariant": 5, "index bounds": 2, "overflow": 3}

    def test_closure_08_multi_use_carries_callee_requires(self):
        gc = _load_goal_coverage()
        items = {i.item: i for i in gc.goal_inventory("tests/should_succeed/closures/08_multiple_calls.rs")}
        # the closure body proves nothing; the obligation is uses_fn's requires
        assert set(items) == {"multi_use"}
        assert items["multi_use"].goal_kinds["callee requires"] == 1

    def test_span_mode_calls_and_refinement(self):
        gc = _load_goal_coverage()
        items = {i.item: i for i in gc.goal_inventory("tests/should_succeed/spans.rs")}
        assert items["quux"].goal_kinds["callee requires"] == 1  # `decr [%#sspans'0] {i}`
        assert items["impl_Tr_for_S::foo refinement"].refines
        assert items["baz"].goal_kinds["logic goal"] == 1

    def test_stub_only_items_have_no_goals(self):
        gc = _load_goal_coverage()
        names = {i.item for i in gc.goal_inventory("tests/should_succeed/specification/erasure.rs")}
        assert {"test_foo", "test_foo2"} <= names
        assert not names & {"quux2", "takes_ref", "takes_ref_test", "takes_ref_test2"}

    def test_missing_coma_is_none(self):
        gc = _load_goal_coverage()
        assert gc.goal_inventory("tests/should_succeed/bug/265.rs") is None

    # --- unlabelled ``{false} any`` abort obligations (D-19) -----------------
    # Creusot emits ``Terminator::Abort`` -- the panic edge of a Rust
    # ``assert!``/``unreachable!`` and every MIR block Rust proves dead -- as an
    # UNLABELLED ``<bb> = {false} any`` assertion (backend/program.rs). The
    # labelled-brace walk counts none of it; an inventory that stopped there
    # would report zero goals for such a row and grant the zero-goal credit on
    # a false premise.

    def test_abort_block_is_counted_as_an_unreachable_goal(self):
        gc = _load_goal_coverage()
        # match_int.rs: three `assert!` -> three `{false} any` blocks in `f`.
        items = {i.item: i for i in gc.goal_inventory("tests/should_succeed/match_int.rs")}
        assert items["f"].goal_kinds["unreachable"] == 3

    def test_abort_counts_per_corpus_row(self):
        gc = _load_goal_coverage()
        for test, expected in [
            ("tests/should_succeed/bug/1248.rs", 16),
            ("tests/should_succeed/match_int.rs", 3),
            ("tests/should_succeed/lang/branch_borrow_2.rs", 1),
            ("tests/should_succeed/lang/unary_op.rs", 1),
        ]:
            items = gc.goal_inventory(test)
            got = sum(i.goal_kinds.get("unreachable", 0) for i in items)
            assert got == expected, (test, got, expected)

    def test_outcome_position_false_is_a_branch_condition_not_a_goal(self):
        """``br0 -> {false} (! bb)`` is the branch condition of a switch on the
        literal ``false`` discriminant -- a handler precondition of an abstract
        ``any``, which nothing discharges. loop.rs and one_side_update.rs carry
        ONLY that form (and zero ``assert!``), so both stay zero-goal."""
        gc = _load_goal_coverage()
        for test in ("tests/should_succeed/loop.rs", "tests/should_succeed/one_side_update.rs"):
            text = gc.coma_path_for_test(test).read_text(encoding="utf-8")
            assert "{false}" in text  # the token IS present ...
            items = gc.goal_inventory(test)
            assert sum(i.goal_kinds.get("unreachable", 0) for i in items) == 0  # ... and is not a goal
            assert items == []

    def test_extspec_closure_abort_is_still_not_a_goal(self):
        """bug/1312's ``unreachable!()`` sits in a contract-free closure emitted
        ``[@coma:extspec]`` (no black_box barrier): its body is inlined at call
        sites, so the obligation is the CALLER's and the closure has none of its
        own. Creusot discharges ``vc_closure0`` in 0.026s with the `{false}`
        present and no precondition ruling out ``None`` -- which it could not do
        if that assertion were part of the closure's own VC."""
        gc = _load_goal_coverage()
        text = gc.coma_path_for_test("tests/should_succeed/bug/1312.rs").read_text(encoding="utf-8")
        assert "[@coma:extspec]" in text and "= {false} any" in text
        assert gc.goal_inventory("tests/should_succeed/bug/1312.rs") == []

    def test_abort_regex_shape(self):
        gc = _load_goal_coverage()
        counted = "  let rec f (return (x: ())) = (! bb0 [ bb0 = (! bb1) | bb1 = {false} any ])"
        not_counted = "  let rec g (return (x: ())) = (! bb0 [ bb0 = any [ br0 -> {false} (! bb1) ] ])"
        mod_c = gc.parse_coma("module M_f" + chr(10) + counted + chr(10) + "end")[0]
        mod_n = gc.parse_coma("module M_g" + chr(10) + not_counted + chr(10) + "end")[0]
        assert gc.module_goal_items(mod_c)[0].goal_kinds["unreachable"] == 1
        assert gc.module_goal_items(mod_n) == []

    @pytest.mark.parametrize(
        "module,path,disamb,expected",
        [
            ("M_impl_Tr_for_S__foo", "<S as Tr>::foo", False, True),
            ("M_impl_Tr_for_S__foo", "<T as Tr>::foo", False, False),
            ("M_impl_List_T__len", "List::<T>::len", False, True),
            ("M_impl_List_T__len", "creusot_test::List::<T>::len", False, True),
            ("M_i128__test_add", "i128::test_add", False, True),
            ("M_impl_laws", "impl_laws", False, True),
            ("M_trait_Trait__goo", "Trait::goo", False, True),
            ("M_impl_Model_for_ref_T__model", "<&T as Model>::model", False, True),
            ("M_impl_Clone_for_List_tup2_K_V__clone", "<List<(K, V)> as std::clone::Clone>::clone", False, True),
            (
                "M_custom_variant__impl_WellFounded_for_CustomVariant__no_infinite_decreasing_sequence",
                "<custom_variant::CustomVariant as creusot_std::WellFounded>::no_infinite_decreasing_sequence",
                False,
                True,
            ),
            ("M_custom_variant_0", "custom_variant", True, True),
            ("M_custom_variant_0", "custom_variant", False, False),
            ("M_test_6", "test", False, False),
            ("M_f", "g", False, False),
            ("M_f", "f::{closure#0}", False, False),
        ],
    )
    def test_def_path_mapping(self, module, path, disamb, expected):
        gc = _load_goal_coverage()
        from collections import Counter

        item = gc.GoalItem(module, gc.module_item_name(module), None, False, [], Counter(x=1), disamb)
        assert gc.coma_item_matches_path(item, path, disamb) is expected

    def test_closure_mapping_is_index_exact_unless_asked(self):
        gc = _load_goal_coverage()
        from collections import Counter

        item = gc.GoalItem("M_f", "f::{closure#1}", 1, False, [], Counter(x=1))
        assert gc.coma_item_matches_path(item, "f::{closure#1}")
        assert not gc.coma_item_matches_path(item, "f::{closure#0}")
        assert gc.coma_item_matches_path(item, "f::{closure#0}", ignore_closure_index=True)
        assert not gc.coma_item_matches_path(item, "f", ignore_closure_index=True)
        assert not gc.coma_item_matches_path(item, "g::{closure#0}", ignore_closure_index=True)


class TestCreusotGoalCoverage:
    def test_loop_invariant_goal_needs_loop_evidence(self):
        gc = _load_goal_coverage()
        name = "tests/should_succeed/100doors.rs"
        cov = gc.compute_goal_coverage(name, "trust-wp: f verified ✓\n")
        assert [u["item"] for u in cov["uncovered"]] == ["f"]
        assert "loop-invariant evidence" in cov["uncovered"][0]["reason"]
        cov = gc.compute_goal_coverage(name, "trust-wp: f verified ✓ (loop invariant)\n")
        assert cov["uncovered"] == []

    def test_negative_report_for_same_item_is_uncovered(self):
        gc = _load_goal_coverage()
        cov = gc.compute_goal_coverage(
            "tests/should_succeed/100doors.rs",
            "trust-wp: f verified ✓ (loop invariant)\ntrust-wp: f unknown (timeout)\n",
        )
        assert cov["uncovered"] and cov["uncovered"][0]["reason"].startswith("reported unknown")

    @pytest.mark.parametrize(
        "line",
        [
            "trust-wp: f verified* (depends on 1 unverified axiom(s))",
            "trust-wp: f vacuous (contradictory premises)",
            "trust-wp: creusot_test::f law postcondition unverified (non-strict axiom exposure)",
            "trust-wp: f assumed (axiom-only function: 1 universal postcondition(s) with trivial body)",
        ],
    )
    def test_non_clean_verdicts_do_not_cover(self, line):
        gc = _load_goal_coverage()
        cov = gc.compute_goal_coverage(
            "tests/should_succeed/100doors.rs", f"trust-wp: f verified ✓ (loop invariant)\n{line}\n"
        )
        assert cov["uncovered"] and cov["uncovered"][0]["reason"].startswith("reported ")

    def test_proof_assert_line_covers_only_assertion_items(self):
        gc = _load_goal_coverage()
        cov = gc.compute_goal_coverage(
            "tests/should_succeed/100doors.rs", "trust-wp: proof_assert in creusot_test::f verified ✓\n"
        )
        assert cov["uncovered"]

    def test_creusot_closure_index_is_not_driver_index(self):
        """bug/962: Creusot names the only user closure ``closure2``."""
        gc = _load_goal_coverage()
        name = "tests/should_succeed/bug/962.rs"
        out = "trust-wp: disjoint_captures verified ✓\ntrust-wp: disjoint_captures::{closure#0} verified ✓\n"
        assert gc.compute_goal_coverage(name, out)["uncovered"] == []

    def test_nested_closures_count_toward_the_flat_module(self):
        """closures/10_tyinv: Creusot defines closure0 and closure1 flat in M_f."""
        gc = _load_goal_coverage()
        out = "\n".join(
            [
                # recorded driver output
                "trust-wp: f::{closure#0} verified ✓",
                "trust-wp: verifying proof_assert in creusot_test::f::{closure#0} (0 contract preconditions)",
                "trust-wp: proof_assert in creusot_test::f::{closure#0} verified ✓",
                "trust-wp: f::{closure#0}::{closure#1} verified ✓",
                "trust-wp: verifying proof_assert in creusot_test::f::{closure#0}::{closure#1} (0 contract preconditions)",
                "trust-wp: proof_assert in creusot_test::f::{closure#0}::{closure#1} verified ✓",
                "trust-wp: f verified ✓",
            ]
        )
        cov = gc.compute_goal_coverage("tests/should_succeed/closures/10_tyinv.rs", out)
        assert cov["uncovered"] == []
        without_nested = "\n".join(l for l in out.split("\n") if "{closure#1}" not in l)
        cov = gc.compute_goal_coverage("tests/should_succeed/closures/10_tyinv.rs", without_nested)
        assert {u["item"] for u in cov["uncovered"]} == {"f::{closure#0}", "f::{closure#1}"}

    def test_closure_count_mismatch_is_uncovered(self):
        gc = _load_goal_coverage()
        name = "tests/should_succeed/bug/962.rs"
        out = (
            "trust-wp: disjoint_captures verified ✓\n"
            "trust-wp: disjoint_captures::{closure#0} verified ✓\n"
            "trust-wp: disjoint_captures::{closure#1} verified ✓\n"
        )
        cov = gc.compute_goal_coverage(name, out)
        assert [u["item"] for u in cov["uncovered"]] == ["disjoint_captures::{closure#2}"]
        assert "closure pairing ambiguous" in cov["uncovered"][0]["reason"]

    def test_closure_with_negative_report_is_uncovered(self):
        gc = _load_goal_coverage()
        name = "tests/should_succeed/bug/962.rs"
        out = "trust-wp: disjoint_captures verified ✓\ntrust-wp: disjoint_captures::{closure#0} unknown (timeout)\n"
        cov = gc.compute_goal_coverage(name, out)
        assert [u["item"] for u in cov["uncovered"]] == ["disjoint_captures::{closure#2}"]

    def test_explicit_requires_false_vacuity_covers_loop_goal_only_if_coma_says_false(self):
        gc = _load_goal_coverage()
        name = "tests/should_succeed/bug/1562.rs"
        out = "trust-wp: List::<T>::foo verified ✓ (vacuous: explicit #[requires(false)])\n"
        assert gc.compute_goal_coverage(name, out)["uncovered"] == []
        # 100doors' f has no false precondition: the same detail is not loop evidence
        out = "trust-wp: f verified ✓ (vacuous: explicit #[requires(false)])\n"
        cov = gc.compute_goal_coverage("tests/should_succeed/100doors.rs", out)
        assert cov["uncovered"]

    def test_recorded_closure_08_row_is_uncovered(self):
        """F3: the credited corpus row never examined multi_use's goal."""
        gc = _load_goal_coverage()
        out = "trust-wp: multi_use::{closure#0} verified ✓\ntrust-wp: uses_fn trusted (skipped)\n"
        cov = gc.compute_goal_coverage("tests/should_succeed/closures/08_multiple_calls.rs", out)
        assert [u["item"] for u in cov["uncovered"]] == ["multi_use"]

    def test_recorded_erasure_row_leaves_overflow_items_uncovered(self):
        gc = _load_goal_coverage()
        out = "\n".join(
            [
                "trust-wp: foo3 trusted (skipped)",
                "trust-wp: test_ptr trusted (skipped)",
                "trust-wp: test_ptr2 verified ✓ (vacuous: explicit #[requires(false)])",
                "trust-wp: test_ptr_mut trusted (skipped)",
                "trust-wp: test_ptr_mut2 verified ✓ (vacuous: explicit #[requires(false)])",
                "trust-wp: specs verified ✓ (loop invariant vacuous: explicit #[requires(false)])",
            ]
        )
        cov = gc.compute_goal_coverage("tests/should_succeed/specification/erasure.rs", out)
        uncovered = {u["item"]: u for u in cov["uncovered"]}
        assert uncovered["test_foo"]["goal_kinds"] == {"overflow": 2}
        assert "test_foo2" in uncovered


class TestReviewProbesGoalCoverageGate:
    """The review's probes (F1/F2) must be REJECTED; controls stay rejected."""

    def _gate(self, tmp_path, monkeypatch, name, source, coma, **result):
        module = _load_compare_baselines()
        ref = tmp_path / "reference" / "creusot" / name
        ref.parent.mkdir(parents=True, exist_ok=True)
        ref.write_text(source)
        if coma is not None:
            ref.with_suffix(".coma").write_text(coma)
        monkeypatch.setattr(module, "REPO_ROOT", tmp_path)
        gc = _load_goal_coverage()
        base = {"name": name, "status": "pass"}
        base.update(result)
        base.setdefault("driver_report", gc.driver_report_lines(base.get("message", "")))
        return module._true_100_violation_reasons(base)

    def test_st_closure_pre_rejected(self, tmp_path, monkeypatch):
        # Creusot's coma for this probe differs from closures/08 only inside the
        # closure's precondition predicate, which does not change the inventory.
        coma = (_CORPUS_SS / "closures" / "08_multiple_calls.coma").read_text()
        reasons = self._gate(
            tmp_path,
            monkeypatch,
            "tests/should_succeed/zz_review_probe/st_closure_pre.rs",
            _ST_CLOSURE_PRE_SRC,
            coma,
            message=_ST_CLOSURE_PRE_OUT + _wire_line(verified=1, trusted=1, base_exit_code=2),
            verification_tier="tier2-source-trusted",
            trusted_def_paths=["uses_fn"],
            telemetry=_complete_telemetry(verified=1, trusted=1, base_exit_code=2),
        )
        assert any(
            r.startswith("uncovered Creusot goal item multi_use [") and "callee requires" in r
            for r in reasons
        ), reasons

    def test_st_overflow_rejected(self, tmp_path, monkeypatch):
        reasons = self._gate(
            tmp_path,
            monkeypatch,
            "tests/should_succeed/zz_review_probe/st_overflow.rs",
            _ST_OVERFLOW_SRC,
            _ST_OVERFLOW_OK_COMA + _ST_OVERFLOW_BAD_COMA,
            message=_ST_OVERFLOW_OUT + _wire_line(verified=1, trusted=1, base_exit_code=2),
            verification_tier="tier2-source-trusted",
            trusted_def_paths=["five"],
            telemetry=_complete_telemetry(verified=1, trusted=1, base_exit_code=2),
        )
        assert "uncovered Creusot goal item bad [overflow×1]: not reported by trust-wp" in reasons

    def test_source_trusted_pass_with_every_item_covered_is_accepted(self, tmp_path, monkeypatch):
        reasons = self._gate(
            tmp_path,
            monkeypatch,
            "tests/should_succeed/zz_review_probe/st_overflow_ok_only.rs",
            _ST_OVERFLOW_SRC,
            _ST_OVERFLOW_OK_COMA,
            message=_ST_OVERFLOW_OUT + _wire_line(verified=1, trusted=1, base_exit_code=2),
            verification_tier="tier2-source-trusted",
            trusted_def_paths=["five"],
            telemetry=_complete_telemetry(verified=1, trusted=1, base_exit_code=2),
        )
        assert reasons == []

    def test_st_trusted_pre_still_rejected(self, tmp_path, monkeypatch):
        out = (
            "trust-wp: id_big trusted (skipped)\n"
            "trust-wp: caller FAILED ✗ (postcondition)\n"
            "trust-wp: (1 trusted, skipped)\n"
            "trust-wp: 0 verified, 1 failed, 0 errors, 1 trusted\n"
        )
        reasons = self._gate(
            tmp_path,
            monkeypatch,
            "tests/should_succeed/zz_review_probe/st_trusted_pre.rs",
            _ST_TRUSTED_PRE_SRC,
            None,
            status="error",
            message=out + _wire_line(failed=1, trusted=1, base_exit_code=1),
            verification_tier="tier3",
            trusted_def_paths=["id_big"],
            telemetry=_complete_telemetry(failed=1, trusted=1, base_exit_code=1),
        )
        assert "status='error' (expected 'pass')" in reasons
        assert "telemetry.trusted=1" in reasons

    def test_st_control_still_rejected(self, tmp_path, monkeypatch):
        out = (
            "trust-wp: five trusted (skipped)\n"
            "trust-wp: bad FAILED ✗ (postcondition)\n"
            "trust-wp: (1 trusted, skipped)\n"
            "trust-wp: 0 verified, 1 failed, 0 errors, 1 trusted\n"
        )
        reasons = self._gate(
            tmp_path,
            monkeypatch,
            "tests/should_succeed/zz_review_probe/st_control.rs",
            _ST_CONTROL_SRC,
            None,
            status="error",
            message=out + _wire_line(failed=1, trusted=1, base_exit_code=1),
            verification_tier="tier3",
            trusted_def_paths=["five"],
            telemetry=_complete_telemetry(failed=1, trusted=1, base_exit_code=1),
        )
        assert "status='error' (expected 'pass')" in reasons

    def test_tier2_pass_without_driver_report_violates(self, tmp_path, monkeypatch):
        module = _load_compare_baselines()
        reasons = module._true_100_violation_reasons(
            {
                "name": "tests/should_succeed/100doors.rs",
                "status": "pass",
                "message": "Verification succeeded",
                "verification_tier": "tier2",
                "telemetry": _complete_telemetry(verified=1),
            }
        )
        assert "goal coverage: driver_report not recorded" in reasons

    def test_tier2_pass_without_coma_inventory_violates(self, tmp_path, monkeypatch):
        reasons = self._gate(
            tmp_path,
            monkeypatch,
            "tests/should_succeed/zz_review_probe/no_coma.rs",
            "// UISKIP\n" + _ST_OVERFLOW_SRC,
            None,
            message="trust-wp: ok verified ✓\n",
            verification_tier="tier2",
            telemetry=_complete_telemetry(verified=1),
        )
        assert "no Creusot .coma goal inventory for this test" in reasons

    def test_nonzero_base_exit_code_on_tier2_violates(self, tmp_path, monkeypatch):
        reasons = self._gate(
            tmp_path,
            monkeypatch,
            "tests/should_succeed/zz_review_probe/exit2.rs",
            _ST_OVERFLOW_SRC,
            _ST_OVERFLOW_OK_COMA,
            message="trust-wp: ok verified ✓\n",
            verification_tier="tier2",
            telemetry=_complete_telemetry(verified=1, base_exit_code=2),
        )
        assert "telemetry.base_exit_code=2 on a pass" in reasons

    def test_source_trusted_exit_code_exemption_requires_only_trusted(self, tmp_path, monkeypatch):
        module = _load_compare_baselines()
        tel = _complete_telemetry(verified=1, trusted=1, base_exit_code=2, warnings=1)
        assert module._base_exit_code_reasons({"telemetry": tel}, True) == [
            "telemetry.base_exit_code=2 on a pass"
        ]
        tel = _complete_telemetry(verified=1, trusted=1, base_exit_code=2)
        assert module._base_exit_code_reasons({"telemetry": tel}, True) == []
        assert module._base_exit_code_reasons({"telemetry": tel}, False) == [
            "telemetry.base_exit_code=2 on a pass"
        ]
        tel = _complete_telemetry(verified=1, trusted=1, base_exit_code=101)
        assert module._base_exit_code_reasons({"telemetry": tel}, True)

    def test_source_trusted_exit_code_exemption_reads_a_verified_assertion(self):
        # bug/negative_int_pats: its `f` states no contract and proves seven
        # assertions beside the source's `#[trusted] any`. A verified assertion
        # is the verified evidence; a trusted item with nothing verified is not.
        module = _load_compare_baselines()
        tel = _complete_telemetry(proof_assert_verified=7, trusted=1, base_exit_code=2)
        assert module._base_exit_code_reasons({"telemetry": tel}, True) == []
        tel = _complete_telemetry(trusted=1, base_exit_code=2)
        assert module._base_exit_code_reasons({"telemetry": tel}, True) == [
            "telemetry.base_exit_code=2 on a pass"
        ]
        tel = _complete_telemetry(
            proof_assert_verified=7, proof_assert_failed=1, trusted=1, base_exit_code=2
        )
        assert module._base_exit_code_reasons({"telemetry": tel}, True) == [
            "telemetry.base_exit_code=2 on a pass"
        ]


# ---------------------------------------------------------------------------
# Goal-coverage tightening (review notes N1-N3 on the goal-coverage gate).
# Each "loose" case below must be uncovered; the controls must stay covered.
# ---------------------------------------------------------------------------


def _goal_module(name: str, comment: str | None = None, fn: str = "m") -> str:
    header = f"module {name}" + (f" (* {comment} *)" if comment else "")
    return (
        f"{header}\n"
        "  use creusot.prelude.Any\n"
        "  \n"
        f"  let rec {fn} (return (x: bool)) = (! bb0\n"
        "    [ bb0 = s0 [ s0 = return {_ret} ] ]\n"
        "    [ & _ret: bool = Any.any_l () ])\n"
        f"    [ return (result: bool) -> {{[@stop_split] [@expl:{fn} ensures] result}} (! return {{result}}) ]\n"
        "end\n"
    )


def _synthetic_coverage(tmp_path, modules, out):
    gc = _load_goal_coverage()
    name = "tests/should_succeed/zz_tighten/synthetic.rs"
    coma = tmp_path / name[:-3]
    coma = coma.with_suffix(".coma")
    coma.parent.mkdir(parents=True, exist_ok=True)
    coma.write_text("\n".join(modules))
    cov = gc.compute_goal_coverage(name, out, corpus_root=tmp_path)
    return {c["item"] for c in cov["covered"]}, {u["item"]: u["reason"] for u in cov["uncovered"]}


class TestGoalCoverageSelfTypeExact:
    """N1: impl self types and trait names are matched exactly."""

    def test_generic_args_distinguish_impls(self, tmp_path):
        covered, uncovered = _synthetic_coverage(
            tmp_path,
            [
                _goal_module("M_impl_Tr_for_Foo_A__m", "<Foo<A> as Tr>"),
                _goal_module("M_impl_Tr_for_Foo_B__m", "<Foo<B> as Tr>"),
                _goal_module("M_impl_Tr_for_Foo_bar__m", "<Foo_bar as Tr>"),
            ],
            "trust-wp: <Foo<A> as Tr>::m verified ✓\n",
        )
        assert covered == {"impl_Tr_for_Foo_A::m"}
        assert set(uncovered) == {"impl_Tr_for_Foo_B::m", "impl_Tr_for_Foo_bar::m"}

    def test_reference_pointee_is_compared(self, tmp_path):
        covered, uncovered = _synthetic_coverage(
            tmp_path,
            [_goal_module("M_impl_Tr_for_ref_Bar__m", "<&Bar as Tr>")],
            "trust-wp: <&Foo as Tr>::m verified ✓\n",
        )
        assert not covered and set(uncovered) == {"impl_Tr_for_ref_Bar::m"}

    def test_trait_name_is_exact(self, tmp_path):
        covered, uncovered = _synthetic_coverage(
            tmp_path,
            [_goal_module("M_impl_Tr_Ext_for_Foo__m", "<Foo as Tr_Ext>")],
            "trust-wp: <Foo as Tr>::m verified ✓\n",
        )
        assert not covered and set(uncovered) == {"impl_Tr_Ext_for_Foo::m"}

    def test_trait_args_compared_through_the_module_comment(self, tmp_path):
        # Creusot drops trait args from the module name; its header comment keeps them.
        covered, _ = _synthetic_coverage(
            tmp_path,
            [_goal_module("M_impl_Tr_for_S__m", "<S as Tr<u8>>")],
            "trust-wp: <S as Tr<u16>>::m verified ✓\n",
        )
        assert not covered
        covered, _ = _synthetic_coverage(
            tmp_path,
            [_goal_module("M_impl_Tr_for_S__m", "<S as Tr<u8>>")],
            "trust-wp: <S as Tr<u8>>::m verified ✓\n",
        )
        assert covered == {"impl_Tr_for_S::m"}

    def test_ambiguous_report_covers_none(self, tmp_path):
        # two inherent impls whose flattened names differ only by Creusot's
        # ``_N`` disambiguator: a path matching both covers neither
        covered, uncovered = _synthetic_coverage(
            tmp_path,
            [
                _goal_module("M_impl_Memory__m", "Memory"),
                _goal_module("M_impl_Memory_0__m", "Memory"),
            ],
            "trust-wp: Memory::m verified ✓\n",
        )
        assert not covered
        assert all("ambiguous" in why for why in uncovered.values()), uncovered

    def test_own_result_ref_does_not_cover_refmut(self):
        gc = _load_goal_coverage()
        out = "trust-wp: OwnResult::<&T, E>::copied verified ✓\ntrust-wp: OwnResult::<&T, E>::cloned verified ✓\n"
        cov = gc.compute_goal_coverage("tests/should_succeed/result/own.rs", out)
        covered = {c["item"] for c in cov["covered"]}
        assert covered == {"impl_OwnResult_ref_T_E::copied", "impl_OwnResult_ref_T_E::cloned"}

    @pytest.mark.parametrize(
        "module,path,expected",
        [
            ("M_impl_Tr_for_Foo_A__m", "<Foo<A> as Tr>::m", True),
            ("M_impl_Tr_for_Foo_A__m", "<Foo<B> as Tr>::m", False),
            ("M_impl_Tr_for_Foo_A__m", "<Foo as Tr>::m", False),
            ("M_impl_Tr_for_Foo_bar__m", "<Foo<A> as Tr>::m", False),
            ("M_impl_Tr_Ext_for_Foo_A__m", "<Foo<A> as Tr>::m", False),
            ("M_impl_Model_for_ref_T__model", "<&Bar as Model>::model", False),
            ("M_impl_Model_for_ref_T__model", "<&mut T as Model>::model", False),
            ("M_impl_OwnResult_refmut_T_E__copied", "OwnResult::<&T, E>::copied", False),
            ("M_impl_OwnResult_refmut_T_E__copied", "OwnResult::<&mut T, E>::copied", True),
            ("M_impl_OwnResult_Option_T_E__transpose", "OwnResult::<std::option::Option<T>, E>::transpose", True),
            ("M_impl_FakeFnOnce_for_AddsTwo__call", "<AddsTwo<'a> as FakeFnOnce>::call", True),
            ("M_impl_MyHashMap_K_V_0__new", "MyHashMap::<K, V>::new", True),
            ("M_impl_MyHashMap_K_V_0__new", "MyHashMap::<K>::new", False),
            ("M_impl_Foo_for_unit__g", "<() as Foo>::g", True),
            ("M_impl_T_for_tup2_T1_T2__x", "<(T1, T2) as T<B>>::x", True),
            ("M_impl_T_for_tup2_T1_T2__x", "<(T1, T3) as T<B>>::x", False),
        ],
    )
    def test_exact_mapping(self, module, path, expected):
        gc = _load_goal_coverage()
        from collections import Counter

        item = gc.GoalItem(module, gc.module_item_name(module), None, False, [], Counter(x=1))
        assert gc.coma_item_matches_path(item, path) is expected

    def test_corpus_controls_stay_covered(self):
        gc = _load_goal_coverage()
        cov = gc.compute_goal_coverage(
            "tests/should_succeed/hashmap_list.rs", "trust-wp: MyHashMap::<K, V>::new verified ✓\n"
        )
        assert "impl_MyHashMap_K_V_0::new" in {c["item"] for c in cov["covered"]}
        cov = gc.compute_goal_coverage(
            "tests/should_succeed/traits/18_trait_laws.rs",
            "trust-wp: <() as Symmetric>::reflexive verified ✓\n",
        )
        assert "impl_Symmetric_for_unit::reflexive" in {c["item"] for c in cov["covered"]}


_DOORS_OK = "trust-wp: f verified ✓ (loop invariant)\n"


class TestGoalCoverageUnrecognisedLinesAreNegative:
    """N2: every non-positive per-item line is negative; summaries are excluded explicitly."""

    @pytest.mark.parametrize(
        "line",
        [
            "trust-wp: f evidence gap (loop invariant: no certificate)",
            "trust-wp: f postcondition evidence gap (withheld)",
            "trust-wp: f panicked during verification: boom",
            "trust-wp: f panicked during proof_assert: boom",
            "trust-wp: f ay solver panic during verification: boom",
            "trust-wp: f unverified (termination — structural variant decrease lacks solver evidence)",
            "trust-wp: f trait refinement ASSUMED (not proven) (#2121)",
            "trust-wp: f loop induction verified ✓, postcondition incomplete (proof-trusted) — deferring to function-level path",
            "trust-wp: f error while verifying loop call obligations: x",
            "trust-wp: f some status nobody has seen before",
            "trust-wp: warning: f: MIR context extraction failed: detail",
            "trust-wp:   (proof_assert in creusot_test::f: MIR body extraction failed, using preconditions only)",
            "trust-wp: note: recursive logic function `creusot_test::f` has no #[variant(...)]; recursion accepted without termination proof",
            "trust-wp: f verified ✓ (a detail the gate does not know)",
        ],
    )
    def test_item_line_is_negative(self, line):
        gc = _load_goal_coverage()
        cov = gc.compute_goal_coverage("tests/should_succeed/100doors.rs", _DOORS_OK + line + "\n")
        assert [u["item"] for u in cov["uncovered"]] == ["f"], cov

    @pytest.mark.parametrize(
        "line",
        [
            "trust-wp: 1 proof_assert assumption(s) injected without proof",
            "trust-wp: 1 logic function postcondition(s) unverified — callers may depend on unproven axioms",
            "trust-wp: warning: all 3 function(s) assumed without SMT proof — no contracts were verified",
            "trust-wp: error: failed to parse proof_assert 'x > 0': bad",
            "trust-wp: warning: failed to parse ensures 'x': bad",
            "trust-wp: (a crate-level line nobody has seen before)",
        ],
    )
    def test_crate_level_negative_uncovers_everything(self, line):
        gc = _load_goal_coverage()
        cov = gc.compute_goal_coverage("tests/should_succeed/100doors.rs", _DOORS_OK + line + "\n")
        assert [u["item"] for u in cov["uncovered"]] == ["f"], cov

    def test_termination_only_verdict_does_not_cover(self):
        gc = _load_goal_coverage()
        cov = gc.compute_goal_coverage("tests/should_succeed/100doors.rs", "trust-wp: f verified ✓ (termination)\n")
        assert cov["uncovered"]

    def test_summaries_and_announcements_are_excluded(self):
        gc = _load_goal_coverage()
        out = _DOORS_OK + "\n".join(
            [
                "trust-wp: g is a logic function (postcondition will be verified)",
                "trust-wp: <Q as creusot_std::Invariant>::invariant is a logic function (definition registered)",
                "trust-wp: f loop invariant + call obligations verified ✓ — continuing to post-loop verification",
                "trust-wp: stopping remaining contract verification after first adaptive-budget failure/error (#3771)",
                "trust-wp:   (proof_assert: 2 closure existential enrichment(s) applied)",
                "trust-wp: (1 trusted, skipped)",
                "trust-wp: 1 verified, 0 failed, 0 errors, 1 trusted",
                "trust-wp: proof_assert: 0 verified, 0 failed, 0 errors",
                "",
            ]
        )
        assert gc.compute_goal_coverage("tests/should_succeed/100doors.rs", out)["uncovered"] == []


class TestGoalCoverageTraitLogicGrantLines:
    """The discharge of a trait logic method's grant (D-110) is announced per
    impl; it is not a Creusot goal, so it neither covers nor uncovers one."""

    NAME = "tests/should_succeed/bug/464.rs"  # impl invariant [logic goal, postcondition] + refines
    OWN = (
        "trust-wp: creusot_test::<Struct as Trait>::invariant verified \u2713\n"
        "trust-wp: <Struct as Trait>::invariant refinement verified \u2713\n"
    )
    GRANT = (
        "trust-wp: creusot_test::Trait::invariant is a trait logic method declaration "
        "(postcondition owed by each implementation)\n"
        "trust-wp: <Struct as Trait>::invariant establishes the postcondition of trait logic "
        "method `Trait::invariant`\n"
    )

    def test_the_grant_lines_beside_the_item_s_own_verdicts_cover_it(self):
        gc = _load_goal_coverage()
        assert gc.compute_goal_coverage(self.NAME, self.OWN)["uncovered"] == []
        assert gc.compute_goal_coverage(self.NAME, self.GRANT + self.OWN)["uncovered"] == []

    def test_the_grant_lines_alone_cover_nothing(self):
        gc = _load_goal_coverage()
        uncovered = gc.compute_goal_coverage(self.NAME, self.GRANT)["uncovered"]
        assert {u["item"] for u in uncovered} == {
            "impl_Trait_for_Struct::invariant",
            "impl_Trait_for_Struct::invariant refinement",
        }, uncovered

    def test_a_grant_the_impl_does_not_discharge_uncovers_it(self):
        gc = _load_goal_coverage()
        failed = (
            "trust-wp: <Struct as Trait>::invariant unknown (postcondition of trait logic "
            "method `Trait::invariant` not proved)\n"
        )
        uncovered = gc.compute_goal_coverage(self.NAME, self.OWN + failed)["uncovered"]
        assert "impl_Trait_for_Struct::invariant" in {u["item"] for u in uncovered}, uncovered


class TestGoalCoverageAssertionCounts:
    """N3: proof_assert verdicts are counted per item against Creusot's assertion goals."""

    @staticmethod
    def _pa(fn, n, verified=None):
        verified = n if verified is None else verified
        lines = [f"trust-wp: verifying proof_assert in creusot_test::{fn} (0 contract preconditions)"] * n
        lines += [f"trust-wp: proof_assert in creusot_test::{fn} verified ✓"] * verified
        return "\n".join(lines) + "\n"

    def test_assertion_only_item_needs_every_assertion(self):
        gc = _load_goal_coverage()
        name = "tests/should_succeed/bug/1674.rs"  # f: 2 assertions
        assert gc.compute_goal_coverage(name, self._pa("f", 1))["uncovered"]
        assert gc.compute_goal_coverage(name, self._pa("f", 3))["uncovered"]
        assert gc.compute_goal_coverage(name, self._pa("f", 2, verified=1))["uncovered"]
        assert gc.compute_goal_coverage(name, self._pa("f", 2))["uncovered"] == []

    def test_mixed_item_needs_its_proof_asserts_too(self):
        gc = _load_goal_coverage()
        name = "tests/should_succeed/bug/463.rs"  # test: assertion 1 + callee requires 1
        closure = "trust-wp: test::{closure#0} verified ✓\n"
        cov = gc.compute_goal_coverage(name, closure + "trust-wp: test verified ✓\n")
        uncovered = {u["item"]: u["reason"] for u in cov["uncovered"]}
        assert set(uncovered) == {"test"} and "proof_assert count" in uncovered["test"], uncovered
        ok = closure + "trust-wp: test verified ✓\n" + self._pa("test", 1)
        assert gc.compute_goal_coverage(name, ok)["uncovered"] == []

    def test_closure_assertions_count_across_the_module(self):
        gc = _load_goal_coverage()
        full = "\n".join(
            [
                "trust-wp: f::{closure#0} verified ✓",
                "trust-wp: verifying proof_assert in creusot_test::f::{closure#0} (0 contract preconditions)",
                "trust-wp: proof_assert in creusot_test::f::{closure#0} verified ✓",
                "trust-wp: f::{closure#0}::{closure#1} verified ✓",
                "trust-wp: verifying proof_assert in creusot_test::f::{closure#0}::{closure#1} (0 contract preconditions)",
                "trust-wp: proof_assert in creusot_test::f::{closure#0}::{closure#1} verified ✓",
                "trust-wp: f verified ✓",
            ]
        )
        name = "tests/should_succeed/closures/10_tyinv.rs"
        assert gc.compute_goal_coverage(name, full)["uncovered"] == []
        missing = "\n".join(l for l in full.split("\n") if l != "trust-wp: proof_assert in creusot_test::f::{closure#0}::{closure#1} verified ✓")
        cov = gc.compute_goal_coverage(name, missing)
        assert {u["item"] for u in cov["uncovered"]} == {"f::{closure#0}", "f::{closure#1}"}


def test_goal_coverage_numeric_suffix_is_not_a_disambiguation_of_an_exact_module():
    """lang/const: ``fn add_one`` and ``fn add_one_2``; ``add_one`` must not
    also denote M_add_one_2 (neither widening nor a spurious ambiguity)."""
    gc = _load_goal_coverage()
    name = "tests/should_succeed/lang/const.rs"
    only_add_one = gc.compute_goal_coverage(name, "trust-wp: add_one verified ✓\n")
    covered = {c["item"] for c in only_add_one["covered"]}
    assert "add_one" in covered and "add_one_2" not in covered


# ---------------------------------------------------------------------------
# should_fail validated-refutation rule over STORED driver outputs (D-28)
# ---------------------------------------------------------------------------

_SF_REFUTATION_FIXTURES = HARNESS_DIR / "fixtures" / "should_fail_refutation"

# Rows whose stored output carries ONLY an unvalidated FAILED ✗ / failed
# counter (ay_result=trust-wp-structural-provenance, sat model_validated=false,
# or none/unknown). Each must be ``unknown`` — never a credited rejection.
_SF_UNVALIDATED_ONLY = (
    "alloc_max_size",
    "bug/222",
    "bug/436_0",
    "bug/492",
    "bug/692",
    "bug/695",
    "bug/specialize",
    "const_default",
    "final_borrows",
    "lints/contractless_external_function",
    "opaque_unproveable",
    "type_invariants/partial_instance",
    "unsound_dyn",
)

# Credited by a validated model (ay_result=sat model_validated=true) matching
# a counted failure: must stay pass with the named credit.
_SF_VALIDATED = {
    "bug/878": "validated counterexample: creusot_test::test proof_assert",
    "impl_trait": "validated counterexample: creusot_test::main proof_assert",
    "terminates/incorrect_variant": (
        "validated counterexample: incorrect_recursion::variant_decrease[1] "
        "recursive_variant"
    ),
    "bug/01_resolve_unsoundness": (
        "validated counterexample: make_vec_of_size loop_preservation"
    ),
    "bug/869": "validated counterexample: creusot_test::unsound proof_assert",
    "terminates/invalid_variant_type": "validated counterexample: foo loop_variant_nonneg",
    "traits/17_impl_refinement": (
        "validated counterexample: <() as ReqFalse>::need_false::trait precondition "
        "implies impl precondition trait_refinement"
    ),
    "type_invariants/borrows": "validated counterexample: NonZero::new function_contract",
    "zst": "validated counterexample: creusot_test::zst_pointers_may_be_equal proof_assert",
}


def _load_sf_refutation_fixture(stem: str) -> dict:
    path = _SF_REFUTATION_FIXTURES / (stem.replace("/", "__") + ".json")
    return json.loads(path.read_text(encoding="utf-8"))


def _classify_sf_fixture(stem: str):
    fixture = _load_sf_refutation_fixture(stem)
    assert fixture["name"] == f"tests/should_fail/{stem}.rs"
    return harness.classify_should_fail_result_with_credit(
        fixture["exit_code"] == 0,
        fixture["output"],
        fixture["source"],
        fixture["name"],
        exit_code=fixture["exit_code"],
    )


class TestShouldFailValidatedRefutationFixtures:
    @pytest.mark.parametrize("stem", _SF_UNVALIDATED_ONLY)
    def test_unvalidated_failed_is_not_a_rejection(self, stem):
        assert _classify_sf_fixture(stem) == ("unknown", None, None)

    @pytest.mark.parametrize("stem", sorted(_SF_VALIDATED))
    def test_validated_refutation_stays_credited(self, stem):
        assert _classify_sf_fixture(stem) == ("pass", None, _SF_VALIDATED[stem])

    def test_frontend_refusal_stays_credited(self):
        assert _classify_sf_fixture("ghost/non_ghost") == (
            "pass",
            None,
            "frontend: called non-ghost function ... in ghost context",
        )

    def test_fixture_set_is_exactly_the_audited_rows(self):
        stems = {
            p.stem.replace("__", "/") for p in _SF_REFUTATION_FIXTURES.glob("*.json")
        }
        assert stems == set(_SF_UNVALIDATED_ONLY) | set(_SF_VALIDATED) | {
            "ghost/non_ghost"
        }


# ---------------------------------------------------------------------------
# Triage family "no item-level verified report": P3 (NO_REPLAY translate-only
# coverage-inventory exemption, never a tier upgrade) and P4 (status-level
# lenient passes). Replays of the stored lane outputs are RED before the fix.
# ---------------------------------------------------------------------------

_LOGIC_VCGEN_OUTPUT = (
    "trust-wp: creusot_test::bor_1_2 verified ✓\n"
    "trust-wp: creusot_test::f postcondition FAILED (logic postcondition)\n"
    "trust-wp: creusot_test::g postcondition unverified (body contains parameterized closure — #985)\n"
    "trust-wp: 2 logic function postcondition(s) unverified — callers may depend on unproven axioms\n"
    "trust-wp: 1 verified, 0 failed, 0 errors, 2 unverified axiom(s), 2 warnings\n"
    + _wire_line(base_exit_code=2, verified=1, warnings=2, unverified_axioms=2)
)
_TRAIT_LAWS_OUTPUT = (
    "trust-wp: creusot_test::uses_op postcondition FAILED (logic postcondition)\n"
    "trust-wp: creusot_test::<() as Symmetric>::reflexive law postcondition unverified (non-strict axiom exposure)\n"
    "trust-wp: creusot_test::impl_laws verified ✓\n"
    "trust-wp: 1 verified, 0 failed, 0 errors, 2 unverified axiom(s), 2 warnings\n"
    + _wire_line(base_exit_code=2, verified=1, warnings=2, unverified_axioms=2)
)


def _closures11_output(base_exit_code: int, trusted: int) -> str:
    return (
        "trust-wp: captures_and_call::{closure#0} verified ✓\n"
        "trust-wp: proof_assert in creusot_test::captures_and_call::{closure#0} verified ✓\n"
        "trust-wp: proof_assert in creusot_test::captures_and_call inconclusive (incomplete) — function has no contracts\n"
        f"trust-wp: 3 verified, 0 failed, 0 errors{', 1 trusted' if trusted else ''}\n"
        "trust-wp: proof_assert: 5 verified, 0 failed, 0 errors, 1 inconclusive\n"
        + _wire_line(
            base_exit_code=base_exit_code,
            verified=3,
            trusted=trusted,
            proof_assert_verified=5,
            proof_assert_inconclusive=1,
        )
    )


def _corpus_source(name: str) -> str:
    return (WORKSPACE_ROOT / "reference" / "creusot" / name).read_text()


class TestP4LenientPassHardening:
    def test_logic_postcondition_failed_is_not_a_pass(self):
        from harness_classify_succeed import classify_failure

        name = "tests/should_succeed/lang/logic_vcgen.rs"
        status, _ = classify_failure(_LOGIC_VCGEN_OUTPUT, _corpus_source(name), 2, name)
        assert status == "unknown"

    def test_trait_law_logic_postcondition_failed_is_not_a_pass(self):
        from harness_classify_succeed import classify_failure

        name = "tests/should_succeed/traits/18_trait_laws.rs"
        status, _ = classify_failure(_TRAIT_LAWS_OUTPUT, _corpus_source(name), 2, name)
        assert status == "unknown"

    def test_proof_assert_inconclusive_blocks_gap_only_exit(self):
        from harness_classify_succeed import _is_soundness_gap_only_exit

        assert not _is_soundness_gap_only_exit(_closures11_output(2, 1), 2)
        # control: the same shape without the inconclusive counter qualifies
        clean = _closures11_output(2, 1).replace("proof_assert_inconclusive=1", "proof_assert_inconclusive=0")
        assert _is_soundness_gap_only_exit(clean, 2)

    def test_closures11_stored_shape_is_not_a_pass(self):
        from harness_classify_succeed import classify_failure

        name = "tests/should_succeed/closures/11_proof_assert_in_closure.rs"
        status, _ = classify_failure(_closures11_output(2, 1), _corpus_source(name), 2, name)
        assert status != "pass"

    def test_inconclusive_only_wire_line_on_clean_exit_is_unknown(self):
        from harness_classify_signals import _wire_line_shows_pa_only_failure
        from harness_classify_succeed import classify_failure

        output = _closures11_output(0, 0)
        assert _wire_line_shows_pa_only_failure(output)
        name = "tests/should_succeed/closures/11_proof_assert_in_closure.rs"
        assert classify_failure(output, _corpus_source(name), 0, name) == ("unknown", None)

    def test_proof_assert_failure_still_fails(self):
        from harness_classify_succeed import classify_failure

        output = _closures11_output(0, 0).replace("proof_assert_failed=0", "proof_assert_failed=1")
        name = "tests/should_succeed/closures/11_proof_assert_in_closure.rs"
        assert classify_failure(output, _corpus_source(name), 0, name)[0] == "fail"

    @pytest.mark.parametrize(
        "line",
        [
            "trust-wp: creusot_test::f postcondition FAILED (logic postcondition)",
            "trust-wp: creusot_test::<() as Symmetric>::reflexive law postcondition unverified (x)",
        ],
    )
    def test_tier_markers_do_not_need_the_axiom_summary(self, line):
        from harness_verification_tier import _has_fail_closed_trust_or_axiom_marker

        assert _has_fail_closed_trust_or_axiom_marker(line + "\ntrust-wp: 1 verified, 0 failed, 0 errors\n")

    def test_tier_marker_control(self):
        from harness_verification_tier import _has_fail_closed_trust_or_axiom_marker

        assert not _has_fail_closed_trust_or_axiom_marker(
            "trust-wp: creusot_test::f verified ✓\ntrust-wp: 1 verified, 0 failed, 0 errors\n"
        )


class TestP3NoReplayCoverageExemption:
    FAILED_653 = "trust-wp: omg FAILED ✗ (postcondition)\n"

    @pytest.mark.parametrize(
        "name",
        [
            "tests/should_succeed/bug/653.rs",
            "tests/should_succeed/spec_tests.rs",
            "tests/should_succeed/syntax/05_pearlite.rs",
        ],
    )
    def test_allowlisted_rows_are_exempt_but_never_proof_grade(self, name):
        gc = _load_goal_coverage()
        cov = gc.compute_goal_coverage(name, self.FAILED_653)
        assert cov["inventory"] == gc.NO_REPLAY_EXEMPT_INVENTORY
        assert cov["covered"] == [] and cov["uncovered"] == []
        assert cov["not_discharged_by_creusot"], cov
        assert all(e["reason"] == gc.NO_REPLAY_EXEMPT_REASON for e in cov["not_discharged_by_creusot"])
        assert gc.goal_coverage_violations(cov), "the exemption must never clear the gate"

    def test_gate_refuses_tier2_on_an_exempt_row(self):
        module = _load_compare_baselines()
        reasons = module.goal_coverage_reasons(
            {
                "name": "tests/should_succeed/bug/653.rs",
                "driver_report": ["trust-wp: omg verified ✓"],
                "telemetry": _complete_telemetry(verified=1),
            }
        )
        assert any("NO_REPLAY translate-only" in r for r in reasons), reasons

    def test_non_allowlisted_no_replay_row_keeps_full_inventory(self):
        gc = _load_goal_coverage()
        cov = gc.compute_goal_coverage("tests/should_succeed/bug/387.rs", "")
        assert cov["inventory"] == "coma"
        assert cov["uncovered"], "bug/387 has Creusot goals and must stay inventoried"

    def test_exemption_is_exact_path_and_requires_marker(self, tmp_path):
        gc = _load_goal_coverage()
        src = _corpus_source("tests/should_succeed/bug/653.rs")
        coma = (WORKSPACE_ROOT / "reference/creusot/tests/should_succeed/bug/653.coma").read_text()
        # same file under a longer path: not exempt
        for rel in ("tests/should_succeed/x/bug/653", "tests/should_succeed/bug/6530"):
            (tmp_path / rel).parent.mkdir(parents=True, exist_ok=True)
            (tmp_path / f"{rel}.rs").write_text(src)
            (tmp_path / f"{rel}.coma").write_text(coma)
            assert not gc.is_no_replay_translate_only_exempt(f"{rel}.rs", tmp_path)
            assert gc.compute_goal_coverage(f"{rel}.rs", "", corpus_root=tmp_path)["inventory"] == "coma"
        # allowlisted path without the NO_REPLAY marker: not exempt
        rel = "tests/should_succeed/bug/653"
        (tmp_path / rel).parent.mkdir(parents=True, exist_ok=True)
        (tmp_path / f"{rel}.rs").write_text(src.replace("NO_REPLAY", "REPLAY"))
        (tmp_path / f"{rel}.coma").write_text(coma)
        assert not gc.is_no_replay_translate_only_exempt(f"{rel}.rs", tmp_path)
        cov = gc.compute_goal_coverage(f"{rel}.rs", "", corpus_root=tmp_path)
        assert cov["inventory"] == "coma" and cov["uncovered"]

    def test_non_coma_inventory_is_a_violation(self):
        gc = _load_goal_coverage()
        assert gc.goal_coverage_violations({"inventory": "error", "covered": [], "uncovered": []})

    def test_coverage_allowlist_matches_classifier_allowlist(self):
        gc = _load_goal_coverage()
        assert tuple(gc.NO_REPLAY_TRANSLATE_ONLY_ALLOWLIST) == tuple(
            harness.harness_classify._NO_REPLAY_TRANSLATE_ONLY_ALLOWLIST
        )


# ---------------------------------------------------------------------------
# NO_REPLAY credit policy (D-21)
# ---------------------------------------------------------------------------

_NO_REPLAY_CORPUS_TESTS = (
    "bug/387",
    "bug/511",
    "bug/653",
    "closures/01_basic",
    "closures/03_generic_bound",
    "closures/04_generic_closure",
    "closures/05_map",
    "lang/float_ops",
    "spec_tests",
    "syntax/04_assoc_prec",
    "syntax/05_pearlite",
    "syntax/10_mutual_rec_types",
    "traits/04",
)
# Every goal (B) unprovable or (C) contentless.
_NO_REPLAY_ELIGIBLE = ("bug/653", "spec_tests", "bug/511", "syntax/05_pearlite")
# At least one (A) provable goal: never translate-only.
_NO_REPLAY_A_GOAL = tuple(t for t in _NO_REPLAY_CORPUS_TESTS if t not in _NO_REPLAY_ELIGIBLE)
_DIRTY_FRONTEND_COUNTERS = (
    "panics",
    "parse_errors",
    "termination_errors",
    "logic_recursion_errors",
    "erasure_errors",
)


def _ss(name: str) -> str:
    return f"tests/should_succeed/{name}.rs"


class TestNoReplayCreditPolicy:
    """Pins the per-test NO_REPLAY credit decision (D-21)."""

    def test_policy_covers_exactly_the_no_replay_corpus(self):
        base = WORKSPACE_ROOT / "reference/creusot/tests/should_succeed"
        found = sorted(
            str(p.relative_to(base))[: -len(".rs")]
            for p in base.rglob("*.rs")
            if re.search(r"//\s*NO_REPLAY", p.read_text(encoding="utf-8", errors="replace"))
        )
        # A new NO_REPLAY corpus test forces an explicit per-goal decision.
        assert found == sorted(_NO_REPLAY_CORPUS_TESTS)

    def test_allowlists_are_exactly_the_eligible_tests(self):
        gc = _load_goal_coverage()
        cb = _load_compare_baselines()
        assert set(harness.harness_classify._NO_REPLAY_TRANSLATE_ONLY_ALLOWLIST) == set(_NO_REPLAY_ELIGIBLE)
        assert tuple(gc.NO_REPLAY_TRANSLATE_ONLY_ALLOWLIST) == tuple(
            harness.harness_classify._NO_REPLAY_TRANSLATE_ONLY_ALLOWLIST
        )
        assert tuple(cb.NO_REPLAY_TRANSLATE_ONLY_ALLOWLIST) == tuple(gc.NO_REPLAY_TRANSLATE_ONLY_ALLOWLIST)

    @pytest.mark.parametrize("name", _NO_REPLAY_ELIGIBLE)
    def test_eligible_is_credited_translate_only_with_clean_frontend(self, name):
        output = "trust-wp: f FAILED ✗\n" + _wire_line(failed=1, base_exit_code=1)
        status, _skip, mode = harness.classify_no_replay_result_with_mode(
            output, exit_code=1, test_name=_ss(name)
        )
        assert (status, mode) == ("pass", "translate_only")

    @pytest.mark.parametrize("counter", _DIRTY_FRONTEND_COUNTERS)
    @pytest.mark.parametrize("name", _NO_REPLAY_ELIGIBLE)
    def test_eligible_is_not_credited_with_dirty_frontend(self, name, counter):
        output = _wire_line(failed=1, base_exit_code=1, **{counter: 1})
        status, _skip = harness.classify_no_replay_result(output, exit_code=1, test_name=_ss(name))
        assert status != "pass"

    @pytest.mark.parametrize("name", _NO_REPLAY_ELIGIBLE)
    def test_eligible_is_not_credited_without_wire_line(self, name):
        status, _skip = harness.classify_no_replay_result(
            "trust-wp: f FAILED ✗\n", exit_code=1, test_name=_ss(name)
        )
        assert status != "pass"

    @pytest.mark.parametrize("name", _NO_REPLAY_A_GOAL)
    @pytest.mark.parametrize(
        "output,exit_code",
        [
            (_wire_line(failed=1, base_exit_code=1), 1),  # refuted
            (_wire_line(base_exit_code=2), 2),  # examined nothing
            (_wire_line(), 0),  # clean exit, verified nothing
            (_wire_line(verified=1, trusted=1), 0),  # proof rests on trust
            (_wire_line(errors=1, demoted=1, base_exit_code=2), 2),  # unknown
        ],
    )
    def test_a_goal_test_is_never_credited_translate_only(self, name, output, exit_code):
        status, _skip, mode = harness.classify_no_replay_result_with_mode(
            output, exit_code=exit_code, test_name=_ss(name)
        )
        assert status != "pass" and mode is None

    @pytest.mark.parametrize("name", _NO_REPLAY_A_GOAL)
    def test_a_goal_test_parse_only_row_violates_gate_and_keeps_inventory(self, name):
        cb = _load_compare_baselines()
        gc = _load_goal_coverage()
        reasons = cb._true_100_violation_reasons(
            {
                "name": _ss(name),
                "status": "pass",
                "message": "Parse-only (NO_REPLAY): syntax-only test",
                "verification_tier": "tier3",
                "telemetry": _complete_telemetry(),
            }
        )
        assert "NO_REPLAY parse-only pass" in reasons
        assert not gc.is_no_replay_translate_only_exempt(_ss(name))
        assert gc.compute_goal_coverage(_ss(name), "")["inventory"] == "coma"

    @pytest.mark.parametrize("name", _NO_REPLAY_A_GOAL)
    def test_a_goal_test_can_still_earn_a_verified_pass(self, name):
        output = "trust-wp: f verified ✓\n" + _wire_line(verified=1)
        status, _skip, mode = harness.classify_no_replay_result_with_mode(
            output, exit_code=0, test_name=_ss(name)
        )
        assert (status, mode) == ("pass", "verified")

    @pytest.mark.parametrize(
        "name",
        [
            "tests/should_succeed/bug/6530.rs",
            "tests/should_succeed/bug/653_x.rs",
            "tests/should_succeed/spec_tests_2.rs",
            "tests/should_succeed/syntax/05_pearlite2.rs",
            "tests/should_succeed/x/bug/653.rs",
            "tests/should_succeed/x/spec_tests.rs",
            "tests/should_fail/bug/653.rs",
            "tests/should_fail/spec_tests.rs",
            "bug/653.rs",
            "spec_tests.rs",
        ],
    )
    def test_same_name_prefix_is_never_credited(self, name):
        output = "trust-wp: f FAILED ✗\n" + _wire_line(failed=1, base_exit_code=1)
        status, _skip = harness.classify_no_replay_result(output, exit_code=1, test_name=name)
        assert status != "pass"
        cb = _load_compare_baselines()
        assert not cb._is_translate_only_allowed(name)
        reasons = cb._true_100_violation_reasons(
            {
                "name": name,
                "status": "pass",
                "message": "Parse-only (NO_REPLAY): syntax-only test",
                "verification_tier": "tier3",
                "telemetry": _complete_telemetry(failed=1, base_exit_code=1),
            }
        )
        assert "NO_REPLAY parse-only pass" in reasons

    def test_non_no_replay_source_under_allowlisted_name_is_never_credited(self, tmp_path):
        # Runner: without the marker the NO_REPLAY classifier is not reached and
        # a refuted run is not a pass.
        output = "trust-wp: omg FAILED ✗ (postcondition)\n" + _wire_line(failed=1, base_exit_code=1)
        source = _corpus_source(_ss("bug/653")).replace("NO_REPLAY", "REPLAY")
        status, _message, *_rest = harness_runner._classify_outcome(
            harness, tmp_path, _ss("bug/653"), source, False, output, 1
        )
        assert status != "pass"
        # Gate/coverage: the marker is re-read from the corpus source.
        gc = _load_goal_coverage()
        for name in _NO_REPLAY_ELIGIBLE:
            rel = _ss(name)
            dst = tmp_path / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_text(_corpus_source(rel).replace("NO_REPLAY", "REPLAY"))
            assert not gc.is_no_replay_translate_only_exempt(rel, tmp_path)

    @pytest.mark.parametrize("name", _NO_REPLAY_ELIGIBLE)
    def test_credited_row_is_tier3_parse_only_and_passes_gate(self, tmp_path, name):
        output = "trust-wp: f FAILED ✗\n" + _wire_line(failed=1, base_exit_code=1)
        source = _corpus_source(_ss(name))
        status, message, *_rest = harness_runner._classify_outcome(
            harness, tmp_path, _ss(name), source, False, output, 1
        )
        tier = harness.classify_verification_tier(_ss(name), status, message, None, source)
        assert status == "pass"
        assert message.startswith(harness.NO_REPLAY_PASS_PREFIX)
        assert tier == "tier3"
        cb = _load_compare_baselines()
        assert cb._true_100_violation_reasons(
            {
                "name": _ss(name),
                "status": "pass",
                "message": message,
                "verification_tier": tier,
                "driver_report": ["trust-wp: f FAILED ✗"],
                "telemetry": _complete_telemetry(failed=1, base_exit_code=1),
            }
        ) == []

    @pytest.mark.parametrize("name", _NO_REPLAY_ELIGIBLE)
    def test_credited_row_is_reported_not_proved(self, name):
        gc = _load_goal_coverage()
        cov = gc.compute_goal_coverage(_ss(name), "trust-wp: f verified ✓\n")
        assert cov["inventory"] == "creusot-not-proved (NO_REPLAY translate-only)"
        assert cov["covered"] == []
        assert gc.goal_coverage_violations(cov)
        cb = _load_compare_baselines()
        reasons = cb.goal_coverage_reasons(
            {
                "name": _ss(name),
                "driver_report": ["trust-wp: f verified ✓"],
                "telemetry": _complete_telemetry(verified=1),
            }
        )
        assert any("NO_REPLAY translate-only" in r for r in reasons), reasons

    @pytest.mark.parametrize("name", ["syntax/04_assoc_prec", "syntax/05_pearlite"])
    def test_shims_never_rewrite_no_replay_contracts(self, name):
        from harness_project import apply_test_specific_shims

        rel = _ss(name)
        original = _corpus_source(rel)
        shimmed = apply_test_specific_shims(Path("reference/creusot") / rel, original)
        contract_re = re.compile(r"#\s*\[\s*(?:requires|ensures)\s*\(.*")
        assert contract_re.findall(shimmed) == contract_re.findall(original)


# ---------------------------------------------------------------------------
# Translate-only credit never hides a verified refutable goal (D-21)
# ---------------------------------------------------------------------------

_PEARL = _ss("syntax/05_pearlite")
# Recorded real driver outputs.
_REAL_NO_REPLAY_OUTPUTS = {
    "syntax/05_pearlite": (
        "trust-wp: has_len_3 is a logic function (definition registered)\n"
        "trust-wp: solver verified ✓\n"
        "trust-wp: struct_in_pearlite unknown (incomplete)\n"
        "trust-wp: struct_order FAILED ✗ (postcondition)\n"
        "trust-wp: 1 verified, 1 failed, 1 errors\n"
        + _wire_line(verified=1, failed=1, errors=1, base_exit_code=1),
        1,
    ),
    "bug/653": (
        "trust-wp: omg FAILED ✗ (postcondition)\ntrust-wp: 0 verified, 1 failed, 0 errors\n"
        + _wire_line(failed=1, base_exit_code=1),
        1,
    ),
    "spec_tests": (
        "trust-wp: test_specs FAILED ✗ (postcondition)\ntrust-wp: 0 verified, 1 failed, 0 errors\n"
        + _wire_line(failed=1, base_exit_code=1),
        1,
    ),
    "bug/511": (_wire_line(base_exit_code=2), 2),
}


def _no_replay_outcome(name: str, output: str, exit_code: int, tmp_path):
    source = _corpus_source(name)
    status, message, *_rest = harness_runner._classify_outcome(
        harness, tmp_path, name, source, False, output, exit_code
    )
    tier = harness.classify_verification_tier(name, status, message, None, source)
    return status, message, tier


def _gate_row(name, output, status="pass", message="Parse-only (NO_REPLAY): syntax-only test", tier="tier3"):
    from harness_classify_succeed import _extract_wire_line_pairs

    gc = _load_goal_coverage()
    return {
        "name": name,
        "status": status,
        "message": message,
        "verification_tier": tier,
        "driver_report": gc.driver_report_lines(output),
        "telemetry": _extract_wire_line_pairs(output),
    }


class TestNoReplayGoalTable:
    def test_one_table_backs_every_allowlist(self):
        gc = _load_goal_coverage()
        cb = _load_compare_baselines()
        assert tuple(gc.NO_REPLAY_TRANSLATE_ONLY_GOAL_TABLE) == tuple(gc.NO_REPLAY_TRANSLATE_ONLY_ALLOWLIST)
        assert tuple(gc.NO_REPLAY_TRANSLATE_ONLY_GOAL_TABLE) == tuple(
            harness.harness_classify._NO_REPLAY_TRANSLATE_ONLY_ALLOWLIST
        )
        assert tuple(cb.NO_REPLAY_TRANSLATE_ONLY_ALLOWLIST) == tuple(gc.NO_REPLAY_TRANSLATE_ONLY_GOAL_TABLE)
        assert cb.no_replay_translate_only_refusals.__module__ == "creusot_goal_coverage"

    @pytest.mark.parametrize("name", _NO_REPLAY_ELIGIBLE)
    def test_table_matches_reference_coma(self, name):
        gc = _load_goal_coverage()
        rows = gc.NO_REPLAY_TRANSLATE_ONLY_GOAL_TABLE[name]
        classes = {item: cls for item, cls, _ in rows}
        assert len(classes) == len(rows)
        assert set(classes.values()) <= {"B", "C", "trusted-strip"}
        modules = {m.name[len("M_"):] for m in gc.coma_modules(_ss(name))}
        # Every .coma module is in the table and classified B or C.
        assert modules == {i for i, c in classes.items() if c != "trusted-strip"}
        # Every goal-bearing item is in the table; every B item bears a goal.
        goal_items = {g.item for g in gc.goal_inventory(_ss(name))}
        assert goal_items <= set(classes)
        assert {i for i, c in classes.items() if c == "B"} <= goal_items
        source = _corpus_source(_ss(name))
        for item, cls in classes.items():
            if cls == "trusted-strip":
                assert re.search(r"#\[trusted\]\s*(?:#\[[^\]]*\]\s*)*pub fn " + item + r"\b", source)
            if cls == "C" and item in goal_items:
                # A C item's only goal is literally `true`.
                coma = (WORKSPACE_ROOT / "reference/creusot" / _ss(name)).with_suffix(".coma").read_text()
                assert re.search(r"goal vc_" + item + r": true\b", coma)

    def test_pearlite_classes(self):
        gc = _load_goal_coverage()
        classes = {i: c for i, c, _ in gc.NO_REPLAY_TRANSLATE_ONLY_GOAL_TABLE["syntax/05_pearlite"]}
        assert classes["struct_in_pearlite"] == "B" and classes["struct_order"] == "B"
        assert classes["has_len_3"] == "C" and classes["solver"] == "trusted-strip"
        assert {i: c for i, c, _ in gc.NO_REPLAY_TRANSLATE_ONLY_GOAL_TABLE["bug/653"]} == {"omg": "B"}
        assert {i: c for i, c, _ in gc.NO_REPLAY_TRANSLATE_ONLY_GOAL_TABLE["spec_tests"]} == {"test_specs": "B"}


class TestNoReplayVerifiedRefutableGoalRefused:
    """Reviewer's forged-output probes against the translate-only credit (D-21)."""

    @pytest.mark.parametrize("name", sorted(_REAL_NO_REPLAY_OUTPUTS))
    def test_real_outputs_are_tier3_translate_only_and_pass_gate(self, tmp_path, name):
        output, exit_code = _REAL_NO_REPLAY_OUTPUTS[name]
        status, _skip, mode = harness.classify_no_replay_result_with_mode(
            output, exit_code=exit_code, test_name=_ss(name)
        )
        assert (status, mode) == ("pass", "translate_only")
        status, message, tier = _no_replay_outcome(_ss(name), output, exit_code, tmp_path)
        assert (status, tier) == ("pass", "tier3") and message.startswith(harness.NO_REPLAY_PASS_PREFIX)
        cb = _load_compare_baselines()
        assert cb._true_100_violation_reasons(_gate_row(_ss(name), output, message=message)) == []

    def test_p1_pearlite_struct_in_pearlite_verified_is_error(self, tmp_path):
        output = (
            "trust-wp: solver verified ✓\n"
            "trust-wp: struct_in_pearlite verified ✓\n"
            "trust-wp: struct_order FAILED ✗ (postcondition)\n"
            + _wire_line(verified=2, failed=1, base_exit_code=1)
        )
        status, reason = harness.classify_no_replay_result(output, exit_code=1, test_name=_PEARL)
        assert status == "error"
        assert "struct_in_pearlite" in reason and "refutable" in reason
        status, message, tier = _no_replay_outcome(_PEARL, output, 1, tmp_path)
        assert (status, tier) == ("error", "tier3")
        assert "struct_in_pearlite" in message.splitlines()[0]
        cb = _load_compare_baselines()
        reasons = cb._true_100_violation_reasons(_gate_row(_PEARL, output))
        assert any("struct_in_pearlite" in r and "refutable" in r for r in reasons), reasons

    def test_p2_every_goal_verified_at_exit_0_is_error_not_tier2(self, tmp_path):
        output = (
            "trust-wp: solver verified ✓\n"
            "trust-wp: struct_in_pearlite verified ✓\n"
            "trust-wp: struct_order verified ✓\n"
            + _wire_line(verified=3)
        )
        status, reason, mode = harness.classify_no_replay_result_with_mode(
            output, exit_code=0, test_name=_PEARL
        )
        assert (status, mode) == ("error", None)
        assert "struct_in_pearlite" in reason and "struct_order" in reason
        status, message, tier = _no_replay_outcome(_PEARL, output, 0, tmp_path)
        assert status == "error" and not message.startswith(harness.NO_REPLAY_VERIFIED_PREFIX)

    @pytest.mark.parametrize(
        "name,item", [("bug/653", "omg"), ("spec_tests", "test_specs")]
    )
    @pytest.mark.parametrize("exit_code", [0, 1])
    def test_verified_b_item_on_old_allowlist_is_error(self, name, item, exit_code):
        output = f"trust-wp: {item} verified ✓\n" + _wire_line(
            verified=1, base_exit_code=exit_code
        )
        status, reason, mode = harness.classify_no_replay_result_with_mode(
            output, exit_code=exit_code, test_name=_ss(name)
        )
        assert (status, mode) == ("error", None)
        assert item in reason
        cb = _load_compare_baselines()
        reasons = cb._true_100_violation_reasons(_gate_row(_ss(name), output))
        assert any(item in r and "refutable" in r for r in reasons), reasons

    @pytest.mark.parametrize(
        "line",
        [
            "trust-wp: proof_assert in struct_in_pearlite verified ✓",
            "trust-wp: struct_order verified ✓ (termination)",
            "trust-wp: struct_order verified ✓ (loop invariant)",
            "trust-wp: struct_in_pearlite refinement verified ✓",
            "trust-wp: struct_in_pearlite verified ✓ (logic postcondition)",
            "trust-wp: field1_is_true verified ✓",
            "trust-wp: caller::{closure#0} verified ✓",
            "trust-wp: crate::struct_order verified ✓",
        ],
    )
    def test_any_positive_line_on_b_or_unlisted_item_is_refused(self, line):
        output = line + "\n" + _wire_line(failed=1, base_exit_code=1)
        status, reason = harness.classify_no_replay_result(output, exit_code=1, test_name=_PEARL)
        assert status == "error" and reason, (line, reason)
        cb = _load_compare_baselines()
        assert any("refused" in r for r in cb._true_100_violation_reasons(_gate_row(_PEARL, output)))

    def test_c_and_trusted_strip_items_may_verify(self):
        output = (
            "trust-wp: solver verified ✓\n"
            "trust-wp: caller verified ✓\n"
            "trust-wp: struct_order FAILED ✗\n"
            + _wire_line(verified=2, failed=1, base_exit_code=1)
        )
        assert harness.classify_no_replay_result(output, exit_code=1, test_name=_PEARL)[0] == "pass"

    def test_wire_verified_beyond_allowed_lines_is_refused(self):
        # verified=2 but only one attributable positive line: the second proof
        # has no named item and may be a refutable goal.
        output = "trust-wp: solver verified ✓\n" + _wire_line(verified=2, failed=1, base_exit_code=1)
        status, reason = harness.classify_no_replay_result(output, exit_code=1, test_name=_PEARL)
        assert status == "error" and "exceeds" in reason
        cb = _load_compare_baselines()
        assert any("exceeds" in r for r in cb._true_100_violation_reasons(_gate_row(_PEARL, output)))

    @pytest.mark.parametrize(
        "output,exit_code",
        [
            (_wire_line(base_exit_code=2), 2),  # all-zero: nothing examined (S4)
            (_wire_line(errors=3, base_exit_code=2), 2),  # errors only (S4)
        ],
    )
    def test_s4_weak_runs_stay_translate_only_credit(self, output, exit_code):
        status, _skip, mode = harness.classify_no_replay_result_with_mode(
            output, exit_code=exit_code, test_name=_PEARL
        )
        assert (status, mode) == ("pass", "translate_only")

    # D-150: the recorded run of the real row since `#[trusted]` was honoured —
    # `solver` is `#[trusted]` in the corpus source, so its trusted counter is
    # the source's own trust base.
    _PEARL_TRUSTED = (
        "trust-wp: has_len_3 is a logic function (definition registered)\n"
        "trust-wp: solver trusted (skipped)\n"
        "trust-wp: struct_in_pearlite unknown (incomplete)\n"
        "trust-wp: struct_order FAILED ✗ (postcondition)\n"
        "trust-wp: (1 trusted, skipped)\n"
        "trust-wp: 0 verified, 1 failed, 1 errors, 1 trusted\n"
        + _wire_line(failed=1, errors=1, trusted=1, base_exit_code=1)
    )

    def test_source_declared_trusted_item_on_translate_only_row_is_clean(self):
        cb = _load_compare_baselines()
        row = _gate_row(_PEARL, self._PEARL_TRUSTED)
        row["trusted_def_paths"] = ["solver"]
        assert cb._true_100_violation_reasons(row) == []

    def test_translate_only_trusted_item_the_source_does_not_declare_is_refused(self):
        # The isolating twin: the same run, but the trusted item is one the
        # source does NOT mark `#[trusted]`.
        cb = _load_compare_baselines()
        output = self._PEARL_TRUSTED.replace("solver trusted", "struct_order trusted")
        row = _gate_row(_PEARL, output)
        row["trusted_def_paths"] = ["struct_order"]
        reasons = cb._true_100_violation_reasons(row)
        assert "telemetry.trusted=1" in reasons, reasons

    def test_translate_only_trusted_counter_without_named_items_is_refused(self):
        cb = _load_compare_baselines()
        row = _gate_row(_PEARL, self._PEARL_TRUSTED.replace("trusted=1", "trusted=2"))
        row["trusted_def_paths"] = ["solver"]
        reasons = cb._true_100_violation_reasons(row)
        assert "telemetry.trusted=2" in reasons, reasons

    def test_gate_refuses_translate_only_row_without_driver_report(self):
        cb = _load_compare_baselines()
        output, _ = _REAL_NO_REPLAY_OUTPUTS["bug/653"]
        row = _gate_row(_ss("bug/653"), output)
        del row["driver_report"]
        assert any("driver report absent" in r for r in cb._true_100_violation_reasons(row))

    def test_gate_refuses_verified_no_replay_message_on_allowlisted_row(self):
        cb = _load_compare_baselines()
        output = "trust-wp: omg verified ✓\n" + _wire_line(verified=1)
        row = _gate_row(
            _ss("bug/653"), output, message="Verified (NO_REPLAY): verified with clean telemetry", tier="tier2"
        )
        reasons = cb._true_100_violation_reasons(row)
        assert "NO_REPLAY verified pass on a translate-only allowlisted test" in reasons


# ---------------------------------------------------------------------------
# The no-obligation tier (D-19). A crate whose Creusot .coma carries no goal at
# all may be credited a pass, but never at a proof-grade tier -- otherwise the
# tier counts mix "proved everything Creusot proves" with "there was nothing to
# prove". The gate counts such a row clean only through zero-goal parity
# (D-88, TestZeroGoalParityGate), never through the tier label.
# ---------------------------------------------------------------------------


class TestNoObligationTier:
    # Every row below is a real corpus row; its classification is checked
    # against the reference .coma, not against a fixture.
    ZERO_OBLIGATION = "tests/should_succeed/lang/empty.rs"  # `pub fn f() { return; }`
    GOAL_BEARING = "tests/should_succeed/100doors.rs"
    NO_COMA = "tests/should_succeed/bug/265.rs"
    UISKIP = "tests/should_succeed/termination/custom_variant.rs"  # `// UISKIP` header, no .coma

    def test_zero_obligation_pass_is_not_tier2(self):
        tier = harness.classify_verification_tier(
            self.ZERO_OBLIGATION, "pass", "Verification succeeded", None, "pub fn f() {}"
        )
        assert tier == "tier0-no-obligation"

    def test_zero_obligation_pass_is_not_tier1(self):
        # verification surface in the source would otherwise give rule 9 tier1
        tier = harness.classify_verification_tier(
            self.ZERO_OBLIGATION, "pass", "some other pass text", None,
            "#[requires(true)] pub fn f() {}",
        )
        assert tier == "tier0-no-obligation"

    def test_goal_bearing_row_keeps_tier2(self):
        tier = harness.classify_verification_tier(
            self.GOAL_BEARING, "pass", "Verification succeeded", None, "pub fn f() {}"
        )
        assert tier == "tier2"

    def test_a_test_creusot_translated_to_nothing_has_no_obligation(self):
        # No .coma because Creusot's output is empty (D-157): no obligation.
        gc = _load_goal_coverage()
        assert gc.goal_inventory(self.NO_COMA) is None
        assert gc.creusot_emitted_nothing(self.NO_COMA)
        tier = harness.classify_verification_tier(
            self.NO_COMA, "pass", "Verification succeeded", None, "pub fn f() {}"
        )
        assert tier == "tier0-no-obligation"

    def test_a_missing_coma_creusot_never_ran_is_unaffected(self):
        # A test the ui runner skips, and a name that is no corpus file, prove
        # nothing about obligations: fail closed, keep the old tier.
        gc = _load_goal_coverage()
        for name in (self.UISKIP, "tests/should_succeed/bug/no_such_test.rs"):
            assert gc.goal_inventory(name) is None
            assert not gc.creusot_emitted_nothing(name)
            tier = harness.classify_verification_tier(
                name, "pass", "Verification succeeded", None, "pub fn f() {}"
            )
            assert tier == "tier2", name

    def test_fail_closed_markers_still_win(self):
        # A zero-obligation row that still leans on a trusted item stays tier3,
        # the more conservative answer; the new tier never rescues it.
        tier = harness.classify_verification_tier(
            self.ZERO_OBLIGATION, "pass",
            "trust-wp: g trusted (skipped)\ntrust-wp: 1 verified, 0 failed, 0 errors, 1 trusted",
            None, "pub fn f() {}",
        )
        assert tier == "tier3"

    def test_non_pass_is_still_tier3(self):
        tier = harness.classify_verification_tier(
            self.ZERO_OBLIGATION, "error", "boom", None, "pub fn f() {}"
        )
        assert tier == "tier3"

    def test_zero_goal_rows_reach_no_proof_grade_tier(self):
        """Rows whose reference .coma carries zero goal items; a pass on any of
        them may reach neither tier1 nor tier2."""
        gc = _load_goal_coverage()
        rows = [
            "bug/1921", "bug/195", "bug/570", "bug/691", "bug/793",
            "clones/04", "constrained_types", "traits/07",
            "traits/15_impl_interfaces",
        ]
        for row in rows:
            name = f"tests/should_succeed/{row}.rs"
            assert gc.goal_inventory(name) == [], row
            tier = harness.classify_verification_tier(
                name, "pass", "Verification succeeded", None, "pub fn f() {}"
            )
            assert tier == "tier0-no-obligation", row

    def test_gate_refuses_the_tier_label_alone(self):
        # The label is where the gate looks, never what it credits: a row
        # carrying the label but not trust-wp's own evidence (no driver report
        # here) stays a violation, and outside the should_succeed lane the
        # label is never credited at all.
        module = _load_compare_baselines()
        row = {
            "name": "tests/should_succeed/lang/empty.rs",
            "status": "pass",
            "message": "Verification succeeded",
            "verification_tier": "tier0-no-obligation",
            "telemetry": _complete_telemetry(verified=1),
        }
        for lane in ("should_succeed", "examples", None):
            reasons = module._true_100_violation_reasons(row, lane)
            assert any("tier0-no-obligation" in r for r in reasons), lane
        assert any(
            "driver report absent" in r
            for r in module._true_100_violation_reasons(row, "should_succeed")
        )

    def test_tier_histogram_has_a_bucket_for_it(self):
        # A tier absent from the histogram vanishes from every summary, and the
        # row is then counted nowhere at all.
        result = harness.TestResult(
            name=self.ZERO_OBLIGATION,
            status="pass",
            message="Verification succeeded",
            duration_ms=1,
        )
        result.verification_tier = "tier0-no-obligation"
        summary = harness.summarize_results([result])
        tiers = summary["should_succeed"]["verification_tiers"]
        assert tiers["tier0-no-obligation"] == 1
        # and it is NOT folded into the proof-grade counters
        assert summary["should_succeed"]["tier2_verified"] == 0
        assert tiers["tier2"] == 0 and tiers["tier0"] == 0


class TestZeroGoalParityGate:
    """Zero-goal parity (D-88): a should_succeed row graded tier0-no-obligation
    is gate-clean iff (a) Creusot's .coma, read by the gate itself, has no goal
    item and (b) trust-wp's own record shows no failure, gap, refusal or
    unexplained exit. Every row name below is a real corpus row whose
    inventory is read from the reference .coma, not from a fixture."""

    ZERO = "tests/should_succeed/lang/empty.rs"  # `pub fn f() { return; }`
    ZERO_CONTRACT = "tests/should_succeed/bug/195.rs"  # `#[requires(p == p)]`, empty body
    GOALS = "tests/should_succeed/result/result.rs"
    NO_COMA = "tests/should_succeed/bug/265.rs"
    UISKIP = "tests/should_succeed/termination/custom_variant.rs"  # `// UISKIP` header, no .coma
    VERIFIED_OUTPUT = (
        "    Checking creusot_test v0.1.0 (<TMPDIR>/test_project)\n"
        "trust-wp: example verified \u2713\n\n"
        "trust-wp: 1 verified, 0 failed, 0 errors\n"
        "    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.61s\n"
    )
    # Wire counters that disqualify. Spelled out rather than derived from the
    # module under test, so widening the credited set cannot pass silently.
    DISQUALIFYING = (
        "failed", "errors", "warnings", "assumed", "trusted", "skipped",
        "verified_with_axiom_deps", "unverified_axioms", "vacuous",
        "proof_assert_inconclusive", "proof_assert_failed", "proof_assert_errors",
        "evidence_gaps", "panics", "demoted", "parse_errors", "termination_errors",
        "logic_recursion_errors", "erasure_errors",
    )
    POSITIVE = ("verified", "proof_assert_verified", "verified_native_only")

    @staticmethod
    def _row(name, output, status="pass", tier="tier0-no-obligation", message=None):
        from harness_classify_succeed import _extract_wire_line_pairs

        gc = _load_goal_coverage()
        return {
            "name": name,
            "status": status,
            "message": output if message is None else message,
            "verification_tier": tier,
            "driver_report": gc.driver_report_lines(output),
            "telemetry": _extract_wire_line_pairs(output),
        }

    def _clean(self, **wire):
        wire.setdefault("base_exit_code", 2)
        return self._row(
            self.ZERO,
            ZERO_GOAL_CLEAN_OUTPUT.replace(ZERO_GOAL_WIRE_LINE, _wire_line(**wire)),
        )

    def _verified(self, **wire):
        wire = {"verified": 1, "base_exit_code": 0, **wire}
        return self._row(
            self.ZERO_CONTRACT,
            self.VERIFIED_OUTPUT + _wire_line(**wire),
            message="Verification succeeded",
        )

    @staticmethod
    def _gate(row, lane="should_succeed"):
        cb = _load_compare_baselines()
        found = cb.find_true_100_violations({"results": [row]}, lane)
        return found[0][1] if found else []

    # -- the oracle's side is read here, and is the real one --------------------

    def test_the_rows_used_here_are_what_they_claim(self):
        gc = _load_goal_coverage()
        assert gc.goal_inventory(self.ZERO) == []
        assert gc.goal_inventory(self.ZERO_CONTRACT) == []
        assert gc.goal_inventory(self.GOALS)
        assert gc.goal_inventory(self.NO_COMA) is None
        assert gc.goal_inventory(self.UISKIP) is None

    # -- the four quadrants -----------------------------------------------------

    def test_quadrant_no_goals_examined_nothing_is_clean(self):
        assert self._gate(self._row(self.ZERO, ZERO_GOAL_CLEAN_OUTPUT)) == []

    def test_quadrant_no_goals_verified_something_is_clean(self):
        # What trust-wp verified is not a Creusot goal: extra, never owed.
        assert self._gate(self._verified()) == []

    def test_quadrant_goals_examined_nothing_is_dropped_obligations(self):
        # The isolating twin of the first quadrant: the SAME trust-wp output,
        # and only the oracle differs.
        labelled = self._row(self.GOALS, ZERO_GOAL_CLEAN_OUTPUT)
        reasons = self._gate(labelled)
        assert any("goal item(s)" in r and "dropped" in r for r in reasons), reasons
        # The shape the harness actually stores for it (status error, tier3)
        # stays a violation and now says why.
        stored = self._row(self.GOALS, ZERO_GOAL_CLEAN_OUTPUT, status="error", tier="tier3")
        reasons = self._gate(stored)
        assert any("obligations dropped" in r for r in reasons), reasons

    def test_quadrant_goals_verified_something_is_graded_normally(self):
        # The inventory, not the stored label, selects goal coverage over parity.
        row = self._verified()
        row["name"] = self.GOALS
        reasons = self._gate(row)
        assert any("uncovered Creusot goal item" in r for r in reasons), reasons
        row["verification_tier"] = "tier2"
        assert self._gate(row) == reasons
        assert not any("zero-goal parity" in r for r in reasons), reasons

    def test_a_source_declared_trusted_item_keeps_parity(self):
        # D-158: traits/14_assoc_in_logic's run, credited because its source
        # declares `#[trusted] test`...
        row = self._row(ZERO_GOAL_SOURCE_TRUSTED_ROW, ZERO_GOAL_SOURCE_TRUSTED_OUTPUT)
        assert self._gate(row) == []
        # ...and the isolating twins: the same run under a zero-goal row whose
        # source declares no `test`, a trusted item the source does not name,
        # and a counter the named items do not account for.
        reasons = self._gate(self._row(self.ZERO, ZERO_GOAL_SOURCE_TRUSTED_OUTPUT))
        assert any("not declared #[trusted]" in r for r in reasons), reasons
        assert any("telemetry.trusted=1" in r for r in reasons), reasons
        stray = self._row(
            ZERO_GOAL_SOURCE_TRUSTED_ROW,
            ZERO_GOAL_SOURCE_TRUSTED_OUTPUT.replace("trust-wp: test trusted", "trust-wp: other trusted"),
        )
        assert any("not declared #[trusted]" in r for r in self._gate(stray))
        miscounted = self._row(
            ZERO_GOAL_SOURCE_TRUSTED_ROW,
            ZERO_GOAL_SOURCE_TRUSTED_OUTPUT.replace(" trusted=1 ", " trusted=2 "),
        )
        assert any("trusted count 2 != 1" in r for r in self._gate(miscounted))

    def test_a_trusted_item_beside_any_other_counter_keeps_no_parity(self):
        out = ZERO_GOAL_SOURCE_TRUSTED_OUTPUT.replace(" warnings=0 ", " warnings=1 ")
        reasons = self._gate(self._row(ZERO_GOAL_SOURCE_TRUSTED_ROW, out))
        assert any("telemetry.warnings=1" in r for r in reasons), reasons

    def test_a_test_creusot_translated_to_nothing_is_clean(self):
        # D-157: an absent .coma is Creusot's empty translation, so the first
        # quadrant's credit holds for it too.
        assert self._gate(self._row(self.NO_COMA, ZERO_GOAL_CLEAN_OUTPUT)) == []

    def test_a_missing_coma_creusot_never_ran_is_never_credited(self):
        # The isolating twin: the same run, for a test the ui runner skips.
        reasons = self._gate(self._row(self.UISKIP, ZERO_GOAL_CLEAN_OUTPUT))
        assert any("no Creusot .coma" in r for r in reasons), reasons

    def test_creusot_emitted_nothing_reads_the_runner_s_contract(self, tmp_path):
        # One source, one file system change at a time: the header, the .coma,
        # the source itself.
        gc = _load_goal_coverage()
        name = "tests/should_succeed/t.rs"
        source = tmp_path / name
        source.parent.mkdir(parents=True)
        source.write_text("extern crate creusot_std;\npub fn f() {}\n")
        assert gc.creusot_emitted_nothing(name, tmp_path)
        assert gc.zero_goal_oracle_refusals(name, tmp_path) == []
        source.write_text("// UISKIP\nextern crate creusot_std;\npub fn f() {}\n")
        assert not gc.creusot_emitted_nothing(name, tmp_path)
        assert gc.zero_goal_oracle_refusals(name, tmp_path)
        source.write_text("extern crate creusot_std;\npub fn f() {}\n")
        coma = tmp_path / "tests/should_succeed/t.coma"
        coma.write_text("(* nothing *)\n")
        assert not gc.creusot_emitted_nothing(name, tmp_path)
        assert gc.zero_goal_oracle_refusals(name, tmp_path)  # a .coma is read, and this one is broken
        coma.unlink()
        source.unlink()
        assert not gc.creusot_emitted_nothing(name, tmp_path)
        assert gc.zero_goal_oracle_refusals(name, tmp_path)
        assert not gc.creusot_emitted_nothing("tests/should_fail/t.rs", tmp_path)

    def test_an_empty_inventory_from_a_broken_coma_is_refused(self, tmp_path):
        # Zero goals is the credit, so a .coma that parses to fewer modules
        # than it declares (truncated) or to none cannot vouch for it.
        gc = _load_goal_coverage()
        real = (_CORPUS_SS / "lang" / "empty.coma").read_text()
        cases = {
            "truncated": real.replace("\nend", ""),
            "no module": "(* nothing *)\n",
        }
        for label, text in cases.items():
            root = tmp_path / label
            coma = root / "tests" / "should_succeed" / "lang" / "empty.coma"
            coma.parent.mkdir(parents=True)
            coma.write_text(text)
            assert gc.goal_inventory(self.ZERO, root) == [], label
            reasons = gc.zero_goal_parity_refusals(
                self.ZERO, status="pass",
                telemetry=_complete_telemetry(base_exit_code=2),
                report_lines=[], message=ZERO_GOAL_CLEAN_OUTPUT, corpus_root=root,
            )
            assert any("module" in r for r in reasons), (label, reasons)
        root = tmp_path / "intact"
        coma = root / "tests" / "should_succeed" / "lang" / "empty.coma"
        coma.parent.mkdir(parents=True)
        coma.write_text(real)
        assert gc.zero_goal_parity_refusals(
            self.ZERO, status="pass", telemetry=_complete_telemetry(base_exit_code=2),
            report_lines=[], message=ZERO_GOAL_CLEAN_OUTPUT, corpus_root=root,
        ) == []

    def test_the_stored_coverage_summary_is_never_read(self):
        # (a) is read from the .coma by the gate, in both directions.
        lying = self._row(self.GOALS, ZERO_GOAL_CLEAN_OUTPUT)
        lying["goal_coverage"] = {"inventory": "coma", "goal_items": 0, "covered": [], "uncovered": []}
        assert self._gate(lying)
        honest = self._row(self.ZERO, ZERO_GOAL_CLEAN_OUTPUT)
        honest["goal_coverage"] = {"inventory": "coma", "goal_items": 3, "covered": [], "uncovered": [{}]}
        assert self._gate(honest) == []

    # -- (b): every disqualifying telemetry field --------------------------------

    def test_the_counter_split_covers_every_wire_field(self):
        cb = _load_compare_baselines()
        gc = _load_goal_coverage()
        assert set(gc.ZERO_GOAL_POSITIVE_COUNTERS) == set(self.POSITIVE)
        assert set(self.DISQUALIFYING) | set(self.POSITIVE) | {"base_exit_code"} == set(
            cb.TELEMETRY_FIELD_NAMES
        )

    def test_each_disqualifying_counter_refuses_an_examined_nothing_row(self):
        for key in self.DISQUALIFYING:
            reasons = self._gate(self._clean(**{key: 1}))
            assert any(f"telemetry.{key}=1" in r for r in reasons), (key, reasons)

    def test_each_disqualifying_counter_refuses_a_verified_row(self):
        for key in self.DISQUALIFYING:
            reasons = self._gate(self._verified(**{key: 1}))
            assert any(f"telemetry.{key}=1" in r for r in reasons), (key, reasons)

    def test_positive_counters_alone_do_not_disqualify(self):
        for key in self.POSITIVE:
            row = self._verified(**{"verified": 0, key: 1})
            reasons = self._gate(row)
            assert not any(f"telemetry.{key}" in r for r in reasons), (key, reasons)

    # -- (b): the exit code is the driver's answer for what was examined ---------

    def test_exit_code_must_match_what_was_examined(self):
        assert self._gate(self._clean(base_exit_code=0))  # examined nothing, yet 0
        assert self._gate(self._verified(base_exit_code=2))  # verified, yet 2
        for code in (1, 3, 101):
            assert self._gate(self._clean(base_exit_code=code)), code
            assert self._gate(self._verified(base_exit_code=code)), code

    def test_status_must_be_pass(self):
        for status in ("error", "fail", "unknown", "skip"):
            row = self._row(self.ZERO, ZERO_GOAL_CLEAN_OUTPUT, status=status)
            assert self._gate(row), status

    def test_telemetry_and_report_must_be_recorded(self):
        row = self._row(self.ZERO, ZERO_GOAL_CLEAN_OUTPUT)
        del row["telemetry"]
        assert any("wire telemetry absent" in r for r in self._gate(row))
        row = self._row(self.ZERO, ZERO_GOAL_CLEAN_OUTPUT)
        del row["driver_report"]
        assert any("driver report absent" in r for r in self._gate(row))

    # -- (b): no negative, refusal, trust or failure report line -----------------

    def test_negative_and_refusal_report_lines_refuse(self):
        lines = (
            # verbatim from bug/02_derive, the one zero-goal row this refuses
            "trust-wp: <Lit as std::clone::Clone>::clone refinement not checked: impl of "
            "external trait method `std::clone::Clone::clone` declares no requires "
            "(precondition direction holds); postcondition direction has no trait-level contract",
            "trust-wp: error: unsupported construct",
            "trust-wp: warning: failed to parse contract",
            "trust-wp: f trusted (skipped)",
            "trust-wp: f unknown (timeout)",
            "trust-wp: 0 verified, 1 failed, 0 errors",
            "trust-wp: 1 verified, 0 failed, 0 errors, 1 trusted",
            "trust-wp: verifying proof_assert in f (0 contract preconditions)",
        )
        for line in lines:
            output = ZERO_GOAL_CLEAN_OUTPUT.replace(
                ZERO_GOAL_WIRE_LINE, line + "\n" + ZERO_GOAL_WIRE_LINE
            )
            assert self._gate(self._row(self.ZERO, output)), line

    # -- (b): a refusal that stopped compilation is not "nothing to examine" -----

    def test_frontend_refusal_with_the_same_wire_line_refuses(self):
        # What the pre-D-88 harness stored for the refused twin: status pass,
        # tier0-no-obligation. The gate must refuse it on its own evidence.
        refused = self._row(self.ZERO, ZERO_GOAL_REFUSED_OUTPUT)
        assert refused["telemetry"] == self._row(self.ZERO, ZERO_GOAL_CLEAN_OUTPUT)["telemetry"]
        reasons = self._gate(refused)
        assert any("rustc reported an error" in r for r in reasons), reasons
        assert any("`Finished`" in r for r in reasons), reasons

    def test_exit_two_needs_the_raw_build_output(self):
        # An examined-nothing row whose stored message is a summary string
        # carries no evidence that the crate compiled.
        row = self._row(self.ZERO, ZERO_GOAL_CLEAN_OUTPUT, message="Verification succeeded")
        assert any("`Finished`" in r for r in self._gate(row))

    def test_truncated_output_refuses(self):
        row = self._row(self.ZERO, ZERO_GOAL_CLEAN_OUTPUT)
        row["message_truncated"] = True
        assert any("truncated" in r for r in self._gate(row))
        gc = _load_goal_coverage()
        row = self._row(
            self.ZERO,
            ZERO_GOAL_CLEAN_OUTPUT.replace(
                "    Finished", f"{gc.STORED_OUTPUT_TRUNCATED_MARKER}\n    Finished"
            ),
        )
        assert any("truncated" in r for r in self._gate(row))

    def test_truncation_marker_is_the_harness_marker(self):
        from harness_output import TRUNCATED_OUTPUT_MARKER

        assert _load_goal_coverage().STORED_OUTPUT_TRUNCATED_MARKER == TRUNCATED_OUTPUT_MARKER

    def test_a_translate_only_credit_is_not_called_dropped(self, tmp_path):
        # D-21: an allowlisted NO_REPLAY row whose run examined nothing is a
        # translate-only credit although its .coma has (refutable) goals;
        # Creusot does not discharge them either, so nothing was dropped.
        output = _wire_line(base_exit_code=2)
        name = _ss("bug/653")
        assert _load_goal_coverage().goal_inventory(name)
        status, message, tier = _no_replay_outcome(name, output, 2, tmp_path)
        row = _gate_row(name, output, status=status, message=message, tier=tier)
        assert self._gate(row, None) == []
        assert self._gate(row, "should_succeed") == []

    # -- scope ------------------------------------------------------------------

    def test_parity_is_a_should_succeed_rule_only(self):
        row = self._row(self.ZERO, ZERO_GOAL_CLEAN_OUTPUT)
        assert self._gate(row, "should_succeed") == []
        for lane in ("examples", None, "some_future_lane"):
            assert any("tier0-no-obligation" in r for r in self._gate(row, lane)), lane

    def test_the_report_names_parity_rows_separately(self, tmp_path, capsys):
        cb = _load_compare_baselines()
        payload = {"results": [self._row(self.ZERO, ZERO_GOAL_CLEAN_OUTPUT)]}
        path = tmp_path / "cur.json"
        path.write_text(json.dumps(payload))
        cb.compare_results(str(path), str(path), "should_succeed")
        out = capsys.readouterr().out
        assert "ZERO-GOAL PARITY (1;" in out and self.ZERO in out
        assert "TRUE-100 VIOLATIONS" not in out

    # -- the inventory's recall is the credit (D-89) ----------------------------
    #
    # A `[@coma:extspec]` closure has no barrier, so Coma inlines its body at
    # every call: an overflow or `hist_inv post` inside it is the CALLER's
    # goal. `_body_goal_kinds` never looks through an extspec callee (it is
    # not in `callees`), so a .coma whose goals all sit in called extspec
    # closures inventories as EMPTY. Harmless while goals were what got
    # credited; here zero is, so `inventory_recall_gaps` names each such call
    # and parity refuses on it.

    def test_a_goal_inside_a_called_extspec_closure_is_not_zero_goals(self, tmp_path):
        # The real row: `multi_arg` calls `|a, b| a + b` (Int32.add) and
        # `move_closure` calls a closure doing `*a += 1` under a `closure
        # hist_inv post`: goals in Creusot's .coma, none in the inventory.
        # Graded by the harness's own classifier and tier (NO_REPLAY verified
        # path; rule 5c turns it tier0-no-obligation) for a clean run that
        # verified only `uses_closure`. Latent today: the source's
        # `#[trusted] new_ref` keeps the real run's trusted counter nonzero.
        name = _ss("closures/01_basic")
        text = (_CORPUS_SS / "closures" / "01_basic.coma").read_text()
        assert "[@coma:extspec]" in text and "Int32.add" in text
        assert "closure0 {x} {_4.f0} {_4.f1}" in text  # multi_arg calls it
        output = (
            "    Checking creusot_test v0.1.0 (<TMPDIR>/test_project)\n"
            "trust-wp: uses_closure verified \u2713\n\n"
            "trust-wp: 1 verified, 0 failed, 0 errors\n"
            "    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.61s\n"
            + _wire_line(verified=1, base_exit_code=0)
        )
        status, message, tier = _no_replay_outcome(name, output, 0, tmp_path)
        assert (status, tier) == ("pass", "tier0-no-obligation"), (status, message, tier)
        row = _gate_row(name, output, status=status, message=message, tier=tier)
        assert self._gate(row), "parity credited a row whose .coma carries closure goals"

    def test_the_same_goal_through_a_called_extspec_closure_refuses(self, tmp_path):
        # Isolating pair over one oracle row: the SAME overflow goal, once in
        # the fn's own body and once in an extspec closure the body calls.
        gc = _load_goal_coverage()
        name = _ss("bug/258")
        real = (_CORPUS_SS / "bug" / "258.coma").read_text()
        anchor = (
            "  let rec err (_to: UInt64.t) (return (x: ())) = (! bb0\n"
            "    [ bb0 = return {_ret} ] [ & _ret: () = Any.any_l () ])"
        )
        assert anchor in real
        locals_ = " [ & _ret: () = Any.any_l () | & _r: UInt64.t = Any.any_l () ])"
        in_body = (
            "  let rec err (_to: UInt64.t) (return (x: ())) = (! bb0\n"
            "    [ bb0 = s0 [ s0 = UInt64.add {_to} {(1: UInt64.t)} "
            "(fun (_x: UInt64.t) -> [ &_r <- _x ] s1) | s1 = return {_ret} ] ]" + locals_
        )
        in_closure = (
            "  let rec closure0 [@coma:extspec] (self: ()) (a: UInt64.t) (return (x: UInt64.t)) = bb0\n"
            "    [ bb0 = s0 [ s0 = UInt64.add {a} {(1: UInt64.t)} "
            "(fun (_x: UInt64.t) -> [ &_ret <- _x ] s1) | s1 = return {_ret} ] ]\n"
            "    [ & _ret: UInt64.t = Any.any_l () | & a: UInt64.t = a ]\n"
            "    [ return (result: UInt64.t) -> return {result} ]\n"
            "  \n"
            "  let rec err (_to: UInt64.t) (return (x: ())) = (! bb0\n"
            "    [ bb0 = s0 [ s0 = closure0 {()} {_to} "
            "(fun (_x: UInt64.t) -> [ &_r <- _x ] s1) | s1 = return {_ret} ] ]" + locals_
        )

        def refusals(label: str, body: str) -> list[str]:
            root = tmp_path / label
            coma = root / "tests" / "should_succeed" / "bug" / "258.coma"
            coma.parent.mkdir(parents=True)
            coma.write_text(real.replace(anchor, body))
            row = self._row(name, ZERO_GOAL_CLEAN_OUTPUT)
            return gc.zero_goal_parity_refusals(
                name,
                status=row["status"],
                telemetry=row["telemetry"],
                report_lines=row["driver_report"],
                message=row["message"],
                corpus_root=root,
            )

        assert refusals("no goal", anchor) == []
        assert refusals("in body", in_body)
        assert refusals("in closure", in_closure), "the closure-borne overflow goal was not seen"

    def test_a_self_recursive_call_precondition_is_a_goal(self, tmp_path):
        # Creusot emits a recursive call as a plain call of the fn itself
        # (cell/02_fib.coma: `fib_memo {mem} {_26}` in fib_memo's own body),
        # so the callee's header `requires` is a goal at that call.
        # `_body_goal_kinds` skips `callee is d`. Isolating pair: the SAME
        # `requires b` call, owed once by a caller of a stub and once by the
        # fn itself.
        gc = _load_goal_coverage()
        name = _ss("bug/258")
        head = "module M_f\n  use creusot.prelude.Any\n  \n"
        call = (
            "(! bb0\n    [ bb0 = s0 [ s0 = f {b} (fun (_x: ()) -> [ &_ret <- _x ] s1) "
            "| s1 = return {_ret} ] ]\n"
            "    [ & _ret: () = Any.any_l () | & b: bool = b ]) "
            "[ return (result: ()) -> (! return {result}) ]\nend\n"
        )
        requires = "{[@stop_split] [@expl:f requires] b}"
        other_caller = (
            head
            + f"  let rec f (b: bool) (return (x: ())) = {requires} "
            "any [ return (result: ()) -> (! return {result}) ]\n  \n"
            "  let rec g (b: bool) (return (x: ())) = " + call
        )
        self_caller = head + f"  let rec f (b: bool) (return (x: ())) = {requires}\n    " + call

        def refusals(label: str, text: str) -> list[str]:
            root = tmp_path / label
            coma = root / "tests" / "should_succeed" / "bug" / "258.coma"
            coma.parent.mkdir(parents=True)
            coma.write_text(text)
            row = self._row(name, ZERO_GOAL_CLEAN_OUTPUT)
            return gc.zero_goal_parity_refusals(
                name,
                status=row["status"],
                telemetry=row["telemetry"],
                report_lines=row["driver_report"],
                message=row["message"],
                corpus_root=root,
            )

        assert refusals("other caller", other_caller)
        assert refusals("self caller", self_caller), "the recursive call's requires was not seen"

    @staticmethod
    def _oracle(tmp_path, label, text, rel="bug/258"):
        """Half (a) over a .coma written in place of the real ``rel`` one."""
        gc = _load_goal_coverage()
        root = tmp_path / label
        coma = root / "tests" / "should_succeed" / f"{rel}.coma"
        coma.parent.mkdir(parents=True)
        coma.write_text(text)
        assert gc.goal_inventory(_ss(rel), root) == [], label  # the inventory reads zero
        return gc.zero_goal_oracle_refusals(_ss(rel), root)

    SELF_HEAD = "module M_f\n  use creusot.prelude.Any\n  \n"
    SELF_CALL = (
        "(! bb0\n    [ bb0 = s0 [ s0 = f {b} (fun (_x: ()) -> [ &_ret <- _x ] s1) "
        "| s1 = return {_ret} ] ]\n"
        "    [ & _ret: () = Any.any_l () | & b: bool = b ]) "
        "[ return (result: ()) -> (! return {result}) ]\nend\n"
    )

    def test_a_self_call_owes_only_a_precondition_it_has(self, tmp_path):
        # Isolates the header half of the self-recursion refusal: the SAME
        # recursive call, with and without a header precondition. Without one
        # the call owes nothing (a recursive fn with no requires and no variant).
        requires = "{[@stop_split] [@expl:f requires] b}"
        with_pre = self.SELF_HEAD + f"  let rec f (b: bool) (return (x: ())) = {requires}\n    " + self.SELF_CALL
        without = self.SELF_HEAD + "  let rec f (b: bool) (return (x: ())) = " + self.SELF_CALL
        refused = self._oracle(tmp_path, "with", with_pre)
        assert any("f calls itself" in r and "f requires" in r for r in refused), refused
        assert self._oracle(tmp_path, "without", without) == []

    def test_the_real_recursive_call_is_named(self):
        # cell/02_fib.coma is the shape's source: its inventory is not empty
        # (fib_memo has other goals), so this pins the recall scan on real text.
        gc = _load_goal_coverage()
        gaps = gc.inventory_recall_gaps(gc.coma_modules(_ss("cell/02_fib")))
        assert len(gaps) == 1, gaps
        assert gaps[0].startswith("M_fib_memo: fib_memo calls itself") and "fib_memo requires" in gaps[0]

    def test_an_uncalled_extspec_closure_owes_nothing(self, tmp_path):
        # bug/1312 returns its closure (`impl Fn`), so its `{false} any`
        # unreachable goal is nobody's: the real row stays creditable. The
        # isolating twin calls that SAME closure from foo99 and is refused.
        gc = _load_goal_coverage()
        name = _ss("bug/1312")
        real = (_CORPUS_SS / "bug" / "1312.coma").read_text()
        assert gc.goal_inventory(name) == [] and gc.zero_goal_oracle_refusals(name) == []
        uncalled = "s0 = [ &_my_closure <- () ] s1"
        called = "s0 = closure0 {()} {x} (fun (_x: Int32.t) -> [ &_my_closure <- () ] s1)"
        assert uncalled in real
        assert self._oracle(tmp_path, "uncalled", real, "bug/1312") == []
        refused = self._oracle(tmp_path, "called", real.replace(uncalled, called), "bug/1312")
        assert any("foo99 calls [@coma:extspec] closure0" in r and "unreachable" in r for r in refused), refused

    EXT_MODULE = (
        "module M_err\n  use creusot.prelude.Any\n  use creusot.int.UInt64\n  \n"
        "  let rec closure1 [@coma:extspec] (self: ()) (a: UInt64.t) (return (x: UInt64.t)) = bb0\n"
        "    [ bb0 = s0 [ s0 = UInt64.add {a} {(1: UInt64.t)} "
        "(fun (_x: UInt64.t) -> [ &_ret <- _x ] s1) | s1 = return {_ret} ] ]\n"
        "    [ & _ret: UInt64.t = Any.any_l () | & a: UInt64.t = a ]\n"
        "    [ return (result: UInt64.t) -> return {result} ]\n"
        "  \n"
        "  let rec closure0 [@coma:extspec] (self: ()) (a: UInt64.t) (return (x: UInt64.t)) = bb0\n"
        "    [ bb0 = s0 [ s0 = INNER (fun (_x: UInt64.t) -> [ &_ret <- _x ] s1) | s1 = return {_ret} ] ]\n"
        "    [ & _ret: UInt64.t = Any.any_l () | & a: UInt64.t = a ]\n"
        "    [ return (result: UInt64.t) -> return {result} ]\n"
        "  \n"
        "  let rec err (_to: UInt64.t) (return (x: ())) = (! bb0\n"
        "    [ bb0 = s0 [ s0 = OUTER (fun (_x: UInt64.t) -> [ &_r <- _x ] s1) | s1 = return {_ret} ] ]"
        " [ & _ret: () = Any.any_l () | & _r: UInt64.t = Any.any_l () ])"
        " [ return (result: ()) -> (! return {result}) ]\nend\n"
    )

    def test_goals_reach_the_caller_through_a_chain_of_extspec_closures(self, tmp_path):
        # err calls closure0, which owes nothing of its own but calls closure1,
        # whose overflow goal Coma inlines into closure0 and so into err.
        # Isolating: the SAME err -> closure0 call is clean when closure0 does
        # not call closure1, and the goal-bearing closure1 alone is nobody's.
        chain = self.EXT_MODULE.replace("INNER", "closure1 {()} {a}").replace("OUTER", "closure0 {()} {_to}")
        broken = self.EXT_MODULE.replace("INNER", "any").replace("OUTER", "closure0 {()} {_to}")
        uncalled = self.EXT_MODULE.replace("INNER", "any").replace("OUTER", "any")
        refused = self._oracle(tmp_path, "chain", chain)
        assert any("err calls [@coma:extspec] closure0" in r and "through closure1" in r for r in refused), refused
        assert self._oracle(tmp_path, "broken", broken) == []
        assert self._oracle(tmp_path, "uncalled", uncalled) == []

    def test_an_extspec_header_precondition_is_the_callers_goal(self, tmp_path):
        # closures/14_move_resolve's shape: the closure's only goal is its
        # header type invariant, which the call inlines like its body.
        header = "{[@stop_split] [@expl:closure 'a' type invariant] true}\n    bb0"
        called = (
            self.EXT_MODULE.replace("INNER", "any").replace("OUTER", "closure0 {()} {_to}")
            .replace(
                "(self: ()) (a: UInt64.t) (return (x: UInt64.t)) = bb0\n    [ bb0 = s0 [ s0 = any",
                "(self: ()) (a: UInt64.t) (return (x: UInt64.t)) =\n    " + header + "\n    [ bb0 = s0 [ s0 = any",
            )
        )
        assert header in called
        refused = self._oracle(tmp_path, "called", called)
        assert any("closure0" in r and "type invariant" in r for r in refused), refused
        assert self._oracle(tmp_path, "uncalled", called.replace("closure0 {()} {_to}", "any")) == []

    def test_the_real_extspec_rows_are_named(self):
        gc = _load_goal_coverage()
        gaps = gc.inventory_recall_gaps(gc.coma_modules(_ss("closures/01_basic")))
        assert [g.split(":")[0] for g in gaps] == ["M_multi_arg", "M_move_closure", "M_move_mut"], gaps
        # 14_move_resolve's `g` calls a closure whose only goal is its header
        # type invariant.
        gaps = gc.inventory_recall_gaps(gc.coma_modules(_ss("closures/14_move_resolve")))
        assert len(gaps) == 1 and "g_T calls [@coma:extspec] closure0" in gaps[0], gaps
        assert "type invariant" in gaps[0], gaps

    # -- a declaration the inventory drops is not an empty one -----------------

    def test_a_declaration_the_inventory_does_not_read_refuses(self, tmp_path):
        # Each text sits beside lang/empty's `f` and carries a goal that
        # `parse_coma` would drop without a word, so the inventory still reads
        # zero. The `(return)` let rec is lang/const's `set_VALUE` shape.
        real = (_CORPUS_SS / "lang" / "empty.coma").read_text()
        anchor = "  let rec f (return (x: ())) ="
        assert real.count(anchor) == 1
        body = " = (! bb0 [ bb0 = {[@expl:assertion] false} return {_ret} ] [ & _ret: () = Any.any_l () ])"
        clean = " = (! bb0 [ bb0 = return {_ret} ] [ & _ret: () = Any.any_l () ])"
        cases = {
            "unparsed let rec": "  let rec set_X (return) = bb0\n    [ bb0 = {[@expl:Add overflow] false} return ]\n",
            "let rec group": f"  let rec g (return (x: ())){clean}\n  with h (return (x: ())){body}\n",
            "plain let": f"  let g (return (x: ())){body}\n",
            "val": "  val g (x: int) : int requires { x > 0 }\n",
            "lemma": "  lemma l : false\n",
            "unnamed goal": "  goal : false\n",
            "unknown line": "  frobnicate {[@expl:assertion] false}\n",
        }
        for label, decl in cases.items():
            refused = self._oracle(tmp_path, label, real.replace(anchor, decl + "  \n" + anchor), "lang/empty")
            assert refused and not any("goal item(s)" in r for r in refused), (label, refused)
        before_decl = real.replace("module M_f\n", "module M_f\n    {[@expl:assertion] false}\n")
        assert self._oracle(tmp_path, "before any declaration", before_decl, "lang/empty")
        outside = "goal g : false\n" + real
        assert self._oracle(tmp_path, "outside any module", outside, "lang/empty")
        # Controls: the real file, and `with` continuing a type group (replace.coma).
        assert self._oracle(tmp_path, "real", real, "lang/empty") == []
        types = "  type t_A = A t_B\n  with t_B = B t_A\n  \n"
        assert self._oracle(tmp_path, "type group", real.replace(anchor, types + anchor), "lang/empty") == []

    def test_every_real_empty_inventory_parses_whole(self):
        # The declaration check costs no real row: every should_succeed .coma
        # whose inventory is empty parses whole at this reference.
        gc = _load_goal_coverage()
        empty = [
            _ss(str(p.relative_to(_CORPUS_SS))[:-3])
            for p in sorted(_CORPUS_SS.rglob("*.rs"))
            if gc.goal_inventory(_ss(str(p.relative_to(_CORPUS_SS))[:-3])) == []
        ]
        assert empty
        assert [n for n in empty if gc._coma_integrity_refusal(n, gc.CORPUS_ROOT)] == []

    # -- the inventory's recall, one step further sideways ----------------------
    #
    # Three more goals Creusot really has that the inventory never counts. Each
    # is a zero that is not zero (a parity credit), and the first also credits a
    # real row through goal coverage today. The controls beside each RED case
    # are ordinary tests, so a broken control cannot hide inside an xfail.

    @staticmethod
    def _oracle_any(tmp_path, label, text, rel):
        """(inventory item names, half-(a) refusals) over ``text`` written in
        place of the real ``rel`` .coma, with no claim about either."""
        gc = _load_goal_coverage()
        root = tmp_path / label
        coma = root / "tests" / "should_succeed" / f"{rel}.coma"
        coma.parent.mkdir(parents=True)
        coma.write_text(text)
        items = gc.goal_inventory(_ss(rel), root)
        return [item.item for item in items], gc.zero_goal_oracle_refusals(_ss(rel), root)

    @staticmethod
    def _elim_empty_module():
        # bug/761.rs: `pub fn elim_empty(x: Empty) { match x {} }`. Creusot emits
        # it as a BODY carrying a type-invariant goal and an `unreachable`
        # (`{false} any`) goal. Every Creusot-generated `elim_*` destructor in
        # the corpus is an `= any` stub, so the `elim_` skip in
        # `module_goal_items`, which only ever sees body defs, reaches user fns.
        real = (_CORPUS_SS / "bug" / "761.coma").read_text()
        module = real[real.index("module M_elim_empty") :]
        if not ("let rec elim_empty (x: ())" in module and "s1 = {false} any" in module):
            pytest.fail("bug/761.coma no longer has the elim_empty body this case reads")
        return module

    BUG_761_OUTPUT = (
        "    Checking creusot_test v0.1.0 (<TMPDIR>/test_project)\n"
        "trust-wp: try_option verified ✓\n"
        "trust-wp: try_result verified ✓\n\n"
        "trust-wp: 2 verified, 0 failed, 0 errors\n"
        "    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.61s\n"
    )

    def test_a_user_fn_not_named_elim_is_counted(self, tmp_path):
        # Control for the two elim_ RED cases: the SAME module with the fn
        # renamed is one goal item, so half (a) refuses it.
        module = self._elim_empty_module().replace("elim_empty", "drop_empty")
        items, refused = self._oracle_any(tmp_path, "renamed", module, "bug/258")
        assert items == ["drop_empty"] and refused, (items, refused)

    def test_a_user_fn_named_elim_is_not_zero_goals(self, tmp_path):
        items, refused = self._oracle_any(tmp_path, "elim", self._elim_empty_module(), "bug/258")
        assert items or refused, "parity credits a .coma whose only fn, elim_empty, carries two goals"

    def test_the_real_elim_row_is_not_gate_clean(self):
        # The stored lane's bug/761 row, rebuilt: try_option and try_result
        # verified, elim_empty never examined, graded tier2. elim_empty is a
        # user body with goals, so the gate must not credit the row.
        gc = _load_goal_coverage()
        name = _ss("bug/761")
        self._elim_empty_module()
        # elim_empty is a USER body with real goals; the inventory must count it.
        if sorted(item.item for item in gc.goal_inventory(name)) != ["elim_empty", "try_option", "try_result"]:
            pytest.fail("bug/761's inventory changed; re-read this case")
        row = self._row(
            name,
            self.BUG_761_OUTPUT + _wire_line(verified=2, base_exit_code=0),
            tier="tier2",
            message="Verification succeeded",
        )
        assert self._gate(row), "the gate credits bug/761 without elim_empty's goals"

    CHAR_ANCHOR = "    [ bb0 = return {_ret} ] [ & _ret: () = Any.any_l () ])"

    def _char_call(self, call):
        # lang/empty's `f`, its body now a u8 -> char cast. The prelude gives
        # Char.of_int AND Char.of_BV256 (the #[bitwise_proof] spelling,
        # integer_ops.coma's test_to_char_bw) an `arithmetic overflow`
        # precondition, and the inventory must count both.
        real = (_CORPUS_SS / "lang" / "empty.coma").read_text()
        if self.CHAR_ANCHOR not in real:
            pytest.fail("lang/empty.coma changed; re-read this case")
        body = (
            f"    [ bb0 = s0 [ s0 = {call} (fun (_x: Char.t) -> [ &_1 <- _x ] s1) "
            "| s1 = return {_ret} ] ] [ & _ret: () = Any.any_l () | & _1: Char.t = Any.any_l () ])"
        )
        uses = "  use creusot.prelude.Any\n  use creusot.prelude.Char\n  use creusot.int.UInt8BW\n"
        return real.replace(self.CHAR_ANCHOR, body).replace("  use creusot.prelude.Any\n", uses)

    def test_a_char_of_int_cast_is_a_goal(self, tmp_path):
        # Control: the same cast through Char.of_int is counted.
        text = self._char_call("Char.of_int {UInt8.t'int (97: UInt8.t)}")
        items, refused = self._oracle_any(tmp_path, "of_int", text, "lang/empty")
        assert items == ["f"] and refused, (items, refused)

    def test_a_char_of_bv256_cast_is_a_goal(self, tmp_path):
        text = self._char_call("Char.of_BV256 {UInt8BW.to_BV256 (255: UInt8BW.t)}")
        items, refused = self._oracle_any(tmp_path, "of_BV256", text, "lang/empty")
        assert items or refused, "parity credits a .coma whose only goal is a Char.of_BV256 precondition"

    DECL_ANCHOR = "  let rec f (return (x: ())) ="
    DECL_G = (
        "let rec g (return (x: ())) = (! bb0 [ bb0 = {[@expl:assertion] false} return {_ret} ] "
        "[ & _ret: () = Any.any_l () ]) [ return (result: ()) -> (! return {result}) ]\n"
    )

    def test_a_declaration_at_its_own_indent_is_read(self, tmp_path):
        # Control: g at the printer's two-space indent is read, and counted.
        real = (_CORPUS_SS / "lang" / "empty.coma").read_text()
        text = real.replace(self.DECL_ANCHOR, "  " + self.DECL_G + self.DECL_ANCHOR)
        items, refused = self._oracle_any(tmp_path, "indented", text, "lang/empty")
        assert items == ["f"] and refused, (items, refused)

    def test_a_declaration_at_column_zero_is_not_dropped(self, tmp_path):
        # `_declaration_refusal` refuses a two-space line that is no declaration
        # and a line before the first one, but a line at column 0 (or 1, or a
        # tab) after a declaration joins that declaration as a continuation, so
        # the same g is dropped without a word.
        real = (_CORPUS_SS / "lang" / "empty.coma").read_text()
        text = real.replace(self.DECL_ANCHOR, self.DECL_G + self.DECL_ANCHOR)
        items, refused = self._oracle_any(tmp_path, "column0", text, "lang/empty")
        assert items or refused, "parity credits a .coma whose goal-bearing g sits at column 0"
