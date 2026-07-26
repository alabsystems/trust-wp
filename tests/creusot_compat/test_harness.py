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
import shutil
import subprocess
import sys
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
    assert all(cmd[:3] == ["cargo", "build", "--locked"] for cmd, _ in calls)


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


def test_fixture_verification_command_is_locked(tmp_path):
    """The actual cargo-trust-wp fixture subprocess must consume Cargo.lock."""
    calls = []

    class FinishedProcess:
        returncode = 0

        @staticmethod
        def communicate(timeout=None):
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
    assert calls[0][0] == [
        str(binary),
        "--verbose",
        "--timeout",
        "17",
        "--locked",
    ]


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
            "--version",
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


def test_private_wrapper_rejects_ambiguous_private_sysroots(tmp_path):
    """Two matching private sysroots must not be resolved by directory order."""
    fake_rustc, _, _ = _private_wrapper_layout(tmp_path, candidate_count=2)

    result = subprocess.run(
        [
            str(WORKSPACE_ROOT / "scripts" / "trustc-private-wrapper.sh"),
            str(fake_rustc),
            "--version",
        ],
        cwd=WORKSPACE_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode != 0
    assert "multiple private sysroots match compiler" in result.stderr


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
            "--version",
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


def _run_review_dependency_validator(project: Path, ay: Path, trust_ir_ref: str):
    return subprocess.run(
        [sys.executable, "-", str(project), str(ay), "", "", trust_ir_ref],
        input=_review_dependency_validator_source(),
        capture_output=True,
        text=True,
        check=False,
    )


def test_review_dependency_validator_accepts_exact_fixture(review_dependency_fixture):
    project, ay, trust_ir_commit = review_dependency_fixture
    result = _run_review_dependency_validator(project, ay, trust_ir_commit)
    assert result.returncode == 0, result.stderr
    assert "cargo_toml_trust_ir_matches_lock: yes" in result.stdout
    assert "sibling_ay_is_path_dep_source_of_truth: yes" in result.stdout


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

    def test_create_warmup_project_writes_scaffold(self, tmp_path):
        project_dir = harness.create_warmup_project(WORKSPACE_ROOT, tmp_path)
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
        from tests.creusot_compat import harness_project

        child_lock_text = (project_dir / "Cargo.lock").read_text()
        ws_lock_text = (WORKSPACE_ROOT / "Cargo.lock").read_text()
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
        """When trust-wp rejects (success=False, raw=fail), should_fail -> pass."""
        status, reason = harness.classify_should_fail_result(
            success=False,
            output="FAILED: verification counterexample found",
            source="fn bad() {}",
        )
        assert status == "pass"
        assert reason is None, f"Rc source should not produce a skip reason, got {reason!r}"

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
            test_name="tests/should_fail/ignore_overflow.rs",
            exit_code=101,
        )
        assert status == "error", (
            f"Backend-superseded compile error should classify as error, got {status!r}"
        )
        assert reason is None, (
            f"Backend compile error should not produce a reason, got {reason!r}"
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
        """Per-function status lines prove the lane saw real verification work."""
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
        assert status == "pass"
        assert reason is None

    def test_unsupported_source_is_error(self):
        """Unsupported should_fail sources fail closed instead of skipping."""
        # Use `#[open]` as the unsupported feature — prophetic is now supported (#2683).
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
        """#[logic(law)] should no longer be intercepted as unsupported."""
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
        """duplicate_specs: trust-wp now detects duplicate extern_spec (#2686).

        duplicate_specs.rs was removed from _KNOWN_EXPECTED_DIVERGENCE_TESTS
        (2026-04-14) because trust-wp now detects duplicate/conflicting
        extern_spec declarations and rejects them with exit code 2.
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
# classify_failure: Rc/Arc source no longer auto-skipped (#634)
# ---------------------------------------------------------------------------


class TestClassifyFailureRcArc:
    """Rc/Arc source patterns should NOT trigger auto-skip now that
    trust-wp-std has Rc/Arc specs wired in std_specs.rs."""

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
        # Use `#[open]` as the unsupported feature — prophetic is now supported (#2683).
        status, reason = harness.classify_failure(
            output="FAILED: something",
            source="#[open]\nfn reflexive() {}",
        )
        assert status == "error", f"Expected open-function source to be an error, got {status!r}"
        assert reason is None, f"Expected no skip reason for open source strict error, got {reason!r}"

    def test_law_source_falls_through_to_output_classification(self):
        """Law annotations should now classify from the output text."""
        status, reason = harness.classify_failure(
            output="FAILED: counterexample",
            source="#[law]\nfn reflexive() {}",
        )
        assert status == "fail", (
            f"Expected law source to follow output failure markers, got {status!r}"
        )
        assert reason is None, f"Expected no skip reason for #[law] output fallthrough, got {reason!r}"

    def test_prophetic_source_falls_through_to_output_classification(self):
        """Prophetic logic is now supported — classify from output, not skip (#2683)."""
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
        # Use `#[open]` as the unsupported feature — prophetic is now supported (#2683).
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

        Previously misclassified as 'skip' with 'no contracts verified' because
        the classifier fell through to the contract-count check before the
        _has_panic_exit_status guard was added.
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
        # Use `#[open]` as the unsupported feature — prophetic is now supported (#2683).
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
        assert run_calls == [(["cargo", "check", "--locked"], warmup_project)], (
            f"Expected cargo check in warmup project, got {run_calls!r}"
        )
        assert removed_dirs == [(warmup_dir, True)], (
            f"Expected warmup dir cleanup, got {removed_dirs!r}"
        )


# ---------------------------------------------------------------------------
# classify_error_category (#2690)
# ---------------------------------------------------------------------------


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
        Historically the classifier only matched the ``during verification``
        variant, causing check_sat-phase panics to fall through to
        caught_panic or driver_panic (observed on binary_search_list.rs in
        baseline-20260418).
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

    def test_final_borrows_proof_assert_rejection_is_pass(self):
        """final_borrows.rs: proof_assert failures count as correct rejection (#2690).

        This test has 0 function-level failures but 2 proof_assert failures,
        meaning trust-wp IS correctly rejecting the code.
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
        assert status == "pass", (
            f"proof_assert failures should count as correct rejection, got '{status}'"
        )


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

        This tests the new detection path added by #2690 — solver-level
        timeouts were previously falling through to 'unknown'.
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
        """bug/436_2.rs is no longer a known false-accept."""
        from harness_classify import get_false_accept_summary

        summary = get_false_accept_summary()
        # generic_deref_ghost.rs and generic_deref_snap.rs removed from
        # false-accepts (2026-04-18) -- now caught by ghost type escape check.
        # bug/436_2.rs removed from false-accepts (2026-04-23) -- now caught
        # by snapshot self-reference validation.
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
        """The R4 xfail ledger is EMPTY: all five baseline-20260706 rows are
        fixed (int-shift-full 2026-07-24: shift-amount-in-range obligation;
        impl_arg + trait_where + trait_where_supertrait 2026-07-24: illegal-
        recursive-trait bound check; trait_impl_where 2026-07-24: self-named
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
        """bug/436_2.rs now has a real snapshot self-reference rejection.

        generic_deref_ghost.rs and generic_deref_snap.rs removed from
        false-accepts (#2686) — now detected by check_ghost_type_escape
        and classified as valid rejections ("pass").
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
        """Resolved expected-divergence tests are no longer skipped.

        bug/1544_2.rs and bug/603.rs moved to backend-superseded (#2686) —
        trust-wp-std deliberately does not gate standard Rust traits on spec
        traits. bug/1762.rs is now rejected by trusted contract validation.
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

    Historical classification only matched ``panicked during verification:``
    via a literal substring check.  That missed phase-qualified variants the
    driver emits for other code paths, e.g.:

    - ``panicked during proof_assert:`` — proof_assert driver catch
      (observed on ``mapping_test.rs`` in baseline-20260418)
    - ``panicked during loop verification:`` — loop body catch
    - ``panicked during check_sat:`` — check_sat wrapper catch

    These variants were misclassified as ``driver_panic`` (via the rustc panic
    fall-through) instead of ``caught_panic``.  The regex-based
    ``_has_caught_panic_marker`` helper now recognizes all phase variants
    without colliding with ay's ``ay solver panic during <phase>`` form
    (different verb: ``panic`` vs ``panicked``).
    """

    def test_panicked_during_proof_assert_is_caught_panic(self):
        """Reproduces mapping_test.rs from baseline-20260418 (#2690)."""
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

    def test_clean_wire_line_passes(self):
        """All-zero wire line on exit 0 → pass."""
        from harness_classify import classify_no_replay_result

        output = "trust-wp: 0 verified, 0 failed, 0 errors\n" + self._wire()
        status, reason = classify_no_replay_result(output, exit_code=0)
        assert status == "pass", (
            f"Clean wire line should pass; got status={status!r} reason={reason!r}"
        )
        assert reason is None

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

    The a8d74e4 carve-out required wire `verified>0`, but the driver never
    counts proof_assert verifications there — a proof_assert-only crate with
    one trusted item (bug/negative_int_pats: 7/7 proof_asserts verified,
    trusted=1, exit 2) hard-errored despite a failure-free wire line. The
    carve-out now also accepts a verified>0 proof_assert summary with zero
    failed/errored assertions.
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
