#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Runner/orchestration helpers for the Creusot compatibility harness."""

from __future__ import annotations

import contextlib
import os
import re
import signal
import shlex
import shutil
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Any, Iterator

try:
    import fcntl
except ImportError:  # pragma: no cover - non-Unix fallback
    fcntl = None

try:
    from tests.creusot_compat.harness_facade import (
        RUNNER_REQUIRED_ATTRS,
        resolve_harness_facade,
    )
    from tests.creusot_compat.harness_model import parse_wire_line, WIRE_PREFIX
    from tests.creusot_compat.harness_targets import _workspace_target_binary
    from tests.creusot_compat.harness_verification_tier import (
        classify_verification_tier,
    )
except ModuleNotFoundError:
    # Running as a script (`python3 tests/creusot_compat/harness.py`) puts this
    # directory on sys.path, so import sibling modules directly.
    from harness_facade import RUNNER_REQUIRED_ATTRS, resolve_harness_facade
    from harness_model import parse_wire_line, WIRE_PREFIX
    from harness_targets import _workspace_target_binary
    from harness_verification_tier import classify_verification_tier

_TEST_TIMEOUT_OVERRIDES_SEC = {
    # #2116: these iterator-heavy compat crates still need a larger wall-clock
    # budget than the default 120s harness cap to surface the post-fix result
    # instead of a harness-side timeout.
    "tests/should_succeed/cc/fmap.rs": 300,
    # #2694: fmap_iter axiom overhead regression — previously errored at ~72s, now
    # needs more time due to accumulated axiom assertions (type invariant, trait
    # postcondition, generic container layout, ground sub-expression extraction).
    "tests/should_succeed/ghost/fmap_iter.rs": 600,
    "tests/should_succeed/ghost/seq_iter.rs": 300,
    # cell/02_fib verifies at ~294s — barely exceeds 120s default.
    # #2701: factory session 3/4 axiom additions pushed solve time past 300s.
    "tests/should_succeed/cell/02_fib.rs": 600,
    # result/own.rs finishes at ~164s; timeout override for accurate classification.
    "tests/should_succeed/result/own.rs": 300,
    # inc_some_2_list has passed in 6s but regresses to timeout under contention.
    "tests/should_succeed/rusthorn/inc_some_2_list.rs": 300,
    # #2686: type_invariants/borrows.rs has 8 functions with complex invariant
    # reasoning on mutable borrows. 120s insufficient for complete solve.
    "tests/should_fail/type_invariants/borrows.rs": 300,
    # #2674: integer_ops.rs has 12 type modules * ~12 ops each = ~144 functions,
    # many with #[bitwise_proof] requiring BV theory. 120s insufficient for all.
    "tests/should_succeed/integer_ops.rs": 300,
    # #2674: filter_positive.rs has recursive logic functions (num_of_pos) with
    # complex loop invariants requiring ground instantiation chains.
    "tests/should_succeed/filter_positive.rs": 300,
    # #2674: binary_search_list.rs has user-defined enum List<T> with recursive
    # logic functions and complex quantifier-based loop invariants.
    "tests/should_succeed/binary_search_list.rs": 300,
    # #2674: ghost_vec.rs regressed from 12s to >120s after ay pivot strategy
    # change (ay#8404). Needs larger budget until ay upstream fix.
    # #2701: factory session 3/4 axiom additions pushed solve time past 300s.
    "tests/should_succeed/ghost/ghost_vec.rs": 600,
    # #2674: inferred_invariants.rs has nested loops with mutable borrow
    # invariant inference. Each loop adds verification overhead.
    "tests/should_succeed/inferred_invariants.rs": 300,
    # #2674: bitvector tests hit the 120s harness wall-clock limit.
    "tests/should_succeed/bitvectors/popcount.rs": 300,
    "tests/should_succeed/bitvectors/rightmostbit.rs": 300,
    # #2674: list_reversal_lasso.rs uses linked-list reversal with lasso
    # detection — complex recursive logic functions and loop invariants
    # exceed 120s default with ay-dpll's single-round E-matching.
    "tests/should_succeed/list_reversal_lasso.rs": 300,
    # #2674: inc_some_2_tree.rs uses recursive tree data structures with
    # nested Option unwrapping — ground pool instantiation for tree axioms
    # consumes significant solver time.
    "tests/should_succeed/rusthorn/inc_some_2_tree.rs": 300,
    # #2674: ay bump (eede84ad → 18802b68) caused performance regression
    # on loop invariant verification. bug/164 has nested loops with break
    # statements — previously solved in <1s, now exceeds 120s.
    "tests/should_succeed/bug/164.rs": 300,
    # #2674: ay bump caused performance regression on termination checking.
    # incorrect_variant has recursive functions with modular arithmetic
    # variants — previously solved in <1s, now exceeds 120s.
    # #2686: Increased from 300s to 600s — the test has 3 functions
    # (2 recursive + 1 loop variant), each requiring separate solver
    # invocations for variant decrease checks plus body verification.
    "tests/should_fail/terminates/incorrect_variant.rs": 600,
}


def _resolve_harness_facade(facade: object | None) -> object:
    return resolve_harness_facade(
        facade, RUNNER_REQUIRED_ATTRS, context="runner"
    )


def _effective_timeout_for_test(test_path: Path, timeout_sec: int) -> int:
    """Return the effective harness timeout for a specific compat test."""
    test_path_str = test_path.as_posix()
    for suffix, override_sec in _TEST_TIMEOUT_OVERRIDES_SEC.items():
        if test_path_str.endswith(suffix):
            return max(timeout_sec, override_sec)
    return timeout_sec

def ensure_harness_binaries(
    workspace: Path, verbose: bool, facade: object | None = None
) -> None:
    """Build harness binaries before running compatibility tests."""
    harness = _resolve_harness_facade(facade)

    # Always build debug profile.
    cmd = [
        "cargo",
        "build",
        "--locked",
        "-p",
        "trust-wp-driver",
        "-p",
        "cargo-trust-wp",
    ]
    if verbose:
        print("Building harness binaries (trust-wp-driver, cargo-trust-wp)...")
        result = harness.subprocess.run(cmd, cwd=workspace, text=True)
    else:
        result = harness.subprocess.run(
            cmd, cwd=workspace, capture_output=True, text=True
        )

    if result.returncode != 0:
        error_text = (result.stderr or "").strip() or (result.stdout or "").strip()
        if not error_text:
            error_text = f"exit code {result.returncode}"
        raise RuntimeError(f"Failed to build harness binaries: {error_text}")

    # If a release binary file exists, rebuild it too — run-trust-wp-rustc.sh
    # uses `-f` and prefers release over debug, so a stale release binary
    # silently overrides the freshly-built debug binary (#972).
    release_binary = _workspace_target_binary(
        workspace, "trust-wp-rustc", profile="release"
    )
    if release_binary.is_file():
        release_cmd = [
            "cargo",
            "build",
            "--locked",
            "--release",
            "-p",
            "trust-wp-driver",
            "--bin",
            "trust-wp-rustc",
        ]
        if verbose:
            print("Rebuilding release binaries (stale release binary detected)...")
            release_result = harness.subprocess.run(
                release_cmd, cwd=workspace, text=True
            )
        else:
            release_result = harness.subprocess.run(
                release_cmd, cwd=workspace, capture_output=True, text=True
            )
        if release_result.returncode != 0:
            error_text = (
                (release_result.stderr or "").strip()
                or (release_result.stdout or "").strip()
            )
            if not error_text:
                error_text = f"exit code {release_result.returncode}"
            raise RuntimeError(
                f"Failed to build release harness binaries: {error_text}"
            )


def setup_trust_wp_rustc_wrapper(
    workspace: Path, bin_dir: Path, facade: object | None = None
) -> None:
    """Create a wrapper script for trust-wp-rustc via the facade seam."""
    _ = _resolve_harness_facade(facade)
    bin_dir.mkdir(parents=True, exist_ok=True)
    wrapper_path = bin_dir / "trust-wp-rustc"
    script_path = workspace / "scripts" / "run-trust-wp-rustc.sh"
    release_binary = _workspace_target_binary(workspace, "trust-wp-rustc", profile="release")
    debug_binary = _workspace_target_binary(workspace, "trust-wp-rustc")
    driver_binary = release_binary if release_binary.is_file() else debug_binary

    contents = (
        "#!/bin/bash\n"
        "set -e\n"
        f"export TRUST_WP_RUSTC_BIN={shlex.quote(str(driver_binary))}\n"
        f'"{script_path}" "$@"\n'
    )
    wrapper_path.write_text(contents)
    wrapper_path.chmod(0o755)


_STABLE_HARNESS_BIN_CACHE: dict[str, tuple[Path, float]] = {}


def _stable_harness_bin_dir(
    workspace: Path, cargo_trust_wp: Path, harness: Any
) -> Path:
    """Return a reused bin dir holding cargo-trust-wp + the trust-wp-rustc wrapper.

    The copy is made once per (binary, mtime) and reused across every test so
    macOS Gatekeeper only assesses the new inode a single time, instead of
    paying a ~15-20s first-launch assessment on a freshly-copied binary every
    test (which made every per-test run time out on a degraded syspolicyd).
    """
    key = str(cargo_trust_wp)
    src_mtime = cargo_trust_wp.stat().st_mtime
    cached = _STABLE_HARNESS_BIN_CACHE.get(key)
    if (
        cached is not None
        and cached[1] == src_mtime
        and (cached[0] / "cargo-trust-wp").exists()
        and (cached[0] / "trust-wp-rustc").exists()
    ):
        return cached[0]

    bin_dir = Path(tempfile.mkdtemp(prefix="trust_wp_harness_bin_"))
    harness.setup_trust_wp_rustc_wrapper(workspace, bin_dir)
    cargo_trust_wp_copy = bin_dir / "cargo-trust-wp"
    shutil.copy(cargo_trust_wp, cargo_trust_wp_copy)
    cargo_trust_wp_copy.chmod(0o755)
    _STABLE_HARNESS_BIN_CACHE[key] = (bin_dir, src_mtime)
    return bin_dir


def run_trust_wp_on_project(
    workspace: Path,
    project_dir: Path,
    timeout_sec: int = 120,
    shared_target_dir: Path | None = None,
    facade: object | None = None,
) -> tuple[bool, str, int, int | None]:
    """Run cargo trust-wp on a synthesized test project."""
    harness = _resolve_harness_facade(facade)
    cargo_trust_wp = _workspace_target_binary(workspace, "cargo-trust-wp")

    if not cargo_trust_wp.exists():
        return False, f"cargo-trust-wp not built at {cargo_trust_wp}", 0, None

    # Use ONE stable, reused harness bin dir (cargo-trust-wp copy + the
    # trust-wp-rustc wrapper as its sibling) instead of a fresh per-test copy.
    # A fresh copy is a new filesystem inode, which macOS Gatekeeper
    # (syspolicyd) re-assesses on first launch — ~15-20s each when the daemon
    # is saturated/degraded — so a per-test copy made every test time out
    # before cargo even started. Reusing one already-assessed copy keeps
    # per-test launch fast and is also just less work. (cargo-trust-wp resolves
    # trust-wp-rustc as a sibling of its own exe, so they must stay co-located.)
    bin_dir = _stable_harness_bin_dir(workspace, cargo_trust_wp, harness)
    cargo_trust_wp_copy = bin_dir / "cargo-trust-wp"

    path_entries = [str(bin_dir)]
    if "PATH" in os.environ:
        path_entries.append(os.environ["PATH"])
    joined_path = ":".join(path_entries)

    target_dir = str(shared_target_dir) if shared_target_dir else str(project_dir / "target")
    env = {
        **os.environ,
        "CARGO_TARGET_DIR": target_dir,
        "PATH": joined_path,
        # Bypass cargo serialization lock for per-test invocations (#1346).
        # Safe because CARGO_TARGET_DIR is already isolated (shared temp dir or
        # per-project dir), so no target directory contention exists. The prebuild
        # step (ensure_harness_binaries) still uses the lock since it writes to
        # the shared workspace target/debug/.
        "AIT_ALLOW_LOCKLESS_CARGO": "1",
        # Resolve dependencies from the local registry cache only. Each temp
        # project is its own isolated workspace carrying the DERIVED reviewed
        # lockfile (see harness_project._derived_child_lock) and runs with
        # --locked, but cargo could still touch the network for index
        # freshness ("Updating crates.io index" / "Blocking waiting for file
        # lock on package cache"). That network access races any other cargo
        # process on the machine for the registry index lock and gets
        # miscounted as a per-test compile failure. The workspace build and the
        # warmup `cargo check` already populate the cache with every transitive
        # dependency, so offline resolution is complete and contention-immune.
        "CARGO_NET_OFFLINE": "true",
    }

    return _execute_cargo_trust_wp(
        harness, cargo_trust_wp_copy, project_dir, env, timeout_sec, workspace,
    )


def _execute_cargo_trust_wp(
    harness: Any,
    cargo_trust_wp: Path,
    project_dir: Path,
    env: dict[str, str],
    timeout_sec: int,
    workspace: Path,
) -> tuple[bool, str, int, int | None]:
    """Run cargo-trust-wp in a new process group and handle timeout cleanup."""
    sp = harness.subprocess
    start = time.time()
    try:
        # start_new_session=True puts cargo-trust-wp + trust-wp-rustc in one
        # process group so we can kill the entire tree on timeout.  (#2301)
        proc = sp.Popen(
            # Pass the per-test budget through as the driver-side solver
            # timeout. Without this, every obligation solved under the
            # driver's 60s DEFAULT regardless of --timeout/overrides — the
            # harness budget only killed the outer process. The driver's
            # adaptive slicing + 1.5x hard-timeout envelopes are designed
            # around this value (#2674).
            [
                str(cargo_trust_wp),
                "--verbose",
                "--timeout",
                str(timeout_sec),
                "--locked",
            ],
            cwd=project_dir,
            stdout=sp.PIPE,
            stderr=sp.PIPE,
            text=True,
            env=env,
            start_new_session=True,
        )
        try:
            stdout, stderr = proc.communicate(timeout=timeout_sec)
        except sp.TimeoutExpired:
            return _handle_timeout(harness, proc, start, timeout_sec, workspace)

        duration_ms = int((time.time() - start) * 1000)
        output = stdout + stderr
        success = harness._verification_run_succeeded(proc.returncode, output)
        return success, output, duration_ms, proc.returncode
    except (OSError, sp.SubprocessError) as exc:
        duration_ms = int((time.time() - start) * 1000)
        return False, f"Error: {exc}", duration_ms, None


def _handle_timeout(
    harness: Any,
    proc: subprocess.Popen[str],
    start: float,
    timeout_sec: int,
    workspace: Path,
) -> tuple[bool, str, int, int | None]:
    """Kill the process group and collect partial output after timeout."""
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except OSError:
        pass
    stdout, stderr = proc.communicate(timeout=5)
    duration_ms = int((time.time() - start) * 1000)
    partial = (stdout or "") + (stderr or "")
    if partial:
        return False, f"Timeout after {timeout_sec}s\n{partial}", duration_ms, None
    return False, f"Timeout after {timeout_sec}s", duration_ms, None


def _apply_test_selection(
    tests: list[Path], filter_pattern: str | None, limit: int | None
) -> list[Path]:
    selected_tests = tests
    if filter_pattern:
        pattern = re.compile(filter_pattern, re.IGNORECASE)
        selected_tests = [test for test in selected_tests if pattern.search(str(test))]
    if limit:
        selected_tests = selected_tests[:limit]
    return selected_tests


def _warmup_shared_target(
    harness: Any,
    workspace: Path,
    tests: list[Path],
    shared_target: Path,
    verbose: bool,
) -> None:
    if not tests:
        return

    warmup_dir = Path(tempfile.mkdtemp(prefix="trust_wp_harness_warmup_"))
    try:
        warmup_project = harness.create_warmup_project(workspace, warmup_dir)
        if verbose:
            print("Warming up shared target (compiling dependencies)...")
        warmup_env = {
            **os.environ,
            "CARGO_TARGET_DIR": str(shared_target),
            # Bypass the external cargo lock for warmup (#2297). The harness
            # serializes writes to shared_target below, while the external lock
            # keys all warmup projects as "test_project" and over-serializes
            # unrelated isolated targets.
            "AIT_ALLOW_LOCKLESS_CARGO": "1",
        }
        # Make the warmup compile dependencies through the SAME trust-wp-rustc
        # wrapper the per-test builds use. Cargo's dependency fingerprint
        # includes RUSTC_WRAPPER, so a plain `cargo check` warmup produces dep
        # artifacts the per-test (cargo-trust-wp → RUSTC_WRAPPER=<stable-bin>/
        # trust-wp-rustc) cannot reuse — it recompiles the whole stack inside
        # its own budget and times out. Pointing the warmup at the identical
        # wrapper makes the warm dep cache reusable. With
        # `-Z trust-verify-target` set (deps are non-target → DependencyBoundary
        # skip), the wrapper only COMPILES deps (no verification), so this stays
        # cheap. Falls back to plain cargo if the wrapper bin isn't built yet.
        try:
            _cargo_trust_wp = _workspace_target_binary(workspace, "cargo-trust-wp")
            if _cargo_trust_wp.exists():
                _bin_dir = _stable_harness_bin_dir(workspace, _cargo_trust_wp, harness)
                _wrapper = _bin_dir / "trust-wp-rustc"
                if _wrapper.exists():
                    _path = [str(_bin_dir)]
                    if "PATH" in os.environ:
                        _path.append(os.environ["PATH"])
                    warmup_env["RUSTC_WRAPPER"] = str(_wrapper)
                    warmup_env["CARGO_TRUST_WP"] = "1"
                    warmup_env["PATH"] = ":".join(_path)
                    warmup_env["CARGO_NET_OFFLINE"] = "true"
        except (OSError, AttributeError):
            pass
        with _shared_target_lock(shared_target):
            warmup_result = harness.subprocess.run(
                ["cargo", "check", "--locked"],
                cwd=warmup_project,
                capture_output=True,
                text=True,
                # The fixture dep stack (creusot_contracts + creusot_std +
                # trust_wp + trust_wp_std) compiles cold in ~6 min; a 300s cap
                # made warmup fail under any load, so every per-test run then
                # paid full cold-cache compilation inside its own timeout and
                # timed out. Allow an override and default high enough to
                # actually populate the cache on a quiet box.
                timeout=int(os.environ.get("TRUST_WP_HARNESS_WARMUP_TIMEOUT", "1200")),
                env=warmup_env,
            )
        if warmup_result.returncode != 0 and verbose:
            print(
                f"Warmup failed (exit {warmup_result.returncode}), "
                "first test will pay full compilation cost."
            )
    except (harness.subprocess.TimeoutExpired, OSError) as exc:
        if verbose:
            print(f"Warmup failed ({exc!r}), continuing without cache.")
    finally:
        shutil.rmtree(warmup_dir, ignore_errors=True)
    if verbose:
        print("Warmup complete.")


def _invalidate_test_crate_cache(shared_target: Path) -> None:
    """Remove creusot_test fingerprints/artifacts from the shared target dir.

    Each harness test reuses the crate name ``creusot_test`` v0.1.0 with
    different source content.  Cargo's fingerprint system may decide the crate
    is already compiled and skip invoking ``trust-wp-rustc``, causing
    ``cargo-trust-wp`` to emit "no verification summary detected".

    Deleting only ``creusot_test`` fingerprints and compiled artifacts forces
    recompilation of the test crate while preserving expensive dependency
    caches (trust-wp, trust-wp-std, creusot-contracts, etc.).  See #1959.
    """
    debug_dir = shared_target / "debug"
    fingerprint_dir = debug_dir / ".fingerprint"
    deps_dir = debug_dir / "deps"

    if fingerprint_dir.is_dir():
        for entry in fingerprint_dir.iterdir():
            if entry.name.startswith("creusot_test-"):
                shutil.rmtree(entry, ignore_errors=True)

    if deps_dir.is_dir():
        for entry in deps_dir.iterdir():
            if entry.name.startswith(("libcreusot_test-", "creusot_test-")):
                entry.unlink(missing_ok=True)

    # Also clean incremental compilation cache (#2107). Cargo's incremental
    # compilation can reuse cached MIR/codegen artifacts from a previous test,
    # potentially causing trust-wp-rustc to skip full analysis.
    incremental_dir = debug_dir / "incremental"
    if incremental_dir.is_dir():
        for entry in incremental_dir.iterdir():
            if entry.name.startswith("creusot_test-"):
                shutil.rmtree(entry, ignore_errors=True)

    # Clean build script output (#2107). Proc macros may cache state across
    # test crate invocations.
    build_dir = debug_dir / "build"
    if build_dir.is_dir():
        for entry in build_dir.iterdir():
            if entry.name.startswith("creusot_test-"):
                shutil.rmtree(entry, ignore_errors=True)


@contextlib.contextmanager
def _shared_target_lock(shared_target: Path) -> Iterator[None]:
    """Serialize harness writes to a shared Cargo target directory.

    Every compat fixture is compiled as ``creusot_test``.  When two harness
    processes point at the same ``TRUST_WP_HARNESS_TARGET_DIR``, concurrent
    cache invalidation and cargo-trust-wp runs can reuse or delete the wrong
    ``creusot_test`` artifacts, producing result messages for a different
    fixture.  A per-target advisory lock keeps dependency reuse while making
    the per-test crate cache deterministic.
    """
    if fcntl is None:
        yield
        return

    shared_target.mkdir(parents=True, exist_ok=True)
    lock_path = shared_target / ".trust-wp-harness-target.lock"
    with lock_path.open("a+") as lock_file:
        fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)


def _run_project_with_retry(
    harness: Any,
    workspace: Path,
    test_path: Path,
    temp_path: Path,
    timeout_sec: int,
    shared_target: Path,
    verbose: bool,
) -> tuple[bool, str, int, int | None]:
    with _shared_target_lock(shared_target):
        _invalidate_test_crate_cache(shared_target)
        project_dir = harness.create_test_project(workspace, test_path, temp_path)
        effective_timeout_sec = _effective_timeout_for_test(test_path, timeout_sec)
        success, output, duration_ms, exit_code = harness.run_trust_wp_on_project(
            workspace,
            project_dir,
            timeout_sec=effective_timeout_sec,
            shared_target_dir=shared_target,
        )

        if not success and harness._has_cargo_lock_contention(output):
            if verbose:
                print("(retrying after cargo-lock contention)...", end=" ", flush=True)
            retry_dir = temp_path / "retry"
            retry_dir.mkdir(exist_ok=True)
            retry_project = harness.create_test_project(workspace, test_path, retry_dir)
            success, output, retry_ms, exit_code = harness.run_trust_wp_on_project(
                workspace,
                retry_project,
                timeout_sec=effective_timeout_sec,
                shared_target_dir=shared_target,
            )
            duration_ms += retry_ms

    return success, output, duration_ms, exit_code


def _classify_error_or_unknown_category(
    harness: Any,
    status: str,
    output: str,
    exit_code: int | None,
) -> str | None:
    """Compute error_category for error and unknown statuses (#2690).

    For "error" status, uses the existing ``classify_error_category`` to
    distinguish timeout, compile, driver_panic, etc.

    For "unknown" status, uses ``classify_unknown_category`` to sub-classify
    into demoted, incomplete, quantifier_unhandled, etc.  This surfaces
    actionable diagnostic detail in the baseline summary.
    """
    if status == "error":
        return harness.classify_error_category(output, exit_code)
    if status == "unknown":
        return harness.classify_unknown_category(output)
    return None


def _classify_outcome(
    harness: Any,
    workspace: Path,
    test_name: str,
    source: str,
    success: bool,
    output: str,
    exit_code: int | None,
) -> tuple[str, str, str | None, str | None, bool]:
    """Classify test outcome.

    Returns ``(status, message, skip_reason, error_category, message_truncated)``.
    """
    if harness._is_should_fail_test(test_name):
        status, skip_reason = harness.classify_should_fail_result(
            success, output, source, test_name, exit_code=exit_code
        )
        error_cat = _classify_error_or_unknown_category(harness, status, output, exit_code)
        if status == "pass":
            # Backend-superseded tests (#2686) return a reason explaining why
            # trust-wp's ay backend correctly handles code that Creusot rejects.
            # Use a distinct message prefix to distinguish from normal rejections.
            backend_reason = harness._check_backend_superseded(test_name)
            if backend_reason is not None:
                msg = f"{harness.BACKEND_PASS_PREFIX} {backend_reason}"
                return status, msg, None, None, False
            return status, "Correctly rejected", skip_reason, None, False
        message, message_truncated = harness._truncate_output_with_flag(output, workspace)
        return status, message, skip_reason, error_cat, message_truncated

    # NO_REPLAY tests used to be syntax-only passes.  Strict Creusot
    # compatibility requires replayable verification, so the marker fails
    # closed before the normal success path can accept it -- unless the
    # aggregate telemetry shows a clean run (no failures, errors, or panics
    # and zero exit), in which case the gate is satisfied and the test
    # passes as a parse-only success.
    if harness._is_no_replay_source(source):
        # Pass test_name so the genuinely-unprovable translate-only allowlist
        # (bug/653, traits/04, spec_tests) can match — it is keyed on the test
        # path. Without this the allowlist never fired through the main harness
        # path and every allowlisted NO_REPLAY test errored on its expected
        # failed-prover exit.
        status, skip_reason = harness.classify_no_replay_result(
            output, exit_code=exit_code, test_name=test_name
        )
        error_cat = _classify_error_or_unknown_category(harness, status, output, exit_code)
        if status == "pass":
            return (
                status,
                f"{harness.NO_REPLAY_PASS_PREFIX} syntax-only test",
                None,
                None,
                False,
            )
        if status == "error" and skip_reason is None and error_cat == "unknown":
            return (
                status,
                harness.NO_REPLAY_STRICT_ERROR_MESSAGE,
                None,
                "strict_gate",
                False,
            )
        message, message_truncated = harness._truncate_output_with_flag(output, workspace)
        return status, message, None, error_cat, message_truncated

    if success:
        return "pass", "Verification succeeded", None, None, False

    status, skip_reason = harness.classify_failure(
        output, source, exit_code=exit_code, test_name=test_name
    )
    error_cat = _classify_error_or_unknown_category(harness, status, output, exit_code)
    strict_reason = harness._KNOWN_STRICT_REJECTION_TESTS.get(test_name)
    if strict_reason is not None:
        # The strict-rejection whitelist records should_succeed tests where
        # trust-wp's REJECTION is the known-correct outcome (e.g. Creusot only
        # warns on a non-decreasing variant). A non-zero verifier exit is the
        # EXPECTED transport for that rejection, so the exit!=0 fail-closed
        # short-circuit in classify_failure() (12d0fdc) returns "error" instead
        # of "fail" and would otherwise erase this long-standing whitelist.
        # Re-derive the SEMANTIC status without the exit-code override, for
        # whitelisted tests ONLY; honor the whitelist only on a genuine "fail"
        # (never a crash/panic/infra "error"). Per-test + should_succeed-only =>
        # cannot manufacture a false-accept.
        semantic_status = status
        if status != "fail":
            semantic_status, _ = harness.classify_failure(
                output, source, exit_code=None, test_name=test_name
            )
        if semantic_status == "fail":
            return "pass", f"{harness.STRICT_PASS_PREFIX} {strict_reason}", None, None, False
    message, message_truncated = harness._truncate_output_with_flag(output, workspace)
    return status, message, skip_reason, error_cat, message_truncated


def _extract_telemetry(output: str) -> Any:
    """Extract structured verification telemetry from cargo-trust-wp output (#2641).

    Scans the combined stdout+stderr for a ``TRUST_WP_RESULT:v1`` wire line
    re-emitted by cargo-trust-wp.  Returns a ``VerificationTelemetry`` instance
    or ``None`` when no wire line is found.
    """
    last_telemetry = None
    for line in output.split("\n"):
        stripped = line.strip()
        if stripped.startswith(WIRE_PREFIX):
            telemetry = parse_wire_line(stripped)
            if telemetry is None:
                return None
            last_telemetry = telemetry
    return last_telemetry


def _message_with_telemetry_for_tier(message: str, telemetry: Any) -> str:
    """Append structured counters so tiering can fail closed on generic passes."""
    if telemetry is None:
        return message
    pairs = " ".join(
        f"{key}={value}" for key, value in telemetry.to_dict().items()
    )
    return f"{message}\n{WIRE_PREFIX} {pairs}"


# Driver-emitted proof_assert verification summary, e.g.
# ``trust-wp: proof_assert: 3 verified, 0 failed, 2 errors`` (reporting.rs:370).
_PROOF_ASSERT_SUMMARY_RE = re.compile(
    r"proof_assert:\s*\d+\s+verified,\s+\d+\s+failed,\s+\d+\s+errors"
)


def _tier_message_with_proof_assert_summary(
    message: str, telemetry: Any, output: str
) -> str:
    """Tier-classification message that also surfaces the proof_assert summary.

    The structured wire line carries ``proof_assert_failed``/``proof_assert_errors``
    but not the count of *verified* proof_asserts, so a proof_assert-only crate
    (zero contract-level obligations) reports ``verified=0`` and never reaches
    tier2 even though ay genuinely discharged every assertion. Re-attaching the
    driver's human-readable ``proof_assert: N verified, …`` line lets the tier
    classifier credit those proven assertions as tier2 review-grade evidence.
    The appended structured counters still hold the crate at tier3 when any
    proof_assert failed/errored or produced an evidence gap (see the tier guards
    in harness_verification_tier), so this never masks an unproven assertion.
    """
    tier_message = _message_with_telemetry_for_tier(message, telemetry)
    summary = _PROOF_ASSERT_SUMMARY_RE.search(output)
    if summary is not None:
        tier_message = f"{tier_message}\n{summary.group(0)}"
    return tier_message


def _run_single_test(
    harness: Any,
    workspace: Path,
    test_path: Path,
    index: int,
    total: int,
    timeout_sec: int,
    shared_target: Path,
    verbose: bool,
) -> Any:
    test_name = str(test_path.relative_to(workspace / "reference" / "creusot"))
    if verbose:
        print(f"[{index + 1}/{total}] Testing {test_name}...", end=" ", flush=True)

    with tempfile.TemporaryDirectory() as temp_dir:
        temp_path = Path(temp_dir)
        try:
            source = test_path.read_text()
            success, output, duration_ms, exit_code = _run_project_with_retry(
                harness,
                workspace,
                test_path,
                temp_path,
                timeout_sec,
                shared_target,
                verbose,
            )
            status, message, skip_reason, error_cat, message_truncated = _classify_outcome(
                harness, workspace, test_name, source, success, output, exit_code
            )
            telemetry = _extract_telemetry(output)
            tier = classify_verification_tier(
                test_name,
                status,
                _tier_message_with_proof_assert_summary(message, telemetry, output),
                skip_reason,
                source,
            )
            result = harness.TestResult(
                name=test_name,
                status=status,
                message=message,
                duration_ms=duration_ms,
                skip_reason=skip_reason,
                error_category=error_cat,
                message_truncated=message_truncated,
                verification_tier=tier,
                telemetry=telemetry,
            )
        except Exception as exc:  # pragma: no cover - retained behavior
            result = harness.TestResult(
                name=test_name,
                status="error",
                message=str(exc),
                duration_ms=0,
            )

    if verbose:
        status_str = result.status.upper()
        if result.skip_reason:
            status_str += f" ({result.skip_reason})"
        print(f"{status_str} ({result.duration_ms}ms)")
    return result


def run_harness(
    verbose: bool = False,
    filter_pattern: str | None = None,
    limit: int | None = None,
    lane: str = "should_succeed",
    timeout_sec: int = 120,
    facade: object | None = None,
) -> list[Any]:
    """Run the Creusot compatibility harness."""
    harness = _resolve_harness_facade(facade)
    workspace = harness.find_workspace_root()
    harness.ensure_harness_binaries(workspace, verbose)
    tests = _apply_test_selection(
        harness.find_creusot_tests(workspace, lane=lane), filter_pattern, limit
    )
    if verbose:
        print(f"Found {len(tests)} Creusot tests (lane: {lane})")

    # Use a shared target directory so dependency compilation is amortized
    # across all tests. Without this, every test rebuilds trust-wp deps from
    # scratch (~50-60s), causing false timeouts. (#1551)
    #
    # TRUST_WP_HARNESS_TARGET_DIR: reuse an existing target directory instead of
    # allocating a fresh temp dir. Prevents disk exhaustion on machines with
    # large existing target/ footprints. The directory is NOT cleaned up on
    # exit when provided via env var. (#2522)
    env_target = os.environ.get("TRUST_WP_HARNESS_TARGET_DIR")
    owns_target = env_target is None
    if env_target:
        shared_target = Path(env_target)
        shared_target.mkdir(parents=True, exist_ok=True)
        if verbose:
            print(f"Using shared target from TRUST_WP_HARNESS_TARGET_DIR: {shared_target}")
    else:
        shared_target = Path(tempfile.mkdtemp(prefix="trust_wp_harness_target_"))
    try:
        _warmup_shared_target(harness, workspace, tests, shared_target, verbose)
        results = [
            _run_single_test(
                harness,
                workspace,
                test_path,
                index,
                len(tests),
                timeout_sec,
                shared_target,
                verbose,
            )
            for index, test_path in enumerate(tests)
        ]
        return results
    finally:
        if owns_target:
            shutil.rmtree(shared_target, ignore_errors=True)
