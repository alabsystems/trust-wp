#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Shared target-directory and ownership helpers for the Creusot harness."""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - Python < 3.11 fallback
    import tomli as tomllib  # type: ignore[no-redef]

try:
    from tests.creusot_compat.harness_model import (
        _AIT_PID_NAME_RE,
        _AI_ROLES,
        _ROOT_PID_NAME_RE,
        _SKIP_PREBUILD_ENV,
        _TARGET_ROLE_NAME_RE,
        _TRUTHY_ENV_VALUES,
    )
except ModuleNotFoundError:
    # Running as a script (`python3 tests/creusot_compat/harness.py`) puts this
    # directory on sys.path, so import sibling modules directly.
    from harness_model import (  # type: ignore[no-redef]
        _AIT_PID_NAME_RE,
        _AI_ROLES,
        _ROOT_PID_NAME_RE,
        _SKIP_PREBUILD_ENV,
        _TARGET_ROLE_NAME_RE,
        _TRUTHY_ENV_VALUES,
    )


def _workspace_target_bases(workspace: Path) -> list[Path]:
    """Return candidate workspace target dirs in wrapper-preference order."""
    candidates: list[Path] = []
    seen: set[Path] = set()

    def add(path: Path) -> None:
        resolved = path.resolve()
        if resolved in seen:
            return
        seen.add(resolved)
        candidates.append(resolved)

    env_target_dir = os.environ.get("CARGO_TARGET_DIR")
    if env_target_dir:
        env_target = Path(env_target_dir)
        add(env_target if env_target.is_absolute() else workspace / env_target)

    role = os.environ.get("AI_ROLE", "")
    worker_id = os.environ.get("AI_WORKER_ID")
    if worker_id and role in _AI_ROLES and worker_id.isdigit():
        add(workspace / "target" / f"{role.lower()}_{worker_id}")
    elif role or worker_id:
        add(workspace / "target" / "user")

    add(workspace / "target")
    return candidates


def _workspace_target_binary(
    workspace: Path, name: str, *, profile: str = "debug"
) -> Path:
    """Resolve a workspace binary across isolated and default target dirs."""
    candidates = [
        target_base / profile / name for target_base in _workspace_target_bases(workspace)
    ]
    for candidate in candidates:
        if candidate.exists():
            return candidate
    return candidates[0]


def _skip_harness_prebuild_requested() -> bool:
    """Return True when the harness should reuse existing workspace binaries."""
    value = os.environ.get(_SKIP_PREBUILD_ENV, "").strip().lower()
    return value in _TRUTHY_ENV_VALUES


def _missing_harness_binaries(workspace: Path) -> list[Path]:
    """Return required harness binaries that are absent from candidate targets."""
    required = ("cargo-trust-wp", "trust-wp-rustc")
    missing: list[Path] = []
    for binary_name in required:
        binary_path = _workspace_target_binary(workspace, binary_name)
        if not binary_path.exists():
            missing.append(binary_path)
    return missing


_HARNESS_PROVENANCE_SCHEMA = "trust-wp-harness-binaries.v1"
_HARNESS_PROVENANCE_FILENAME = ".trust-wp-harness-binaries-v1.json"
_BUILD_ENV_KEYS = (
    "CARGO_BUILD_TARGET",
    "CARGO_ENCODED_RUSTFLAGS",
    "RUSTC",
    "RUSTC_WRAPPER",
    "RUSTFLAGS",
    "RUSTUP_TOOLCHAIN",
)


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _git_output(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(
        ["git", "-C", str(repo), *args], stderr=subprocess.DEVNULL
    )


def _git_root(path: Path) -> Path | None:
    probe = path if path.is_dir() else path.parent
    try:
        return Path(
            _git_output(probe, "rev-parse", "--show-toplevel").decode().strip()
        ).resolve()
    except (OSError, subprocess.CalledProcessError):
        return None


def _workspace_source_roots(workspace: Path) -> list[Path]:
    """Return git roots that can contribute bytes to the harness binaries."""
    workspace = workspace.resolve()
    roots = {_git_root(workspace)}
    manifest_path = workspace / "Cargo.toml"
    try:
        manifest = tomllib.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as error:
        raise RuntimeError(f"cannot fingerprint {manifest_path}: {error}") from error

    dependencies = manifest.get("workspace", {}).get("dependencies", {})
    if isinstance(dependencies, dict):
        for dependency in dependencies.values():
            if not isinstance(dependency, dict):
                continue
            raw_path = dependency.get("path")
            if not isinstance(raw_path, str):
                continue
            dependency_root = _git_root((workspace / raw_path).resolve())
            roots.add(dependency_root)

    if None in roots:
        raise RuntimeError(f"harness source is not in a git checkout: {workspace}")
    return sorted((root for root in roots if root is not None), key=str)


def _git_source_state(repo: Path) -> bytes:
    """Hash committed identity plus exact tracked and untracked worktree bytes."""
    digest = hashlib.sha256()
    digest.update(_git_output(repo, "rev-parse", "HEAD").strip())
    digest.update(b"\0tracked-diff\0")
    digest.update(_git_output(repo, "diff", "--no-ext-diff", "--binary", "HEAD", "--"))
    digest.update(b"\0untracked\0")
    untracked = _git_output(repo, "ls-files", "-z", "--others", "--exclude-standard")
    for raw_name in sorted(name for name in untracked.split(b"\0") if name):
        path = repo / os.fsdecode(raw_name)
        digest.update(raw_name)
        digest.update(b"\0")
        if path.is_file():
            digest.update(_sha256_file(path).encode())
        else:
            digest.update(b"non-file")
        digest.update(b"\0")
    return digest.hexdigest().encode()


def _tool_identity(command: str) -> bytes:
    try:
        return subprocess.check_output(
            [command, "--version", "--verbose"], stderr=subprocess.STDOUT
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise RuntimeError(f"cannot fingerprint build tool {command}: {error}") from error


def _harness_source_fingerprint(workspace: Path) -> str:
    digest = hashlib.sha256()
    digest.update(b"trust-wp-harness-source.v1\0")
    for root in _workspace_source_roots(workspace):
        digest.update(str(root).encode())
        digest.update(b"\0")
        digest.update(_git_source_state(root))
        digest.update(b"\0")
    for command in ("cargo", "rustc"):
        digest.update(command.encode())
        digest.update(b"\0")
        digest.update(_tool_identity(command))
        digest.update(b"\0")
    for key in _BUILD_ENV_KEYS:
        digest.update(key.encode())
        digest.update(b"=")
        digest.update(os.environ.get(key, "").encode())
        digest.update(b"\0")
    return digest.hexdigest()


def _selected_harness_binaries(workspace: Path) -> dict[str, Path]:
    cargo_binary = _workspace_target_binary(workspace, "cargo-trust-wp")
    release_driver = _workspace_target_binary(
        workspace, "trust-wp-rustc", profile="release"
    )
    debug_driver = _workspace_target_binary(workspace, "trust-wp-rustc")
    driver_binary = release_driver if release_driver.is_file() else debug_driver
    return {
        "cargo-trust-wp": cargo_binary.resolve(),
        "trust-wp-rustc": driver_binary.resolve(),
    }


def _harness_provenance_path(workspace: Path) -> Path:
    cargo_binary = _selected_harness_binaries(workspace)["cargo-trust-wp"]
    return cargo_binary.parent / _HARNESS_PROVENANCE_FILENAME


def _write_harness_binary_provenance(
    workspace: Path, source_fingerprint: str | None = None
) -> Path:
    binaries = _selected_harness_binaries(workspace)
    missing = [path for path in binaries.values() if not path.is_file()]
    if missing:
        raise RuntimeError(
            "cannot record harness provenance; missing binaries: "
            + ", ".join(str(path) for path in missing)
        )
    payload = {
        "schema": _HARNESS_PROVENANCE_SCHEMA,
        "workspace": str(workspace.resolve()),
        "source_fingerprint": source_fingerprint
        or _harness_source_fingerprint(workspace),
        "binaries": {
            name: {"path": str(path), "sha256": _sha256_file(path)}
            for name, path in binaries.items()
        },
    }
    provenance_path = _harness_provenance_path(workspace)
    temporary = provenance_path.with_suffix(provenance_path.suffix + ".tmp")
    temporary.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(provenance_path)
    return provenance_path


def _harness_binary_provenance_error(workspace: Path) -> str | None:
    """Return why skip-prebuild reuse is not bound to current source and bytes."""
    provenance_path = _harness_provenance_path(workspace)
    try:
        payload = json.loads(provenance_path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return f"missing build provenance {provenance_path}"
    except (OSError, json.JSONDecodeError) as error:
        return f"invalid build provenance {provenance_path}: {error}"

    if payload.get("schema") != _HARNESS_PROVENANCE_SCHEMA:
        return f"unsupported build provenance schema in {provenance_path}"
    if payload.get("workspace") != str(workspace.resolve()):
        return "build provenance belongs to a different workspace"

    try:
        current_source = _harness_source_fingerprint(workspace)
    except RuntimeError as error:
        return str(error)
    if payload.get("source_fingerprint") != current_source:
        return "harness source/dependency/toolchain fingerprint changed since build"

    expected_binaries = payload.get("binaries")
    if not isinstance(expected_binaries, dict):
        return "build provenance has no binary records"
    for name, path in _selected_harness_binaries(workspace).items():
        record = expected_binaries.get(name)
        if not isinstance(record, dict):
            return f"build provenance has no {name} record"
        if record.get("path") != str(path):
            return f"selected {name} path differs from build provenance"
        if not path.is_file():
            return f"selected {name} binary is missing: {path}"
        if record.get("sha256") != _sha256_file(path):
            return f"selected {name} bytes differ from build provenance"
    return None


def _current_workspace_target_name() -> str | None:
    """Return the current session's isolated target dir name, if configured."""
    role = os.environ.get("AI_ROLE", "").strip().lower()
    worker_id = os.environ.get("AI_WORKER_ID", "").strip()
    if not role:
        return None
    if worker_id.isdigit():
        return f"{role}_{worker_id}"
    if role == "user":
        return "user"
    return None


def _parse_target_owner_name(name: str) -> str | None:
    """Map a target dir basename to its owning role/session name."""
    match = _TARGET_ROLE_NAME_RE.fullmatch(name)
    if match is None:
        return None
    role, role_id = match.groups()
    return f"{role}_{role_id}" if role_id is not None else role


def _pid_target_name(path: Path) -> str | None:
    """Return the target dir name owned by a PID file path, if recognized."""
    match = _ROOT_PID_NAME_RE.fullmatch(path.name)
    if match is None:
        match = _AIT_PID_NAME_RE.fullmatch(path.name)
    if match is None:
        return None
    role, role_id = match.groups()
    return f"{role}_{role_id}" if role_id is not None else role


def _read_pid(path: Path) -> int | None:
    """Parse the PID from a repo/runtime pid file."""
    try:
        raw = path.read_text().strip()
    except OSError:
        return None
    pid_text = raw.split(":", 1)[0].strip()
    return int(pid_text) if pid_text.isdigit() else None


def _pid_is_alive(pid: int) -> bool:
    """Best-effort process liveness check."""
    try:
        os.kill(pid, 0)
    except OSError:
        return False
    return True


def _live_role_target_names(workspace: Path) -> set[str]:
    """Return target dir names whose owning sessions currently have live PIDs."""
    live_targets: set[str] = set()
    pid_paths = list(workspace.glob(".pid_*"))
    ait_pid_dir = workspace / ".ait" / "pid"
    if ait_pid_dir.is_dir():
        try:
            pid_paths.extend(ait_pid_dir.iterdir())
        except OSError:
            pass

    for pid_path in pid_paths:
        if not pid_path.is_file():
            continue
        target_name = _pid_target_name(pid_path)
        if target_name is None:
            continue
        pid = _read_pid(pid_path)
        if pid is None or not _pid_is_alive(pid):
            continue
        live_targets.add(target_name)

    return live_targets


def _active_workspace_target_names(workspace: Path) -> set[str]:
    """Return isolated target dirs currently referenced by cargo/rustc processes."""
    target_root = workspace / "target"
    try:
        result = subprocess.run(
            ["ps", "-Ao", "command="],
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError:
        return set()

    if result.returncode != 0:
        return set()

    active_targets: set[str] = set()
    target_pattern = re.compile(
        rf"{re.escape(str(target_root))}/([^/\s]+)(?=[/\s]|$)"
    )
    for line in result.stdout.splitlines():
        if "cargo" not in line and "rustc" not in line:
            continue
        for match in target_pattern.finditer(line):
            target_name = match.group(1)
            if _parse_target_owner_name(target_name) is None:
                continue
            active_targets.add(target_name)

    return active_targets


def _rebuildable_workspace_target_cache_paths(target_dir: Path) -> list[Path]:
    """Return cache directories that are safe to rebuild on the next cargo invocation."""
    debug_dir = target_dir / "debug"
    return [
        debug_dir / "deps",
        debug_dir / "incremental",
        target_dir / "doc",
        target_dir / "tests",
    ]
