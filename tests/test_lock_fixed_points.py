#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Static tests for the committed Cargo lock fixed-point gate."""

from __future__ import annotations

import importlib.util
import subprocess
import sys
import time
from collections import Counter
from contextlib import nullcontext
from pathlib import Path

import pytest


WORKSPACE_ROOT = Path(__file__).resolve().parent.parent
SCRIPT = WORKSPACE_ROOT / "scripts" / "check_lock_fixed_points.py"
SPEC = importlib.util.spec_from_file_location("check_lock_fixed_points", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
LOCK_GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(LOCK_GATE)


def _lane(lockfile: Path) -> str:
    parts = lockfile.parts
    if lockfile == Path("Cargo.lock"):
        return "root"
    if parts[:2] == ("dependency-modes", "trust"):
        return "dependency-mode"
    if parts[0] == "examples":
        return "example"
    if parts[0] == "iface":
        return "interface"
    if parts[0] == "spikes":
        return "spike"
    if parts[:2] == ("tests", "fixtures"):
        return "fixture"
    return "unexpected"


def test_tracked_lockfile_census_covers_every_live_lane() -> None:
    lockfiles = LOCK_GATE.discover_lockfiles(WORKSPACE_ROOT)
    assert len(lockfiles) == 61
    assert Counter(map(_lane, lockfiles)) == {
        "root": 1,
        "dependency-mode": 1,
        "example": 1,
        "interface": 1,
        "spike": 41,
        "fixture": 16,
    }


def test_fixed_point_check_resolves_the_complete_dependency_graph() -> None:
    command = LOCK_GATE.cargo_metadata_command(locked=True, offline=False)
    assert command[-4:] == ["metadata", "--locked", "--format-version", "1"]
    assert "--no-deps" not in command


def test_repair_preserves_existing_resolutions_before_locked_recheck() -> None:
    command = LOCK_GATE.cargo_metadata_command(locked=False, offline=True)
    assert command[-4:] == ["metadata", "--offline", "--format-version", "1"]
    assert "generate-lockfile" not in command


def test_failed_repair_can_restore_every_lock_byte_for_byte(tmp_path: Path) -> None:
    first = Path("Cargo.lock")
    second = Path("nested/Cargo.lock")
    (tmp_path / second.parent).mkdir()
    (tmp_path / first).write_bytes(b"first\r\n")
    (tmp_path / second).write_bytes(b"second\n")

    snapshot = LOCK_GATE.snapshot_lockfiles([first, second], tmp_path)
    (tmp_path / first).write_bytes(b"changed first\n")
    (tmp_path / second).write_bytes(b"changed second\n")
    LOCK_GATE.restore_lockfiles(snapshot, tmp_path)

    assert (tmp_path / first).read_bytes() == b"first\r\n"
    assert (tmp_path / second).read_bytes() == b"second\n"


class _FakeHermeticRoot:
    def __init__(self, *, keep: bool = False) -> None:
        self.keep = keep

    def close(self) -> None:
        pass


def _patch_transaction_inputs(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, lockfiles: list[Path]
) -> None:
    monkeypatch.setattr(LOCK_GATE, "WORKSPACE_ROOT", tmp_path)
    monkeypatch.setattr(LOCK_GATE, "discover_lockfiles", lambda: lockfiles)
    monkeypatch.setattr(LOCK_GATE, "read_pins", lambda: {"ay": "a" * 40})
    monkeypatch.setattr(LOCK_GATE, "HermeticRoot", _FakeHermeticRoot)
    monkeypatch.setattr(
        LOCK_GATE,
        "workspace_repair_lock",
        lambda _root, **_kwargs: nullcontext(),
    )


def test_repair_rolls_back_when_a_late_lock_is_unverifiable(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    first = Path("Cargo.lock")
    second = Path("nested/Cargo.lock")
    (tmp_path / second.parent).mkdir()
    (tmp_path / first).write_text("first\n", encoding="utf-8")
    (tmp_path / second).write_text("second\n", encoding="utf-8")
    _patch_transaction_inputs(monkeypatch, tmp_path, [first, second])

    def sweep(lockfiles: list[Path], **kwargs: object) -> list[object]:
        assert kwargs["write_back"] is True
        (tmp_path / first).write_text("changed\n", encoding="utf-8")
        return [
            LOCK_GATE.Outcome(first, LOCK_GATE.VERIFIED, True),
            LOCK_GATE.Outcome(second, LOCK_GATE.UNVERIFIABLE, True, "late failure"),
        ]

    monkeypatch.setattr(LOCK_GATE, "run_sweep", sweep)
    assert LOCK_GATE.main(["--repair"]) == LOCK_GATE.EXIT_UNVERIFIABLE
    assert (tmp_path / first).read_text(encoding="utf-8") == "first\n"
    assert (tmp_path / second).read_text(encoding="utf-8") == "second\n"


def test_repair_keeps_drift_distinct_while_rolling_back(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    lockfile = Path("Cargo.lock")
    (tmp_path / lockfile).write_text("old\n", encoding="utf-8")
    _patch_transaction_inputs(monkeypatch, tmp_path, [lockfile])

    def sweep(lockfiles: list[Path], **kwargs: object) -> list[object]:
        assert kwargs["write_back"] is True
        (tmp_path / lockfile).write_text("new\n", encoding="utf-8")
        return [LOCK_GATE.Outcome(lockfile, LOCK_GATE.DRIFTED, True, "drift")]

    monkeypatch.setattr(LOCK_GATE, "run_sweep", sweep)
    assert LOCK_GATE.main(["--repair"]) == LOCK_GATE.EXIT_DRIFTED
    assert (tmp_path / lockfile).read_text(encoding="utf-8") == "old\n"


def test_repair_rolls_back_and_stays_unverifiable_when_final_check_fails(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    lockfile = Path("Cargo.lock")
    (tmp_path / lockfile).write_text("old\n", encoding="utf-8")
    _patch_transaction_inputs(monkeypatch, tmp_path, [lockfile])

    def sweep(lockfiles: list[Path], **kwargs: object) -> list[object]:
        if kwargs["write_back"]:
            (tmp_path / lockfile).write_text("new\n", encoding="utf-8")
            return [LOCK_GATE.Outcome(lockfile, LOCK_GATE.VERIFIED, True)]
        assert (tmp_path / lockfile).read_text(encoding="utf-8") == "new\n"
        return [
            LOCK_GATE.Outcome(
                lockfile, LOCK_GATE.UNVERIFIABLE, True, "late network failure"
            )
        ]

    monkeypatch.setattr(LOCK_GATE, "run_sweep", sweep)
    assert (
        LOCK_GATE.main(["--repair", "--allow-unverifiable"])
        == LOCK_GATE.EXIT_UNVERIFIABLE
    )
    assert (tmp_path / lockfile).read_text(encoding="utf-8") == "old\n"


def test_repair_rolls_back_when_reporting_raises_after_both_sweeps(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    lockfile = Path("Cargo.lock")
    (tmp_path / lockfile).write_text("old\n", encoding="utf-8")
    _patch_transaction_inputs(monkeypatch, tmp_path, [lockfile])

    def sweep(lockfiles: list[Path], **kwargs: object) -> list[object]:
        if kwargs["write_back"]:
            (tmp_path / lockfile).write_text("new\n", encoding="utf-8")
        return [LOCK_GATE.Outcome(lockfile, LOCK_GATE.VERIFIED, True)]

    def fail_after_repair(*args: object, **kwargs: object) -> int:
        raise RuntimeError("injected post-repair reporting failure")

    monkeypatch.setattr(LOCK_GATE, "run_sweep", sweep)
    monkeypatch.setattr(LOCK_GATE, "report", fail_after_repair)
    with pytest.raises(RuntimeError, match="post-repair reporting"):
        LOCK_GATE.main(["--repair"])
    assert (tmp_path / lockfile).read_text(encoding="utf-8") == "old\n"


def test_repair_rolls_back_when_hermetic_close_raises_after_repair(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    lockfile = Path("Cargo.lock")
    (tmp_path / lockfile).write_text("old\n", encoding="utf-8")
    _patch_transaction_inputs(monkeypatch, tmp_path, [lockfile])

    class FailingClose(_FakeHermeticRoot):
        def close(self) -> None:
            raise RuntimeError("injected close failure")

    def sweep(lockfiles: list[Path], **kwargs: object) -> list[object]:
        if kwargs["write_back"]:
            (tmp_path / lockfile).write_text("new\n", encoding="utf-8")
        return [LOCK_GATE.Outcome(lockfile, LOCK_GATE.VERIFIED, True)]

    monkeypatch.setattr(LOCK_GATE, "HermeticRoot", FailingClose)
    monkeypatch.setattr(LOCK_GATE, "run_sweep", sweep)
    with pytest.raises(RuntimeError, match="close failure"):
        LOCK_GATE.main(["--repair"])
    assert (tmp_path / lockfile).read_text(encoding="utf-8") == "old\n"


def test_repair_dry_run_is_repeatable_and_never_persists_changes(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    lockfile = Path("Cargo.lock")
    (tmp_path / lockfile).write_text("old\n", encoding="utf-8")
    _patch_transaction_inputs(monkeypatch, tmp_path, [lockfile])
    repairs = 0

    def sweep(lockfiles: list[Path], **kwargs: object) -> list[object]:
        nonlocal repairs
        if kwargs["write_back"]:
            repairs += 1
            assert (tmp_path / lockfile).read_text(encoding="utf-8") == "old\n"
            (tmp_path / lockfile).write_text("new\n", encoding="utf-8")
        else:
            assert (tmp_path / lockfile).read_text(encoding="utf-8") == "new\n"
        return [LOCK_GATE.Outcome(lockfile, LOCK_GATE.VERIFIED, True)]

    monkeypatch.setattr(LOCK_GATE, "run_sweep", sweep)
    for _ in range(2):
        assert LOCK_GATE.main(["--repair", "--dry-run"]) == LOCK_GATE.EXIT_OK
        assert (tmp_path / lockfile).read_text(encoding="utf-8") == "old\n"
    assert repairs == 2


def test_dry_run_requires_repair() -> None:
    assert LOCK_GATE.main(["--dry-run"]) == LOCK_GATE.EXIT_DRIFTED


@pytest.mark.parametrize(
    "waiter_mode", ["exclusive", "shared"], ids=["repair-vs-repair", "repair-vs-check"]
)
def test_workspace_repair_lock_serializes_concurrent_processes(
    tmp_path: Path, waiter_mode: str
) -> None:
    subprocess.run(
        ["git", "init", "-q", "-b", "main", str(tmp_path)],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    first_acquired = tmp_path / "first-acquired"
    release_first = tmp_path / "release-first"
    second_acquired = tmp_path / "second-acquired"
    holder = """
import pathlib, runpy, sys, time
gate = runpy.run_path(sys.argv[1])["workspace_repair_lock"]
with gate(pathlib.Path(sys.argv[2]), exclusive=True):
    pathlib.Path(sys.argv[3]).write_text("acquired\\n")
    while not pathlib.Path(sys.argv[4]).exists():
        time.sleep(0.01)
"""
    waiter = """
import pathlib, runpy, sys
gate = runpy.run_path(sys.argv[1])["workspace_repair_lock"]
with gate(pathlib.Path(sys.argv[2]), exclusive=sys.argv[4] == "exclusive"):
    pathlib.Path(sys.argv[3]).write_text("acquired\\n")
"""
    first = subprocess.Popen(
        [
            sys.executable,
            "-c",
            holder,
            str(SCRIPT),
            str(tmp_path),
            str(first_acquired),
            str(release_first),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    second: subprocess.Popen[str] | None = None
    try:
        deadline = time.monotonic() + 5
        while not first_acquired.exists() and time.monotonic() < deadline:
            time.sleep(0.01)
        assert first_acquired.exists(), first.communicate(timeout=1)

        second = subprocess.Popen(
            [
                sys.executable,
                "-c",
                waiter,
                str(SCRIPT),
                str(tmp_path),
                str(second_acquired),
                waiter_mode,
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        time.sleep(0.2)
        assert second.poll() is None
        assert not second_acquired.exists()

        release_first.write_text("release\n", encoding="utf-8")
        first_stdout, first_stderr = first.communicate(timeout=5)
        second_stdout, second_stderr = second.communicate(timeout=5)
        assert first.returncode == 0, (first_stdout, first_stderr)
        assert second.returncode == 0, (second_stdout, second_stderr)
        assert second_acquired.is_file()
    finally:
        release_first.touch(exist_ok=True)
        if first.poll() is None:
            first.kill()
            first.wait()
        if second is not None and second.poll() is None:
            second.kill()
            second.wait()


def test_spike_suite_invokes_lock_fixed_point_gate() -> None:
    run_all = (WORKSPACE_ROOT / "spikes" / "run-all.sh").read_text(encoding="utf-8")
    assert run_all.count("../scripts/check_lock_fixed_points.py") == 1


def test_every_sibling_dependent_lock_is_named_by_the_declared_pins() -> None:
    """A lock that escapes the repository must be pinned, not left to the machine."""

    pins = LOCK_GATE.read_pins(WORKSPACE_ROOT)
    assert set(pins) == {"clean", "ay", "trust-ir", "trust-cg", "trust"}
    assert all(len(commit) == 40 for commit in pins.values())

    search_root = LOCK_GATE.escape_root(WORKSPACE_ROOT)
    escaping = {}
    for lockfile in LOCK_GATE.discover_lockfiles(WORKSPACE_ROOT):
        references = LOCK_GATE.escaping_references(lockfile, WORKSPACE_ROOT)
        if references:
            escaping[lockfile] = {
                reference.relative_to(search_root).parts[0] for reference in references
            }
    # Every escape lands on a repository DEPENDS.lock actually declares; an
    # undeclared one would silently reintroduce the developer's own checkout.
    assert set().union(*escaping.values()) <= set(pins)
    assert all(_lane(lockfile) == "spike" for lockfile in escaping if _lane(lockfile) == "spike")
    assert len(escaping) == 44


def test_in_place_locks_are_exactly_the_ones_that_never_leave_the_repository() -> None:
    lockfiles = LOCK_GATE.discover_lockfiles(WORKSPACE_ROOT)
    in_place = [
        lockfile
        for lockfile in lockfiles
        if not LOCK_GATE.escaping_references(lockfile, WORKSPACE_ROOT)
        and lockfile != LOCK_GATE.TRUST_MODE_LOCK
    ]
    assert Counter(map(_lane, in_place)) == {"fixture": 16, "example": 1}


def test_trust_dependency_mode_resolves_at_the_repository_root() -> None:
    """The importer manifest only means what it says from the root it replaces."""

    manifest, anchor = LOCK_GATE.lock_plan(LOCK_GATE.TRUST_MODE_LOCK, WORKSPACE_ROOT)
    assert manifest == WORKSPACE_ROOT / "dependency-modes" / "trust" / "Cargo.toml"
    assert anchor == WORKSPACE_ROOT
    escapes = LOCK_GATE.escaping_references(LOCK_GATE.TRUST_MODE_LOCK, WORKSPACE_ROOT)
    assert {reference.name for reference in escapes} >= {"ay-core", "trust-ir"}


def test_hermetic_clone_covers_every_directory_a_tracked_lock_lives_in() -> None:
    """A pinned lock is resolved in the clone, so the clone must contain it."""

    covered = set(LOCK_GATE.HERMETIC_TREES)
    for lockfile in LOCK_GATE.discover_lockfiles(WORKSPACE_ROOT):
        if lockfile == Path("Cargo.lock"):
            continue
        assert lockfile.parts[0] in covered, lockfile


def test_only_cargos_own_locked_refusal_counts_as_drift() -> None:
    """Anything else is a statement about the machine, never about the lock."""

    refusal = (
        "error: cannot update the lock file /x/Cargo.lock because --locked was "
        "passed to prevent this"
    )
    assert LOCK_GATE._LOCKED_REFUSAL.search(refusal)
    for machine_failure in (
        "failed to read `/x/Cargo.toml`\n\nCaused by:\n  No such file or directory",
        "error: no matching package named `foo` found",
        "error: failed to load manifest for workspace member `/x`",
    ):
        assert not LOCK_GATE._LOCKED_REFUSAL.search(machine_failure)


def test_repair_refuses_a_rollback() -> None:
    """Refreshing against a drifted sibling rewrites first-party crates backwards."""

    before = (
        '[[package]]\nname = "ay-core"\nversion = "0.11.0"\n\n'
        '[[package]]\nname = "clean-kernel"\nversion = "1.2.0"\n'
    )
    forward = (
        '[[package]]\nname = "ay-core"\nversion = "0.15.0"\n\n'
        '[[package]]\nname = "clean-kernel"\nversion = "1.2.0"\n'
    )
    rolled_back = (
        '[[package]]\nname = "ay-core"\nversion = "0.5.0"\n'
        'source = "git+https://github.com/alabsystems/ay.git?rev=95e1b431"\n\n'
        '[[package]]\nname = "clean-kernel"\nversion = "1.2.0"\n'
    )
    assert LOCK_GATE.detect_rollback(before, forward) == []
    findings = LOCK_GATE.detect_rollback(before, rolled_back)
    assert any("ay-core" in finding and "downgrade" in finding for finding in findings)
    assert any("git source" in finding for finding in findings)


def test_declared_pin_rejects_wrong_origin_with_matching_sha() -> None:
    """A matching rev/fragment cannot authenticate a different repository."""

    declared = LOCK_GATE.read_pins()["ay"]
    source = (
        "git+https://example.invalid/alabsystems/ay.git"
        f"?rev={declared}#{declared}"
    )
    assert not LOCK_GATE.lands_on_declared_pin(
        "ay-core", {("0.19.0", source)}
    )


def test_declared_pin_rejects_moving_selector_with_matching_fragment() -> None:
    """A resolved fragment cannot turn branch=main into an exact authority."""

    declared = LOCK_GATE.read_pins()["trust-ir"]
    moving = (
        "git+https://github.com/alabsystems/trust-ir.git"
        f"?branch=main#{declared}"
    )
    assert not LOCK_GATE.lands_on_declared_pin(
        "trust-ir", {("0.11.0", moving)}
    )
    exact = (
        "git+https://github.com/alabsystems/trust-ir.git"
        f"?rev={declared}#{declared}"
    )
    assert LOCK_GATE.lands_on_declared_pin(
        "trust-ir", {("0.11.0", exact)}
    )


def _cargo_bare_database(
    tmp_path: Path,
    database: Path,
    candidate_name: str,
    github_repository: str,
) -> tuple[Path, str]:
    worktree = tmp_path / f"work-{candidate_name}"
    subprocess.run(
        ["git", "init", "-q", "-b", "main", str(worktree)],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    subprocess.run(
        ["git", "-C", str(worktree), "config", "user.email", "db-test@example.invalid"],
        check=True,
    )
    subprocess.run(
        ["git", "-C", str(worktree), "config", "user.name", "Cargo DB Test"],
        check=True,
    )
    (worktree / "marker").write_text(f"{candidate_name}\n", encoding="utf-8")
    subprocess.run(
        ["git", "-C", str(worktree), "add", "marker"],
        check=True,
    )
    subprocess.run(
        ["git", "-C", str(worktree), "commit", "-q", "-m", "marker"],
        check=True,
    )
    revision = subprocess.check_output(
        ["git", "-C", str(worktree), "rev-parse", "HEAD"], text=True
    ).strip()
    candidate = database / candidate_name
    candidate.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        ["git", "clone", "-q", "--bare", str(worktree), str(candidate)],
        check=True,
    )
    (candidate / "FETCH_HEAD").write_text(
        f"{revision}\t\t'{revision}' of "
        f"https://github.com/{github_repository}.git\n",
        encoding="utf-8",
    )
    return candidate, revision


@pytest.mark.parametrize("collision", ["trust-cg", "trust-ir"])
def test_cargo_database_prefix_collision_cannot_impersonate_trust(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path, collision: str
) -> None:
    database = tmp_path / "cargo" / "git" / "db"
    candidate, revision = _cargo_bare_database(
        tmp_path,
        database,
        f"{collision}-0123456789abcdef",
        f"{LOCK_GATE.FIRST_PARTY_ORG}/{collision}",
    )
    monkeypatch.setattr(LOCK_GATE, "cargo_git_database", lambda: database)
    search_root = tmp_path / "siblings"
    search_root.mkdir()

    assert LOCK_GATE.object_source("trust", search_root, revision) is None
    assert LOCK_GATE.object_source(collision, search_root, revision) == candidate


def test_cargo_database_search_continues_until_requested_revision(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    database = tmp_path / "cargo" / "git" / "db"
    _first, first_revision = _cargo_bare_database(
        tmp_path,
        database,
        "trust-0000000000000000",
        "alabsystems/trust",
    )
    second, requested_revision = _cargo_bare_database(
        tmp_path,
        database,
        "trust-1111111111111111",
        "alabsystems/trust",
    )
    monkeypatch.setattr(LOCK_GATE, "cargo_git_database", lambda: database)
    search_root = tmp_path / "siblings"
    search_root.mkdir()

    assert first_revision != requested_revision
    assert (
        LOCK_GATE.object_source("trust", search_root, requested_revision) == second
    )


def test_cargo_database_rejects_foreign_same_basename(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    database = tmp_path / "cargo" / "git" / "db"
    _candidate, revision = _cargo_bare_database(
        tmp_path,
        database,
        "trust-0123456789abcdef",
        "someone-else/trust",
    )
    monkeypatch.setattr(LOCK_GATE, "cargo_git_database", lambda: database)
    search_root = tmp_path / "siblings"
    search_root.mkdir()

    assert LOCK_GATE.object_source("trust", search_root, revision) is None


def test_verdicts_and_exit_codes_keep_unverifiable_distinct_from_both() -> None:
    assert (LOCK_GATE.VERIFIED, LOCK_GATE.DRIFTED, LOCK_GATE.UNVERIFIABLE) == (
        "VERIFIED",
        "DRIFTED",
        "UNVERIFIABLE",
    )
    assert LOCK_GATE.EXIT_OK == 0
    assert LOCK_GATE.EXIT_DRIFTED == 1
    # An unobtainable pin is not a lockfile defect and not a pass.
    assert LOCK_GATE.EXIT_UNVERIFIABLE not in (LOCK_GATE.EXIT_OK, LOCK_GATE.EXIT_DRIFTED)


def test_pin_digest_keys_the_cache_on_the_pins_and_nothing_else() -> None:
    base = {"clean": "a" * 40, "ay": "b" * 40}
    assert LOCK_GATE.pin_digest(base) == LOCK_GATE.pin_digest(dict(reversed(base.items())))
    assert LOCK_GATE.pin_digest(base) != LOCK_GATE.pin_digest({**base, "ay": "c" * 40})


def test_package_moves_report_direction_per_package() -> None:
    before = '[[package]]\nname = "ay-core"\nversion = "0.11.0"\n'
    after = '[[package]]\nname = "ay-core"\nversion = "0.15.0"\n'
    assert LOCK_GATE.package_moves(before, after) == ["ay-core 0.11.0 -> 0.15.0"]


def test_direction_follows_history_not_version_numbers() -> None:
    """A first-party sibling may renumber; semver then orders nothing.

    ``clean`` ran 1.2.0 -> 1.3.0 -> ... -> 1.6.0 and was reset to 0.1.0 by
    "the 1.x line is reserved for public-readiness", then climbed to 0.4.0. So
    clean-kernel 0.4.0 is FIVE releases newer than 1.4.0 while comparing lower
    under semver, and the mistake runs both ways: 0.4.0 -> 1.2.0 looks like an
    upgrade and is nine releases backwards.

    Calling either one wrong is expensive. A false rollback blocks a refresh
    that should happen; a false forward waves through the downgrade the guard
    exists to catch.
    """

    timeline = LOCK_GATE.workspace_version_timeline(
        LOCK_GATE.object_source("clean", LOCK_GATE.first_party_root())
    )
    if not timeline:
        return  # no clean object store on this machine; nothing to assert
    assert "0.4.0" in timeline and "1.4.0" in timeline, timeline
    assert timeline.index("0.4.0") < timeline.index("1.4.0"), (
        f"0.4.0 must be newer than 1.4.0 in clean's history: {timeline}"
    )

    # Forward despite comparing lower.
    assert LOCK_GATE.move_is_forward_in_history("clean-kernel", "1.4.0", "0.4.0") is True
    # Backwards despite comparing higher.
    assert LOCK_GATE.move_is_forward_in_history("clean-kernel", "0.4.0", "1.2.0") is False
    # Within one series, ordinary ordering still holds.
    assert LOCK_GATE.move_is_forward_in_history("clean-kernel", "1.2.0", "1.4.0") is True


def test_unanswerable_direction_keeps_the_strict_verdict() -> None:
    """`None` means unknown, and unknown must not read as safe.

    A third-party crate has no declared sibling to ask, so the answer is
    `None` and `detect_rollback` falls back to semver rather than treating an
    unanswerable move as forward.
    """

    assert LOCK_GATE.first_party_repository("serde") is None
    assert LOCK_GATE.move_is_forward_in_history("serde", "1.0.0", "0.9.0") is None
    # The semver fallback still reports a real third-party downgrade.
    before = '[[package]]\nname = "serde"\nversion = "1.0.0"\n'
    after = '[[package]]\nname = "serde"\nversion = "0.9.0"\n'
    assert LOCK_GATE.detect_rollback(before, after), "third-party downgrade must still be caught"
