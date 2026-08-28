#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

"""Static tests for the committed Cargo lock fixed-point gate."""

from __future__ import annotations

import importlib.util
from collections import Counter
from pathlib import Path


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
