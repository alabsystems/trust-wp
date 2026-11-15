# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Every path a source file embeds must exist.

A deletion elsewhere in the tree can orphan an ``include_str!`` and the break
only surfaces when that crate's TEST target is compiled -- which a merge check
scoped to a couple of packages never does. This test compiles nothing, so it
catches the class in a second instead of a full workspace build.
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path

WORKSPACE_ROOT = Path(__file__).resolve().parent.parent

_EMBED = re.compile(
    r'include_str!\s*\(\s*concat!\((?P<concat>.*?)\)\s*\)'
    r'|include_str!\s*\(\s*"(?P<direct>[^"]+)"\s*\)'
    r'|include_bytes!\s*\(\s*"(?P<bytes>[^"]+)"\s*\)',
    re.S,
)


def _tracked_rust_sources() -> list[Path]:
    out = subprocess.run(
        ["git", "ls-files", "*.rs"],
        cwd=WORKSPACE_ROOT, check=True, capture_output=True, text=True,
    ).stdout.split()
    return [WORKSPACE_ROOT / p for p in out]


def _crate_root(source: Path) -> Path | None:
    """The directory holding the nearest Cargo.toml -- CARGO_MANIFEST_DIR."""
    for parent in source.parents:
        if (parent / "Cargo.toml").exists():
            return parent
        if parent == WORKSPACE_ROOT:
            break
    return None


def _embedded_targets(source: Path) -> list[tuple[Path, str]]:
    """Each embedded path, paired with the directory it is anchored at.

    The two forms anchor differently and getting it wrong makes this guard
    lie in both directions: `concat!(env!("CARGO_MANIFEST_DIR"), "/x")` is
    relative to the CRATE root, a bare `include_str!("x")` to the FILE.
    """
    text = source.read_text(errors="replace")
    targets: list[tuple[Path, str]] = []
    for match in _EMBED.finditer(text):
        if match.group("concat") is not None:
            frag = match.group("concat")
            pieces = re.findall(r'"([^"]*)"', frag)
            # Drop the env!() key itself; it names the anchor, not a segment.
            literals = [x for x in pieces if x != "CARGO_MANIFEST_DIR"]
            if not literals or "CARGO_MANIFEST_DIR" not in frag:
                continue  # some other concat! we cannot resolve statically
            anchor = _crate_root(source)
            if anchor is None:
                continue
            targets.append((anchor, "".join(literals)))
        else:
            targets.append((source.parent, match.group("direct") or match.group("bytes")))
    return targets


def test_every_embedded_path_exists() -> None:
    missing = []
    checked = 0
    for source in _tracked_rust_sources():
        for anchor, target in _embedded_targets(source):
            if "$" in target or "{" in target:
                continue  # built at compile time, not a literal path
            checked += 1
            resolved = (anchor / target.lstrip("/")).resolve()
            if not resolved.exists():
                missing.append(
                    f"{source.relative_to(WORKSPACE_ROOT)} embeds {target!r} "
                    f"-> {resolved} (does not exist)"
                )
    assert checked, "found no embedded paths at all -- the matcher stopped matching"
    assert not missing, "embedded paths that no longer resolve:\n" + "\n".join(missing)
