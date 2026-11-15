"""The decision ledger is append-only, and its numbers are its anchors.

Two fronts that branch from the same tip both number their entries from the same
place, so every parallel front collides in this file. The resolution keeps BOTH
sides and renumbers the incoming one -- and a renumbering done as two passes
(headings first, then references) shifts a heading twice wherever the two ranges
overlap, producing duplicate numbers that read like a clean sequence until you
count them. These are what counting looks like as a test.

A `D-NN` in a source comment or an adversarial case header is an anchor into this
file. A renumbered ledger with stale anchors is worse than either alone, so the
anchors are checked too.
"""
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / "docs" / "DECISIONS.md"
HEADING = re.compile(r"^## D-(\d+)", re.MULTILINE)
REFERENCE = re.compile(r"D-(\d+)")


def _numbers() -> list[int]:
    return [int(n) for n in HEADING.findall(LEDGER.read_text())]


def test_the_ledger_has_entries():
    # A file that stopped matching would make every other check here vacuous.
    assert len(_numbers()) > 50


def test_no_decision_number_is_used_twice():
    repeated = sorted(n for n, count in Counter(_numbers()).items() if count > 1)
    assert not repeated, f"D-{repeated} each appear more than once"


def test_the_numbers_are_dense_and_ascending():
    numbers = _numbers()
    assert numbers == sorted(numbers), "entries are out of order"
    assert numbers == list(range(numbers[0], numbers[0] + len(numbers))), "a number is missing"


def test_every_reference_in_the_ledger_resolves():
    existing = set(_numbers())
    referenced = {int(n) for n in REFERENCE.findall(LEDGER.read_text())}
    assert not referenced - existing, f"ledger cites missing {sorted(referenced - existing)}"


def test_every_anchor_in_the_tree_resolves():
    existing = set(_numbers())
    dangling: dict[int, list[str]] = {}
    for path in list((ROOT / "crates").rglob("*.rs")) + list((ROOT / "tests").rglob("*.rs")):
        try:
            text = path.read_text(errors="replace")
        except OSError:
            continue
        for number in {int(n) for n in REFERENCE.findall(text)} - existing:
            dangling.setdefault(number, []).append(str(path.relative_to(ROOT)))
    assert not dangling, f"anchors naming no entry: {dangling}"
