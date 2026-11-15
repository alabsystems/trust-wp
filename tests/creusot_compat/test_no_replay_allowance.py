"""A neutral line mentioning "verified" never raises the translate-only allowance."""
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))

import creusot_goal_coverage as cov  # noqa: E402

PEARLITE = "tests/should_succeed/syntax/05_pearlite.rs"


def test_neutral_logic_fn_line_does_not_raise_allowance():
    lines = ["trust-wp: has_len_3 is a logic function (postcondition will be verified)"]
    reasons = cov.no_replay_translate_only_refusals(
        PEARLITE, lines, {"verified": 1, "proof_assert_verified": 0}
    )
    assert any("exceeds the 0" in r for r in reasons), reasons


def test_real_positive_line_on_trusted_strip_item_still_allowed():
    lines = ["trust-wp: solver verified ✓"]
    assert cov.no_replay_translate_only_refusals(
        PEARLITE, lines, {"verified": 1, "proof_assert_verified": 0}
    ) == []


def test_refutable_item_mentioned_as_verified_is_still_refused():
    lines = ["trust-wp: struct_in_pearlite verified ✓"]
    reasons = cov.no_replay_translate_only_refusals(
        PEARLITE, lines, {"verified": 1, "proof_assert_verified": 0}
    )
    assert any("struct_in_pearlite" in r for r in reasons), reasons
