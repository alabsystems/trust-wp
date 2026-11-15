"""Translate-only policy is explicit, pinned, and shared by both credit gates."""

from pathlib import Path
import sys

import pytest

SCRIPTS = Path(__file__).resolve().parents[2] / "scripts"
sys.path.insert(0, str(SCRIPTS))
import creusot_goal_coverage as coverage

POLICY = Path(__file__).with_name("allowlist.toml")


def test_classifier_and_gate_read_the_same_policy():
    from tests.creusot_compat import harness_classify_succeed as classifier

    table = coverage.load_no_replay_goal_table()
    assert tuple(table) == classifier._NO_REPLAY_TRANSLATE_ONLY_ALLOWLIST
    assert table == coverage.NO_REPLAY_TRANSLATE_ONLY_GOAL_TABLE
    for case in table:
        assert classifier._is_translate_only_allowed(f"tests/should_succeed/{case}.rs")
        assert not classifier._is_translate_only_allowed(f"tests/should_fail/{case}.rs")


@pytest.mark.parametrize(
    "old,new",
    [
        ('schema_version = 1', 'schema_version = true'),
        ('schema_version = 1', 'schema_version = 2'),
        ('reference_revision = "', 'reference_revision = "wrong-'),
        ('[[no_replay."bug/653".items]]', '[[no_replay."../bug/653".items]]'),
        ('class = "B"', 'class = "provable"'),
        ('name = "omg"', 'name = ""'),
        ('name = "omg"', 'unknown = "omg"'),
        ('reason = "ensures result@ == n@*(n@+1)/2 on `fn omg(n) -> usize { n }`: n = 2 gives 2 != 3"', 'reason = ""'),
        ('schema_version = 1', 'extra = 1\nschema_version = 1'),
    ],
)
def test_malformed_policy_never_supplies_default_exceptions(tmp_path, old, new):
    original = POLICY.read_text()
    assert old in original
    path = tmp_path / "allowlist.toml"
    path.write_text(original.replace(old, new, 1))
    with pytest.raises(ValueError):
        coverage.load_no_replay_goal_table(path)


def test_duplicate_item_and_empty_table_are_refused(tmp_path):
    path = tmp_path / "allowlist.toml"
    path.write_text(POLICY.read_text() + '\n[[no_replay."bug/653".items]]\nname="omg"\nclass="C"\nreason="duplicate"\n')
    with pytest.raises(ValueError, match="duplicate item"):
        coverage.load_no_replay_goal_table(path)
    path.write_text(POLICY.read_text().split('[[no_replay.')[0] + '[no_replay]\n')
    with pytest.raises(ValueError, match="explicit per-item table"):
        coverage.load_no_replay_goal_table(path)


def test_missing_policy_is_an_error(tmp_path):
    with pytest.raises(FileNotFoundError):
        coverage.load_no_replay_goal_table(tmp_path / "missing.toml")
