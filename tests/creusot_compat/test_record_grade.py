# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
"""Review grades follow typed evidence, independently of persisted labels."""
import copy
from pathlib import Path
import sys

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
import compare_baselines as gate
from creusot_goal_coverage import goal_inventory
from verification_grade import (
    FAILURE_COUNTERS, OPTIONAL_TELEMETRY_FIELDS, STRICT_REJECTION_REASONS,
    TELEMETRY_FIELD_NAMES, recompute_record_grade,
)


NAME = "tests/should_succeed/grade.rs"
COMA = '''module M_h
  let rec h (return (x: bool)) = return {true}
    [ return (result: bool) -> {[@expl:h ensures] result} (! return {result}) ]
end
'''
LABELS = (None, "tier0", "tier0-no-obligation", "tier1", "tier2", "tier2-source-trusted", "tier3", "legacy_unknown", "invented")


@pytest.fixture
def record(tmp_path, monkeypatch):
    source = tmp_path / "reference" / "creusot" / NAME
    source.parent.mkdir(parents=True)
    source.write_text("#[ensures(result)] pub fn h() -> bool { true }")
    source.with_suffix(".coma").write_text(COMA)
    assert len(goal_inventory(NAME, tmp_path / "reference" / "creusot")) == 1
    monkeypatch.setattr(gate, "REPO_ROOT", tmp_path)
    return {
        "name": NAME, "status": "pass", "message": "Verification succeeded",
        "driver_report": ["trust-wp: h verified ✓"],
        "telemetry": {**dict.fromkeys(TELEMETRY_FIELD_NAMES, 0), "verified": 1},
    }


def violations(record):
    return gate.find_true_100_violations({"results": [record]}, "should_succeed")


@pytest.mark.parametrize("label", LABELS)
def test_complete_proof_does_not_depend_on_stored_label(record, label):
    record["verification_tier"] = label
    before = copy.deepcopy(record)
    assert violations(record) == []
    assert record == before


@pytest.mark.parametrize("counter", sorted(FAILURE_COUNTERS | {"trusted"}))
def test_every_unproved_counter_overrules_positive_report_and_label(record, counter):
    record["verification_tier"] = "tier2"
    record["telemetry"][counter] = 1
    reasons = violations(record)[0][1]
    assert f"telemetry.{counter}=1" in reasons
    for label in LABELS:
        record["verification_tier"] = label
        assert violations(record)[0][1] == reasons


@pytest.mark.parametrize("counter", TELEMETRY_FIELD_NAMES)
@pytest.mark.parametrize("value", [True, False, "0", -1])
def test_every_counter_requires_a_nonnegative_integer(record, counter, value):
    record["verification_tier"] = "tier2"
    record["telemetry"][counter] = value
    assert violations(record)


@pytest.mark.parametrize("counter", sorted(set(TELEMETRY_FIELD_NAMES) - OPTIONAL_TELEMETRY_FIELDS))
def test_missing_required_counter_refuses(record, counter):
    del record["telemetry"][counter]
    assert violations(record)


@pytest.mark.parametrize("counter", sorted(OPTIONAL_TELEMETRY_FIELDS))
def test_absent_optional_counter_retains_protocol_compatibility(record, counter):
    del record["telemetry"][counter]
    assert violations(record) == []


def test_positive_prose_and_report_cannot_replace_wire_proof_count(record):
    record["telemetry"]["verified"] = 0
    record["verification_tier"] = "tier2"
    assert "no proved obligation in wire telemetry" in violations(record)[0][1]


def test_native_only_counter_is_a_subset_of_verified(record):
    record["telemetry"]["verified_native_only"] = 2
    assert "telemetry.verified_native_only exceeds verified" in violations(record)[0][1]


def test_unrelated_unproved_item_still_invalidates_a_complete_inventory(record):
    record["driver_report"].append("trust-wp: other unknown (timeout)")
    assert any("unproved driver report" in reason for reason in violations(record)[0][1])


def test_missing_report_or_uncovered_goal_cannot_be_promoted(record):
    for report in (None, []):
        record["driver_report"] = report
        assert violations(record)


def test_source_trusted_proof_is_label_independent(record, tmp_path):
    source = tmp_path / "reference" / "creusot" / NAME
    source.write_text(source.read_text() + "\n#[trusted] pub fn axiom() {}")
    record["trusted_def_paths"] = ["axiom"]
    record["driver_report"].append("trust-wp: axiom trusted (skipped)")
    record["telemetry"].update(trusted=1, base_exit_code=2)
    for label in LABELS:
        record["verification_tier"] = label
        assert violations(record) == []
        assert recompute_record_grade(record, tmp_path).tier == "tier2-source-trusted"


def test_empty_inventory_always_uses_zero_goal_parity(record, tmp_path):
    (tmp_path / "reference" / "creusot" / NAME).with_suffix(".coma").write_text("module M_h\nend\n")
    for label in LABELS:
        record["verification_tier"] = label
        assert violations(record) == []
        assert recompute_record_grade(record, tmp_path).tier == "tier0-no-obligation"
    record["telemetry"]["errors"] = 1
    assert violations(record)


def test_only_named_strict_rejection_with_observed_variant_failure_passes(record):
    name = next(iter(STRICT_REJECTION_REASONS))
    record.update(name=name, message="Correctly rejected (strict): known variant rejection")
    record["telemetry"].update(failed=1, base_exit_code=1)
    record["driver_report"] = ["trust-wp: variant_is_not_checked FAILED ✗ (variant decrease)"]
    for label in LABELS:
        record["verification_tier"] = label
        assert violations(record) == []
    record["driver_report"] = []
    assert violations(record)
    record["driver_report"] = ["trust-wp: variant_is_not_checked FAILED ✗ (postcondition)"]
    assert violations(record)
    record["driver_report"] = ["trust-wp: variant_is_not_checked FAILED ✗ (variant decrease)"]
    record["name"] = NAME
    assert violations(record)


def test_trusted_report_requires_matching_source_and_counter_accounting(record):
    record["driver_report"].append("trust-wp: axiom trusted (skipped)")
    assert any("unaccounted trusted" in reason for reason in violations(record)[0][1])


def test_negative_summary_cannot_hide_behind_clean_typed_counters(record):
    record["driver_report"].append("trust-wp: 1 verified, 1 failed, 0 errors")
    assert any("unproved driver summary" in reason for reason in violations(record)[0][1])
