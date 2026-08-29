// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ── report_obligation_result counter accounting tests (#1996) ────────────────
//
// `report_obligation_result` delegates to `classify_obligation_result` for the
// `Ok(...)` branches and applies the returned deltas to a mutable
// `VerificationCounters`. The `Err(EncodingError)` branch records the error in
// `encoding_errors` and increments `errors`. These tests exercise the counter
// mutation logic for all 5 branches + the `Err` path.

/// Simulates the `Ok(outcome)` path of `report_obligation_result`: classify the
/// provenance-preserving outcome, then apply deltas to counters.
fn apply_ok_outcome_branch(
    counters: &mut VerificationCounters,
    outcome: VerificationOutcome,
) -> ObligationOutcome {
    let (outcome, delta_failed, delta_errors, delta_demoted, delta_evidence_gaps, delta_warnings) =
        classify_obligation_outcome(outcome, "test::fn", "test.rs:1");
    counters.failed += delta_failed;
    counters.errors += delta_errors;
    counters.demoted += delta_demoted;
    counters.evidence_gaps += delta_evidence_gaps;
    counters.warnings += delta_warnings;
    if matches!(outcome, ObligationOutcome::Vacuous) {
        counters.vacuous += 1;
        counters.warnings += 1;
    }
    if matches!(outcome, ObligationOutcome::Assumed(_)) {
        counters.assumed += 1;
    }
    outcome
}

#[test]
fn report_obligation_verified_without_provenance_records_evidence_gap() {
    let mut counters = VerificationCounters::default();
    let outcome = apply_ok_outcome_branch(
        &mut counters,
        VerificationOutcome::without_provenance(VerificationResult::Verified(None)),
    );
    assert_eq!(outcome, ObligationOutcome::EvidenceGap);
    assert_eq!(counters.failed, 0);
    assert_eq!(counters.errors, 0);
    assert_eq!(counters.demoted, 0);
    assert_eq!(counters.verified, 0);
    assert_eq!(counters.evidence_gaps, 1);
    assert_eq!(counters.warnings, 1);
}

#[test]
fn report_obligation_assumed_increments_assumed_only() {
    let mut counters = VerificationCounters::default();
    let outcome = apply_ok_outcome_branch(
        &mut counters,
        VerificationOutcome::without_provenance(VerificationResult::Assumed("axiom-only".into())),
    );
    assert_eq!(
        outcome,
        ObligationOutcome::Assumed("axiom-only".to_string())
    );
    assert_eq!(counters.failed, 0, "Assumed must not touch failed");
    assert_eq!(counters.errors, 0, "Assumed must not touch errors");
    assert_eq!(counters.demoted, 0, "Assumed must not touch demoted");
    assert_eq!(counters.assumed, 1, "Assumed must remain visible");
}

#[test]
fn report_obligation_failed_increments_failed_counter() {
    let mut counters = VerificationCounters {
        failed: 2,
        errors: 1,
        ..VerificationCounters::default()
    };
    let cex = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let outcome = apply_ok_outcome_branch(
        &mut counters,
        VerificationOutcome::without_provenance(VerificationResult::Failed(cex)),
    );
    assert_eq!(outcome, ObligationOutcome::ErrorRecorded);
    assert_eq!(
        counters.failed, 3,
        "Failed must increment failed from 2 to 3"
    );
    assert_eq!(counters.errors, 1, "Failed must not touch errors");
    assert_eq!(counters.demoted, 0, "Failed must not touch demoted");
}

#[test]
fn report_obligation_unknown_increments_errors_counter() {
    let mut counters = VerificationCounters {
        errors: 5,
        ..VerificationCounters::default()
    };
    let outcome = apply_ok_outcome_branch(
        &mut counters,
        VerificationOutcome::without_provenance(VerificationResult::Unknown(
            UnknownReason::Timeout,
        )),
    );
    assert_eq!(outcome, ObligationOutcome::ErrorRecorded);
    assert_eq!(counters.failed, 0, "Unknown must not touch failed");
    assert_eq!(
        counters.errors, 6,
        "Unknown must increment errors from 5 to 6"
    );
    assert_eq!(
        counters.demoted, 0,
        "Non-demoted unknown must not touch demoted"
    );
}

#[test]
fn report_obligation_vacuous_records_vacuous_warning_not_verified() {
    let mut counters = VerificationCounters::default();
    let outcome = apply_ok_outcome_branch(
        &mut counters,
        VerificationOutcome::without_provenance(VerificationResult::Unknown(
            UnknownReason::SolverMessage(
                "vacuous proof: base assertions are UNSAT without the negated postcondition".into(),
            ),
        )),
    );
    assert_eq!(outcome, ObligationOutcome::Vacuous);
    assert_eq!(counters.verified, 0, "Vacuous must not increment verified");
    assert_eq!(counters.vacuous, 1, "Vacuous must be visible in telemetry");
    assert_eq!(
        counters.warnings, 1,
        "Vacuous loop obligations are warnings"
    );
    assert_eq!(counters.failed, 0, "Vacuous must not increment failed");
    assert_eq!(
        counters.errors, 0,
        "Vacuous is tracked separately from errors"
    );
    assert_eq!(counters.demoted, 0, "Vacuous is not a demotion");
}

#[test]
fn report_obligation_demoted_unknown_increments_both_errors_and_demoted() {
    let mut counters = VerificationCounters {
        errors: 3,
        demoted: 1,
        ..VerificationCounters::default()
    };
    let outcome = apply_ok_outcome_branch(
        &mut counters,
        VerificationOutcome::without_provenance(VerificationResult::Unknown(
            UnknownReason::Demoted("sort_fallback(2)".into()),
        )),
    );
    assert_eq!(outcome, ObligationOutcome::ErrorRecorded);
    assert_eq!(counters.failed, 0, "Demoted must not touch failed");
    assert_eq!(
        counters.errors, 4,
        "Demoted must increment errors from 3 to 4"
    );
    assert_eq!(
        counters.demoted, 2,
        "Demoted must increment demoted from 1 to 2 (#2106)"
    );
}

/// Tests the `Err(EncodingError)` path of `report_obligation_result` via the
/// extracted `record_encoding_error` helper (#1996).
///
/// `report_obligation_result` delegates its `Err` branch to `record_encoding_error`,
/// which is TyCtxt-free and directly callable. The only TyCtxt-dependent logic
/// in the `Err` path is cosmetic span enrichment — the counter accounting is
/// fully exercised through the helper.
#[test]
fn report_obligation_encoding_error_increments_errors_and_records_breakdown() {
    use trust_wp_ay::EncodingError;

    let mut counters = VerificationCounters {
        errors: 2,
        ..VerificationCounters::default()
    };

    let err = EncodingError::Unsupported {
        message: "test construct".into(),
        span: None,
        contract_text: None,
    };
    let outcome = record_encoding_error(&err, &mut counters, "test::fn", "test.rs:1");

    assert_eq!(outcome, ObligationOutcome::ErrorRecorded);
    assert_eq!(
        counters.errors, 3,
        "Err branch must increment errors from 2 to 3"
    );
    assert_eq!(
        counters.encoding_errors.unsupported, 1,
        "Err branch must record Unsupported in encoding_errors breakdown"
    );
    assert_eq!(counters.failed, 0, "Err branch must not touch failed");
    assert_eq!(counters.demoted, 0, "Err branch must not touch demoted");
}
/// SolverError variant dispatches to the solver breakdown field.
#[test]
fn report_obligation_solver_error_records_solver_breakdown() {
    use trust_wp_ay::EncodingError;

    let mut counters = VerificationCounters::default();

    let err = EncodingError::SolverError {
        message: "ay internal error".into(),
        span: None,
    };
    let outcome = record_encoding_error(&err, &mut counters, "test::fn", "test.rs:1");

    assert_eq!(outcome, ObligationOutcome::ErrorRecorded);
    assert_eq!(counters.errors, 1);
    assert_eq!(counters.encoding_errors.solver, 1);
    assert_eq!(counters.encoding_errors.unsupported, 0);
    assert_eq!(counters.encoding_errors.sort_inference, 0);
}

/// Verify accumulation: multiple obligation results applied sequentially
/// produce correct counter totals. This catches off-by-one or reset bugs.
/// Covers all 5 Ok-path match arms plus the Err path via `record_encoding_error`.
#[test]
fn report_obligation_sequential_accumulation() {
    use trust_wp_ay::EncodingError;

    let mut counters = VerificationCounters::default();

    // 1st: Verified without provenance -- evidence gap, no failed/error/demoted
    let _ = apply_ok_outcome_branch(
        &mut counters,
        VerificationOutcome::without_provenance(VerificationResult::Verified(None)),
    );
    assert_eq!(
        (counters.failed, counters.errors, counters.demoted),
        (0, 0, 0)
    );
    assert_eq!(counters.evidence_gaps, 1);

    // 2nd: Failed -- failed += 1
    let cex = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let _ = apply_ok_outcome_branch(
        &mut counters,
        VerificationOutcome::without_provenance(VerificationResult::Failed(cex)),
    );
    assert_eq!(
        (counters.failed, counters.errors, counters.demoted),
        (1, 0, 0)
    );

    // 3rd: Unknown(Timeout) -- errors += 1
    let _ = apply_ok_outcome_branch(
        &mut counters,
        VerificationOutcome::without_provenance(VerificationResult::Unknown(
            UnknownReason::Timeout,
        )),
    );
    assert_eq!(
        (counters.failed, counters.errors, counters.demoted),
        (1, 1, 0)
    );

    // 4th: Unknown(Demoted) -- errors += 1, demoted += 1
    let _ = apply_ok_outcome_branch(
        &mut counters,
        VerificationOutcome::without_provenance(VerificationResult::Unknown(
            UnknownReason::Demoted("test".into()),
        )),
    );
    assert_eq!(
        (counters.failed, counters.errors, counters.demoted),
        (1, 2, 1)
    );

    // 5th: Assumed -- no change
    let _ = apply_ok_outcome_branch(
        &mut counters,
        VerificationOutcome::without_provenance(VerificationResult::Assumed("axiom".into())),
    );
    assert_eq!(
        (counters.failed, counters.errors, counters.demoted),
        (1, 2, 1),
        "Assumed must not change any counter"
    );

    // 6th: Err(EncodingError) -- errors += 1, encoding_errors.unsupported += 1
    let err = EncodingError::Unsupported {
        message: "test".into(),
        span: None,
        contract_text: None,
    };
    let outcome = record_encoding_error(&err, &mut counters, "test::fn", "test.rs:1");
    assert_eq!(outcome, ObligationOutcome::ErrorRecorded);
    assert_eq!(
        (counters.failed, counters.errors, counters.demoted),
        (1, 3, 1),
        "Err(EncodingError) must only increment errors"
    );
    assert_eq!(
        counters.evidence_gaps, 1,
        "Verified without provenance gap should remain tracked"
    );
    assert_eq!(
        counters.encoding_errors.unsupported, 1,
        "Err path must record in encoding_errors breakdown"
    );
}

// ── report_obligation_result Ok-path does NOT touch encoding_errors (#1996) ──
//
// The `Ok(vr)` path of `report_obligation_result` only mutates `failed`,
// `errors`, and `demoted` via the deltas from `classify_obligation_result`.
// It must NEVER touch `encoding_errors`, which is exclusively for the `Err`
// branch. These tests verify cross-field isolation.

#[test]
fn test_report_obligation_result_verified_does_not_touch_encoding_errors() {
    let mut counters = VerificationCounters::default();
    let _ = apply_ok_outcome_branch(
        &mut counters,
        VerificationOutcome::without_provenance(VerificationResult::Verified(None)),
    );
    assert!(
        counters.encoding_errors.is_empty(),
        "Ok(Verified without provenance) must not touch encoding_errors breakdown"
    );
}

#[test]
fn test_report_obligation_result_failed_does_not_touch_encoding_errors() {
    let mut counters = VerificationCounters::default();
    let cex = Counterexample {
        values: vec![],
        violated_postcondition: None,
    };
    let _ = apply_ok_outcome_branch(
        &mut counters,
        VerificationOutcome::without_provenance(VerificationResult::Failed(cex)),
    );
    assert!(
        counters.encoding_errors.is_empty(),
        "Ok(Failed) must not touch encoding_errors breakdown"
    );
}

#[test]
fn test_report_obligation_result_unknown_does_not_touch_encoding_errors() {
    let mut counters = VerificationCounters::default();
    let _ = apply_ok_outcome_branch(
        &mut counters,
        VerificationOutcome::without_provenance(VerificationResult::Unknown(
            UnknownReason::Timeout,
        )),
    );
    assert!(
        counters.encoding_errors.is_empty(),
        "Ok(Unknown) must not touch encoding_errors breakdown"
    );
}

// ── report_obligation_result Err-path isolation (#1996) ──────────────────────
//
// The `Err(EncodingError)` branch only increments `errors` and records in
// `encoding_errors`. It must NOT touch `failed` or `demoted`.

#[test]
fn test_report_obligation_result_err_sort_inference_records_breakdown() {
    use trust_wp_ay::EncodingError;

    let mut counters = VerificationCounters::default();
    let err = EncodingError::SortInference {
        context: "logic_fn param 0".into(),
        detail: "could not resolve sort".into(),
        span: None,
    };
    let outcome = record_encoding_error(&err, &mut counters, "test::fn", "test.rs:1");

    assert_eq!(outcome, ObligationOutcome::ErrorRecorded);
    assert_eq!(
        counters.errors, 1,
        "Err(SortInference) must increment errors"
    );
    assert_eq!(
        counters.encoding_errors.sort_inference, 1,
        "Err(SortInference) must record sort_inference in breakdown"
    );
    assert_eq!(
        counters.encoding_errors.unsupported, 0,
        "Err(SortInference) must not touch unsupported"
    );
    assert_eq!(
        counters.encoding_errors.solver, 0,
        "Err(SortInference) must not touch solver"
    );
    assert_eq!(counters.failed, 0, "Err branch must not touch failed");
    assert_eq!(counters.demoted, 0, "Err branch must not touch demoted");
}

#[test]
fn test_report_obligation_result_err_sort_conflict_increments_errors_only() {
    use trust_wp_ay::EncodingError;

    let mut counters = VerificationCounters::default();
    let err = EncodingError::SortConflict {
        context: "variable 'x'".into(),
        declared_sort: "Int".into(),
        requested_sort: "Bool".into(),
        span: None,
    };
    // SortConflict hits the wildcard arm of EncodingErrorBreakdown::record,
    // so it increments errors but does NOT appear in any breakdown field.
    let outcome = record_encoding_error(&err, &mut counters, "test::fn", "test.rs:1");

    assert_eq!(outcome, ObligationOutcome::ErrorRecorded);
    assert_eq!(
        counters.errors, 1,
        "Err(SortConflict) must increment errors"
    );
    assert!(
        counters.encoding_errors.is_empty(),
        "SortConflict falls through wildcard — no breakdown field records it"
    );
    assert_eq!(counters.failed, 0, "Err branch must not touch failed");
    assert_eq!(counters.demoted, 0, "Err branch must not touch demoted");
}
