// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod prepare_clauses;

use std::sync::Arc;

use trust_wp_ay::{verify_function_with_modes, VerificationRequest, VerificationResult};
use trust_wp_core::formula::{BinOp, PureExpr};

use super::{
    build_post_refinement_obligations,
    report::{aggregate_refinement_counts, report_refinement_result, RefinementOutcome},
};
use crate::callbacks::encoding_error_breakdown::EncodingErrorBreakdown;

#[test]
fn test_both_verified() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Verified,
        RefinementOutcome::Verified,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, 0);
    assert_eq!(counts.assumed_delta, 0);
    assert_eq!(counts.failed_delta, 0);
    assert_eq!(counts.error_delta, 0);
}

#[test]
fn test_pre_failed_post_verified() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Failed,
        RefinementOutcome::Verified,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, -1);
    assert_eq!(counts.assumed_delta, 0);
    assert_eq!(counts.failed_delta, 1);
    assert_eq!(counts.error_delta, 0);
}

#[test]
fn test_pre_verified_post_error() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Verified,
        RefinementOutcome::Error,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, -1);
    assert_eq!(counts.assumed_delta, 0);
    assert_eq!(counts.failed_delta, 0);
    assert_eq!(counts.error_delta, 1);
}

#[test]
fn test_both_failed() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Failed,
        RefinementOutcome::Failed,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, -1);
    assert_eq!(counts.assumed_delta, 0);
    assert_eq!(counts.failed_delta, 2);
    assert_eq!(counts.error_delta, 0);
}

#[test]
fn test_both_error() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Error,
        RefinementOutcome::Error,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, -1);
    assert_eq!(counts.assumed_delta, 0);
    assert_eq!(counts.failed_delta, 0);
    assert_eq!(counts.error_delta, 2);
}

#[test]
fn test_pre_verified_post_failed() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Verified,
        RefinementOutcome::Failed,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, -1);
    assert_eq!(counts.assumed_delta, 0);
    assert_eq!(counts.failed_delta, 1);
    assert_eq!(counts.error_delta, 0);
}

#[test]
fn test_pre_error_post_verified() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Error,
        RefinementOutcome::Verified,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, -1);
    assert_eq!(counts.assumed_delta, 0);
    assert_eq!(counts.failed_delta, 0);
    assert_eq!(counts.error_delta, 1);
}

/// Regression test for #2011: mixed outcomes must report both deltas.
/// Previously, Failed took priority and Error was silently dropped.
#[test]
fn test_mixed_failed_and_error_reports_both() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Failed,
        RefinementOutcome::Error,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, -1);
    assert_eq!(counts.assumed_delta, 0);
    assert_eq!(counts.failed_delta, 1);
    assert_eq!(counts.error_delta, 1);
}

/// Regression test for #2011: reverse direction of mixed outcomes.
#[test]
fn test_mixed_error_and_failed_reports_both() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Error,
        RefinementOutcome::Failed,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, -1);
    assert_eq!(counts.assumed_delta, 0);
    assert_eq!(counts.failed_delta, 1);
    assert_eq!(counts.error_delta, 1);
}

/// #2121: Both assumed — no verified/failed/error, just assumed.
#[test]
fn test_both_assumed() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Assumed,
        RefinementOutcome::Assumed,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, 0);
    assert_eq!(counts.assumed_delta, 2);
    assert_eq!(counts.failed_delta, 0);
    assert_eq!(counts.error_delta, 0);
}

/// #2121: Pre verified, post assumed — overall assumed, not verified.
#[test]
fn test_pre_verified_post_assumed() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Verified,
        RefinementOutcome::Assumed,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, 0);
    assert_eq!(counts.assumed_delta, 1);
    assert_eq!(counts.failed_delta, 0);
    assert_eq!(counts.error_delta, 0);
}

/// #2121: Pre assumed, post verified — overall assumed, not verified.
#[test]
fn test_pre_assumed_post_verified() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Assumed,
        RefinementOutcome::Verified,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, 0);
    assert_eq!(counts.assumed_delta, 1);
    assert_eq!(counts.failed_delta, 0);
    assert_eq!(counts.error_delta, 0);
}

/// #2121: Assumed + Failed — failure takes priority, assumed still tracked.
#[test]
fn test_pre_assumed_post_failed() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Assumed,
        RefinementOutcome::Failed,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, -1);
    assert_eq!(counts.assumed_delta, 1);
    assert_eq!(counts.failed_delta, 1);
    assert_eq!(counts.error_delta, 0);
}

/// #2121: Assumed + Error — error takes priority, assumed still tracked.
#[test]
fn test_pre_assumed_post_error() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Assumed,
        RefinementOutcome::Error,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, -1);
    assert_eq!(counts.assumed_delta, 1);
    assert_eq!(counts.failed_delta, 0);
    assert_eq!(counts.error_delta, 1);
}

#[test]
fn test_refinement_evidence_gap_decrements_verified_and_records_gap() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Verified,
        RefinementOutcome::EvidenceGap,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(
        counts.verified_delta, -1,
        "evidence gap should remove the enclosing clean verified count"
    );
    assert_eq!(counts.failed_delta, 0);
    assert_eq!(counts.error_delta, 0);
    assert_eq!(counts.evidence_gap_delta, 1);
    assert_eq!(counts.warning_delta, 1);
}

/// #2121 regression: `report_refinement_result` must map `Assumed` to
/// `RefinementOutcome::Assumed`, NOT `Verified`. The original bug was
/// a combined match arm `Verified | Assumed(_) => Verified` that silently
/// accepted assumed results. The aggregation-level tests above construct
/// `RefinementOutcome::Assumed` directly and don't exercise this mapping.
#[test]
fn test_report_refinement_result_assumed_maps_to_assumed() {
    let outcome = report_refinement_result(
        Ok(VerificationResult::Assumed("axiom only".to_string())),
        "test::impl_fn",
        "test::Trait::fn",
        "pre-condition refinement",
        "test.rs:1",
    );
    assert_eq!(
        outcome,
        RefinementOutcome::Assumed,
        "Assumed solver result must NOT be mapped to Verified"
    );
}

/// Verified-shaped results without provenance are not accepted as clean
/// refinement proofs.
#[test]
fn test_report_refinement_result_verified_without_provenance_maps_to_evidence_gap() {
    let outcome = report_refinement_result(
        Ok(VerificationResult::Verified(None)),
        "test::impl_fn",
        "test::Trait::fn",
        "post-condition refinement",
        "test.rs:2",
    );
    assert_eq!(
        outcome,
        RefinementOutcome::EvidenceGap,
        "Verified without accepted evidence must not map to Verified"
    );
}

#[test]
fn test_post_refinement_identical_postcondition_shortcuts_to_true() {
    let post = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("self".to_string(), None)),
    );

    let obligations =
        build_post_refinement_obligations(std::slice::from_ref(&post), std::slice::from_ref(&post));

    assert_eq!(obligations, vec![PureExpr::Bool(true)]);
}

#[test]
fn test_post_refinement_matching_conjunct_shortcuts_to_true() {
    let matching = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("self".to_string(), None)),
    );
    let extra = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );

    let obligations = build_post_refinement_obligations(&[matching.clone(), extra], &[matching]);

    assert_eq!(obligations, vec![PureExpr::Bool(true)]);
}

/// #2106: Demoted Unknown results must produce Demoted outcome, not Error.
#[test]
fn test_report_refinement_result_demoted_maps_to_demoted() {
    let outcome = report_refinement_result(
        Ok(VerificationResult::Unknown(
            trust_wp_ay::UnknownReason::Demoted(
                "encoding approximations may affect soundness: sort_fallback_to_int(1)".to_string(),
            ),
        )),
        "test::impl_fn",
        "test::Trait::fn",
        "post-condition refinement",
        "test.rs:3",
    );
    assert_eq!(
        outcome,
        RefinementOutcome::Demoted,
        "Demoted Unknown must map to Demoted, not Error (#2106)"
    );
}

#[test]
fn test_report_refinement_result_vacuous_solver_message_maps_to_error() {
    let outcome = report_refinement_result(
        Ok(VerificationResult::Unknown(
            trust_wp_ay::UnknownReason::SolverMessage(
                "vacuous proof: base assertions are UNSAT without the negated postcondition"
                    .to_string(),
            ),
        )),
        "test::impl_fn",
        "test::Trait::fn",
        "pre-condition refinement",
        "test.rs:4",
    );
    assert_eq!(
        outcome,
        RefinementOutcome::Error,
        "Vacuous trait refinement must not map to Verified"
    );

    let counts = aggregate_refinement_counts(
        RefinementOutcome::Verified,
        outcome,
        false,
        "test::impl_fn",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, -1);
    assert_eq!(counts.error_delta, 1);
    assert_eq!(counts.failed_delta, 0);
    assert_eq!(counts.demoted_delta, 0);
    assert_eq!(counts.assumed_delta, 0);
}

/// #2106: Demoted counts as error_delta AND demoted_delta in aggregation.
#[test]
fn test_demoted_counts_as_error_and_demoted() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Verified,
        RefinementOutcome::Demoted,
        false,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(
        counts.verified_delta, -1,
        "Demoted should decrement verified"
    );
    assert_eq!(counts.error_delta, 1, "Demoted counts as error");
    assert_eq!(
        counts.demoted_delta, 1,
        "Demoted tracked separately (#2106)"
    );
    assert_eq!(counts.failed_delta, 0);
}

/// #2363 regression: precondition refinement with identical user requires
/// and matching View-wrapped integer-range constraints must verify.
///
/// When both trait and impl declare `n >= 0` and both sides carry the same
/// `View(n) >= -2^31, View(n) <= 2^31-1` range constraints, the precondition
/// direction `(trait_requires + ranges) => (impl_requires + ranges)` should
/// be trivially provable.
#[test]
fn test_precondition_refinement_identical_with_ranges_verifies() {
    // User-written: n >= 0
    let n_ge_0 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );

    // View-wrapped range constraint: View(n) >= -2^31
    let view_n = PureExpr::View(Arc::new(PureExpr::Var("n".to_string(), None)));
    let view_ge_min = PureExpr::BinOp(
        Arc::new(view_n.clone()),
        BinOp::Ge,
        Arc::new(PureExpr::Int(-2_147_483_648)),
    );
    // View-wrapped range constraint: View(n) <= 2^31-1
    let view_le_max = PureExpr::BinOp(
        Arc::new(view_n),
        BinOp::Le,
        Arc::new(PureExpr::Int(2_147_483_647)),
    );

    // Both sides have the same clauses: user requires + int ranges.
    let trait_requires = vec![n_ge_0.clone(), view_ge_min.clone(), view_le_max.clone()];
    let impl_requires = vec![n_ge_0, view_ge_min, view_le_max];

    let result = verify_function_with_modes(
        VerificationRequest::new(&trait_requires, &impl_requires)
            .track(Some(trust_wp_core::TrackLevel::Reg)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "precondition refinement with identical clauses must verify, got {result:?}"
    );
}

/// #2363 regression: precondition refinement WITHOUT range parity fails.
///
/// Demonstrates the original bug: trait side has only `n >= 0` while impl
/// side has `n >= 0` plus View-wrapped range constraints. The solver cannot
/// prove `View(n) <= 2^31-1` from `n >= 0` alone.
#[test]
fn test_precondition_refinement_missing_trait_ranges_fails() {
    let n_ge_0 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );

    let view_n = PureExpr::View(Arc::new(PureExpr::Var("n".to_string(), None)));
    let view_ge_min = PureExpr::BinOp(
        Arc::new(view_n.clone()),
        BinOp::Ge,
        Arc::new(PureExpr::Int(-2_147_483_648)),
    );
    let view_le_max = PureExpr::BinOp(
        Arc::new(view_n),
        BinOp::Le,
        Arc::new(PureExpr::Int(2_147_483_647)),
    );

    // Trait side: only user requires (missing int ranges) — the pre-#2363 bug.
    let trait_requires = vec![n_ge_0.clone()];
    // Impl side: user requires + int ranges.
    let impl_requires = vec![n_ge_0, view_ge_min, view_le_max];

    let result = verify_function_with_modes(
        VerificationRequest::new(&trait_requires, &impl_requires)
            .track(Some(trust_wp_core::TrackLevel::Reg)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "precondition refinement without range parity should produce a concrete refinement failure \
         (not a demotion or encoding error), got {result:?}"
    );
}

/// #2670: Logic function impl with stronger precondition must fail refinement.
///
/// When a trait declares `#[requires(x@ >= 10)]` and an impl narrows to
/// `#[requires(y@ >= 15)]`, the precondition direction check
/// `(trait_requires) => (impl_requires)` must fail because `x@ >= 10`
/// does NOT imply `x@ >= 15` (counterexample: x = 12).
#[test]
fn test_logic_fn_precondition_widening_fails_refinement() {
    let view_x = PureExpr::View(Arc::new(PureExpr::Var("x".to_string(), None)));

    // Trait: x@ >= 10
    let trait_requires = vec![PureExpr::BinOp(
        Arc::new(view_x.clone()),
        BinOp::Ge,
        Arc::new(PureExpr::Int(10)),
    )];

    // Impl: x@ >= 15 (stronger — violates contravariance)
    let impl_requires = vec![PureExpr::BinOp(
        Arc::new(view_x),
        BinOp::Ge,
        Arc::new(PureExpr::Int(15)),
    )];

    let result = verify_function_with_modes(
        VerificationRequest::new(&trait_requires, &impl_requires)
            .track(Some(trust_wp_core::TrackLevel::Reg)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "stronger impl precondition must fail refinement (counterexample: x=12), got {result:?}"
    );
}
