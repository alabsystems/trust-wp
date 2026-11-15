// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for obligation slicing, extracted from the inline module.

use std::{sync::Arc, time::Duration};

use ntest::timeout;
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use super::{
    aggregate_slice_outcomes, aggregate_slice_results, proof_assert_obligation_slice_derivations,
    split_ensures, Counterexample, SliceOutcome, SliceResult, UnknownReason, VerificationOutcome,
    VerificationResult,
};
use crate::{
    tests::helpers::{add, eq, exists_with_sort, forall, gt, int, method_call, var},
    verify::{
        ProofCertificateSummary, SolveEvidenceSnapshot, SolveResourceSnapshot,
        SolveVerificationLevelSnapshot, SolveVerificationSnapshot, VerificationProvenance,
    },
    ProofAssertSliceDerivation,
};

fn strict_summary(resolution_count: u32) -> ProofCertificateSummary {
    ProofCertificateSummary {
        strict_verified: true,
        restricted_rule_subset: true,
        trust_count: 0,
        trust_fallback_count: 0,
        hole_count: 0,
        theory_lemma_count: 0,
        resolution_count,
        farkas_certificate_count: 0,
        lrat_present: true,
        alethe_text: Some(format!("; checked slice {resolution_count}")),
    }
}

#[test]
#[timeout(30000)]
fn split_ensures_empty() {
    let slices = split_ensures(&[]);
    assert!(slices.is_empty());
}

#[test]
#[timeout(30000)]
fn split_ensures_preserves_indices() {
    let ensures = vec![var("a"), var("b"), var("c")];
    let slices = split_ensures(&ensures);
    assert_eq!(slices.len(), 3);
    assert_eq!(slices[0].index, 0);
    assert_eq!(slices[1].index, 1);
    assert_eq!(slices[2].index, 2);
    assert_eq!(slices[0].ensure.as_ref(), &ensures[0]);
    assert_eq!(slices[2].ensure.as_ref(), &ensures[2]);
}

#[test]
#[timeout(30000)]
fn split_ensures_single() {
    let ensures = vec![int(42)];
    let slices = split_ensures(&ensures);
    assert_eq!(slices.len(), 1);
    assert_eq!(slices[0].index, 0);
}

#[test]
#[timeout(30000)]
fn split_ensures_flattens_top_level_conjunctions() {
    let ensures = vec![PureExpr::BinOp(
        Arc::new(var("a")),
        BinOp::And,
        Arc::new(var("b")),
    )];
    let slices = split_ensures(&ensures);
    assert_eq!(slices.len(), 2);
    assert_eq!(slices[0].index, 0);
    assert_eq!(slices[1].index, 0);
    assert_eq!(slices[0].ensure.as_ref(), &var("a"));
    assert_eq!(slices[1].ensure.as_ref(), &var("b"));
}

#[test]
#[timeout(30000)]
fn split_ensures_flattens_guarded_conjunctions() {
    let nested_and = PureExpr::BinOp(Arc::new(var("b")), BinOp::And, Arc::new(var("c")));
    let ensures = vec![PureExpr::BinOp(
        Arc::new(var("a")),
        BinOp::Implies,
        Arc::new(nested_and.clone()),
    )];
    let slices = split_ensures(&ensures);
    assert_eq!(slices.len(), 2);
    assert_eq!(slices[0].index, 0);
    assert_eq!(
        slices[0].ensure.as_ref(),
        &PureExpr::BinOp(Arc::new(var("a")), BinOp::Implies, Arc::new(var("b")))
    );
    assert_eq!(
        slices[1].ensure.as_ref(),
        &PureExpr::BinOp(Arc::new(var("a")), BinOp::Implies, Arc::new(var("c")))
    );
}

#[test]
#[timeout(30000)]
fn split_ensures_flattens_guarded_conjunctions_under_let() {
    let body = PureExpr::BinOp(
        Arc::new(var("guard")),
        BinOp::Implies,
        Arc::new(PureExpr::BinOp(
            Arc::new(var("a")),
            BinOp::And,
            Arc::new(var("b")),
        )),
    );
    let ensures = vec![PureExpr::Let {
        var: "mid".to_string(),
        value: Arc::new(int(0)),
        body: Arc::new(body),
    }];
    let slices = split_ensures(&ensures);
    assert_eq!(slices.len(), 2);
    assert!(matches!(
        slices[0].ensure.as_ref(),
        PureExpr::Let { body, .. }
            if matches!(
                body.as_ref(),
                PureExpr::BinOp(_, BinOp::Implies, consequent)
                    if matches!(consequent.as_ref(), PureExpr::Var(name, _) if name == "a")
            )
    ));
    assert!(matches!(
        slices[1].ensure.as_ref(),
        PureExpr::Let { body, .. }
            if matches!(
                body.as_ref(),
                PureExpr::BinOp(_, BinOp::Implies, consequent)
                    if matches!(consequent.as_ref(), PureExpr::Var(name, _) if name == "b")
            )
    ));
}

#[test]
#[timeout(30000)]
fn split_ensures_keeps_existential_conjunction_intact() {
    let existential = exists_with_sort("y", ExprSort::Int, gt(var("y"), int(0)));
    let ensures = vec![PureExpr::BinOp(
        Arc::new(var("a")),
        BinOp::And,
        Arc::new(existential),
    )];
    let slices = split_ensures(&ensures);
    assert_eq!(slices.len(), 1);
    assert_eq!(slices[0].index, 0);
    assert_eq!(slices[0].ensure.as_ref(), &ensures[0]);
}

#[test]
#[timeout(30000)]
fn proof_assert_derivations_are_exact_and_prepared_only() {
    let premise = var("premise");
    let ensures = vec![PureExpr::Bool(true), premise.clone(), var("other")];
    let derivations = proof_assert_obligation_slice_derivations(&ensures, &[premise]);

    assert_eq!(
        derivations,
        vec![
            ProofAssertSliceDerivation::SyntacticTruth,
            ProofAssertSliceDerivation::ExactPreparedPremise,
            ProofAssertSliceDerivation::NativeEncoded,
        ]
    );
}

#[test]
#[timeout(30000)]
fn proof_assert_derivation_does_not_infer_split_conjuncts() {
    let conjunction = PureExpr::BinOp(Arc::new(var("left")), BinOp::And, Arc::new(var("right")));
    let derivations = proof_assert_obligation_slice_derivations(
        std::slice::from_ref(&conjunction),
        std::slice::from_ref(&conjunction),
    );

    assert_eq!(
        derivations,
        vec![
            ProofAssertSliceDerivation::NativeEncoded,
            ProofAssertSliceDerivation::NativeEncoded,
        ]
    );
}

#[test]
#[timeout(30000)]
fn aggregate_all_verified() {
    let results = vec![
        SliceResult {
            index: 0,
            result: VerificationResult::Verified(Some(strict_summary(3))),
        },
        SliceResult {
            index: 1,
            result: VerificationResult::Verified(Some(strict_summary(5))),
        },
    ];
    let VerificationResult::Verified(Some(summary)) = aggregate_slice_results(results) else {
        panic!("strict slice summaries must survive aggregation");
    };
    assert!(summary.is_fully_verified());
    assert_eq!(summary.resolution_count, 8);
    assert!(summary.alethe_text.is_none());
}

#[test]
#[timeout(30000)]
fn aggregate_empty_is_verified() {
    assert!(matches!(
        aggregate_slice_results(vec![]),
        VerificationResult::Verified(None)
    ));
}

#[test]
#[timeout(30000)]
fn aggregate_missing_summary_remains_visible() {
    let results = vec![
        SliceResult {
            index: 0,
            result: VerificationResult::Verified(Some(strict_summary(3))),
        },
        SliceResult {
            index: 1,
            result: VerificationResult::Verified(None),
        },
    ];
    assert!(matches!(
        aggregate_slice_results(results),
        VerificationResult::Verified(None)
    ));
}

#[test]
#[timeout(30000)]
fn aggregate_failed_takes_precedence_over_unknown() {
    let results = vec![
        SliceResult {
            index: 0,
            result: VerificationResult::Unknown(UnknownReason::Quantifiers),
        },
        SliceResult {
            index: 1,
            result: VerificationResult::Failed(Counterexample::empty()),
        },
        SliceResult {
            index: 2,
            result: VerificationResult::Verified(None),
        },
    ];
    assert!(matches!(
        aggregate_slice_results(results),
        VerificationResult::Failed(_)
    ));
}

#[test]
#[timeout(30000)]
fn aggregate_unknown_takes_precedence_over_verified() {
    let results = vec![
        SliceResult {
            index: 0,
            result: VerificationResult::Verified(None),
        },
        SliceResult {
            index: 1,
            result: VerificationResult::Unknown(UnknownReason::Incomplete),
        },
    ];
    match aggregate_slice_results(results) {
        VerificationResult::Unknown(UnknownReason::Incomplete) => {}
        other => panic!("expected Unknown, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn aggregate_declined_slice_with_certified_sibling_stays_unknown() {
    // Aggregation-audit pin (#129 leg B): every slice is a genuine conjunct
    // of the postcondition (split_ensures flattens top-level conjunctions),
    // so a probe-declined slice — Unknown(QuantifierUnhandled) after a real
    // full-solve attempt — must sink the aggregate to Unknown even when a
    // sibling slice carries a clean strict certificate. The certificate
    // proves ITS conjunct only; it cannot substitute for the declined one.
    //
    // Equally pinned: a decline is NOT conflated with falsity — the
    // aggregate is Unknown (preserving the decline reason), never Failed.
    let results = vec![
        SliceResult {
            index: 0,
            result: VerificationResult::Verified(Some(strict_summary(3))),
        },
        SliceResult {
            index: 1,
            result: VerificationResult::Unknown(UnknownReason::QuantifierUnhandled),
        },
    ];
    match aggregate_slice_results(results) {
        VerificationResult::Unknown(UnknownReason::QuantifierUnhandled) => {}
        other => panic!(
            "a declined conjunct must aggregate to Unknown(QuantifierUnhandled), \
             not be masked by a certified sibling or promoted to Failed; got {other:?}"
        ),
    }
}

#[test]
#[timeout(30000)]
fn aggregate_first_failure_wins() {
    let results = vec![
        SliceResult {
            index: 0,
            result: VerificationResult::Failed(Counterexample::empty()),
        },
        SliceResult {
            index: 1,
            result: VerificationResult::Failed(Counterexample::empty()),
        },
    ];
    // Both fail, but the first one's counterexample is returned.
    assert!(matches!(
        aggregate_slice_results(results),
        VerificationResult::Failed(_)
    ));
}

// --- Assumed propagation tests (#1889) ---

#[test]
#[timeout(30000)]
fn aggregate_assumed_not_promoted_to_verified() {
    let results = vec![
        SliceResult {
            index: 0,
            result: VerificationResult::Verified(None),
        },
        SliceResult {
            index: 1,
            result: VerificationResult::Assumed("axiom-only function".to_string()),
        },
    ];
    match aggregate_slice_results(results) {
        VerificationResult::Assumed(reason) => {
            assert_eq!(reason, "axiom-only function");
        }
        other => {
            panic!("expected Assumed, got {other:?} — Assumed must not be promoted to Verified")
        }
    }
}

#[test]
#[timeout(30000)]
fn aggregate_failed_takes_precedence_over_assumed() {
    let results = vec![
        SliceResult {
            index: 0,
            result: VerificationResult::Assumed("axiom".to_string()),
        },
        SliceResult {
            index: 1,
            result: VerificationResult::Failed(Counterexample::empty()),
        },
    ];
    assert!(matches!(
        aggregate_slice_results(results),
        VerificationResult::Failed(_)
    ));
}

fn outcome_with_assertions(
    result: VerificationResult,
    assertion_count: u64,
) -> VerificationOutcome {
    VerificationOutcome::new(
        result,
        Some(
            VerificationProvenance::with_solve_time(Duration::from_millis(assertion_count))
                .with_assertion_count(assertion_count),
        ),
    )
}

fn outcome_with_accepted_unsat_assertions(
    result: VerificationResult,
    assertion_count: u64,
) -> VerificationOutcome {
    VerificationOutcome::new(
        result,
        Some(
            VerificationProvenance::with_solve_time(Duration::from_millis(assertion_count))
                .with_assertion_count(assertion_count)
                .with_solve_evidence(Some(accepted_unsat_evidence())),
        ),
    )
}

fn accepted_unsat_evidence() -> SolveEvidenceSnapshot {
    SolveEvidenceSnapshot {
        result: "UNSAT".to_string(),
        model_validated: false,
        accepted_for_consumer: true,
        consumer_rejection: None,
        verification: SolveVerificationSnapshot {
            unsat_proof_available: true,
            ..Default::default()
        },
        verification_level: SolveVerificationLevelSnapshot::FullyVerified,
        resource_usage: SolveResourceSnapshot::default(),
    }
}

#[test]
#[timeout(30000)]
fn aggregate_slice_outcomes_preserves_failed_provenance() {
    let outcomes = vec![
        SliceOutcome {
            index: 0,
            outcome: outcome_with_assertions(
                VerificationResult::Unknown(UnknownReason::Incomplete),
                7,
            ),
        },
        SliceOutcome {
            index: 1,
            outcome: outcome_with_assertions(
                VerificationResult::Failed(Counterexample::empty()),
                11,
            ),
        },
    ];
    let aggregate = aggregate_slice_outcomes(outcomes);
    assert!(matches!(aggregate.result, VerificationResult::Failed(_)));
    assert_eq!(
        aggregate.provenance.as_ref().map(|p| p.assertion_count),
        Some(11)
    );
}

#[test]
#[timeout(30000)]
fn aggregate_slice_outcomes_preserves_unknown_provenance() {
    let outcomes = vec![
        SliceOutcome {
            index: 0,
            outcome: VerificationOutcome::without_provenance(VerificationResult::Verified(None)),
        },
        SliceOutcome {
            index: 1,
            outcome: outcome_with_assertions(
                VerificationResult::Unknown(UnknownReason::Quantifiers),
                13,
            ),
        },
    ];
    let aggregate = aggregate_slice_outcomes(outcomes);
    assert!(matches!(
        aggregate.result,
        VerificationResult::Unknown(UnknownReason::Quantifiers)
    ));
    assert_eq!(
        aggregate.provenance.as_ref().map(|p| p.assertion_count),
        Some(13)
    );
}

#[test]
#[timeout(30000)]
fn aggregate_slice_outcomes_all_verified_with_evidence_keeps_solver_provenance() {
    let outcomes = vec![
        SliceOutcome {
            index: 0,
            outcome: outcome_with_accepted_unsat_assertions(
                VerificationResult::Verified(Some(strict_summary(3))),
                5,
            ),
        },
        SliceOutcome {
            index: 1,
            outcome: outcome_with_accepted_unsat_assertions(
                VerificationResult::Verified(Some(strict_summary(5))),
                17,
            ),
        },
    ];
    let aggregate = aggregate_slice_outcomes(outcomes);
    let VerificationResult::Verified(Some(summary)) = aggregate.result else {
        panic!("strict slice summaries must survive outcome aggregation");
    };
    assert!(summary.is_fully_verified());
    assert_eq!(summary.resolution_count, 8);
    assert_eq!(
        aggregate.provenance.as_ref().map(|p| p.assertion_count),
        Some(5)
    );
    assert!(aggregate
        .provenance
        .as_ref()
        .and_then(|p| p.solve_evidence.as_ref())
        .is_some_and(|evidence| evidence.accepted_for_consumer));
}

#[test]
#[timeout(30000)]
fn aggregate_slice_outcomes_verified_gap_beats_accepted_unsat_provenance() {
    let outcomes = vec![
        SliceOutcome {
            index: 0,
            outcome: VerificationOutcome::without_provenance(VerificationResult::Verified(None)),
        },
        SliceOutcome {
            index: 1,
            outcome: outcome_with_accepted_unsat_assertions(
                VerificationResult::Verified(Some(strict_summary(5))),
                17,
            ),
        },
    ];
    let aggregate = aggregate_slice_outcomes(outcomes);
    assert!(matches!(
        aggregate.result,
        VerificationResult::Verified(None)
    ));
    assert!(
        aggregate.provenance.is_none(),
        "verified slice without provenance must not be hidden by accepted UNSAT evidence"
    );
}

#[test]
#[timeout(30000)]
fn aggregate_slice_outcomes_empty_verified_without_provenance() {
    let aggregate = aggregate_slice_outcomes(vec![]);
    assert!(matches!(
        aggregate.result,
        VerificationResult::Verified(None)
    ));
    assert!(aggregate.provenance.is_none());
}

#[test]
#[timeout(30000)]
fn aggregate_unknown_takes_precedence_over_assumed() {
    let results = vec![
        SliceResult {
            index: 0,
            result: VerificationResult::Assumed("axiom".to_string()),
        },
        SliceResult {
            index: 1,
            result: VerificationResult::Unknown(UnknownReason::Timeout),
        },
    ];
    match aggregate_slice_results(results) {
        VerificationResult::Unknown(UnknownReason::Timeout) => {}
        other => panic!("expected Unknown, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn aggregate_all_assumed_returns_assumed() {
    let results = vec![
        SliceResult {
            index: 0,
            result: VerificationResult::Assumed("axiom-1".to_string()),
        },
        SliceResult {
            index: 1,
            result: VerificationResult::Assumed("axiom-2".to_string()),
        },
    ];
    match aggregate_slice_results(results) {
        VerificationResult::Assumed(reason) => {
            assert_eq!(
                reason, "axiom-1",
                "first Assumed reason should be preserved"
            );
        }
        other => panic!("expected Assumed, got {other:?}"),
    }
}

// --- Additional split_ensures tests: deep conjunction flattening ---

/// A deeply nested left-associative conjunction `((a && b) && c)` should
/// flatten into three individual slices, all with the same source index.
#[test]
#[timeout(30000)]
fn split_ensures_flattens_deep_left_associative_conjunction() {
    let deep_and = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(var("a")),
            BinOp::And,
            Arc::new(var("b")),
        )),
        BinOp::And,
        Arc::new(var("c")),
    );
    let ensures = [deep_and];
    let slices = split_ensures(&ensures);
    assert_eq!(
        slices.len(),
        3,
        "((a && b) && c) should flatten into 3 slices"
    );
    assert!(
        slices.iter().all(|s| s.index == 0),
        "all slices from one ensure should share index 0"
    );
    assert_eq!(slices[0].ensure.as_ref(), &var("a"));
    assert_eq!(slices[1].ensure.as_ref(), &var("b"));
    assert_eq!(slices[2].ensure.as_ref(), &var("c"));
}

/// A right-associative conjunction `(a && (b && c))` should also flatten.
#[test]
#[timeout(30000)]
fn split_ensures_flattens_deep_right_associative_conjunction() {
    let deep_and = PureExpr::BinOp(
        Arc::new(var("a")),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(var("b")),
            BinOp::And,
            Arc::new(var("c")),
        )),
    );
    let ensures = [deep_and];
    let slices = split_ensures(&ensures);
    assert_eq!(
        slices.len(),
        3,
        "(a && (b && c)) should flatten into 3 slices"
    );
    assert_eq!(slices[0].ensure.as_ref(), &var("a"));
    assert_eq!(slices[1].ensure.as_ref(), &var("b"));
    assert_eq!(slices[2].ensure.as_ref(), &var("c"));
}

/// Non-And binary operators (Or, Implies) should NOT be flattened - they
/// produce a single slice preserving the entire expression.
#[test]
#[timeout(30000)]
fn split_ensures_does_not_flatten_or() {
    let or_expr = PureExpr::BinOp(Arc::new(var("a")), BinOp::Or, Arc::new(var("b")));
    let ensures = [or_expr.clone()];
    let slices = split_ensures(&ensures);
    assert_eq!(slices.len(), 1, "Or should not be flattened");
    assert_eq!(slices[0].ensure.as_ref(), &or_expr);
}

/// Multiple ensures with mixed structures: one plain, one conjunction.
#[test]
#[timeout(30000)]
fn split_ensures_multiple_ensures_mixed_indices() {
    let plain = var("p");
    let conj = PureExpr::BinOp(Arc::new(var("a")), BinOp::And, Arc::new(var("b")));
    let ensures = [plain, conj];
    let slices = split_ensures(&ensures);
    assert_eq!(slices.len(), 3, "1 plain + 1 conjunction(2) = 3 slices");
    assert_eq!(slices[0].index, 0, "plain ensure -> index 0");
    assert_eq!(
        slices[1].index, 1,
        "first conjunct from ensure #1 -> index 1"
    );
    assert_eq!(
        slices[2].index, 1,
        "second conjunct from ensure #1 -> index 1"
    );
}

/// An existential nested inside an And should suppress flattening so that
/// the downstream negation pipeline can see the full context. (#2141, #2517)
#[test]
#[timeout(30000)]
fn split_ensures_existential_in_left_conjunct_suppresses_flatten() {
    let existential = exists_with_sort("y", ExprSort::Int, gt(var("y"), int(0)));
    let conj = PureExpr::BinOp(Arc::new(existential), BinOp::And, Arc::new(var("b")));
    let ensures = [conj.clone()];
    let slices = split_ensures(&ensures);
    assert_eq!(
        slices.len(),
        1,
        "existential in left conjunct should suppress flattening"
    );
    assert_eq!(slices[0].ensure.as_ref(), &conj);
}

/// A deeply nested existential (inside a BinOp inside an And) should also
/// suppress flattening.
#[test]
#[timeout(30000)]
fn split_ensures_deep_nested_existential_suppresses_flatten() {
    let deep_exists = PureExpr::BinOp(
        Arc::new(var("a")),
        BinOp::Implies,
        Arc::new(exists_with_sort("z", ExprSort::Int, gt(var("z"), int(0)))),
    );
    let conj = PureExpr::BinOp(Arc::new(deep_exists), BinOp::And, Arc::new(var("b")));
    let ensures = [conj];
    let slices = split_ensures(&ensures);
    assert_eq!(
        slices.len(),
        1,
        "deeply nested existential should suppress conjunction flattening"
    );
}

// --- Additional aggregate tests: ordering and mixed scenarios ---

/// When only Assumed and Verified results are present, Assumed takes precedence.
#[test]
#[timeout(30000)]
fn aggregate_assumed_mixed_with_verified_preserves_assumed() {
    let results = vec![
        SliceResult {
            index: 0,
            result: VerificationResult::Verified(None),
        },
        SliceResult {
            index: 1,
            result: VerificationResult::Assumed("axiom-trust".to_string()),
        },
        SliceResult {
            index: 2,
            result: VerificationResult::Verified(None),
        },
    ];
    match aggregate_slice_results(results) {
        VerificationResult::Assumed(reason) => {
            assert_eq!(reason, "axiom-trust");
        }
        other => panic!("expected Assumed, got {other:?}"),
    }
}

/// Full precedence chain: Failed > Unknown > Assumed > Verified.
/// When all four are present, Failed wins.
#[test]
#[timeout(30000)]
fn aggregate_full_precedence_chain() {
    let results = vec![
        SliceResult {
            index: 0,
            result: VerificationResult::Verified(None),
        },
        SliceResult {
            index: 1,
            result: VerificationResult::Assumed("axiom".to_string()),
        },
        SliceResult {
            index: 2,
            result: VerificationResult::Unknown(UnknownReason::Timeout),
        },
        SliceResult {
            index: 3,
            result: VerificationResult::Failed(Counterexample::empty()),
        },
    ];
    assert!(
        matches!(
            aggregate_slice_results(results),
            VerificationResult::Failed(_)
        ),
        "Failed should win over all other result types"
    );
}

/// Single-element results should pass through unchanged.
#[test]
#[timeout(30000)]
fn aggregate_single_verified() {
    let results = vec![SliceResult {
        index: 0,
        result: VerificationResult::Verified(Some(strict_summary(7))),
    }];
    let VerificationResult::Verified(Some(summary)) = aggregate_slice_results(results) else {
        panic!("single strict summary must pass through");
    };
    assert_eq!(summary.resolution_count, 7);
    assert!(summary.alethe_text.is_some());
}

/// Single Unknown should pass through.
#[test]
#[timeout(30000)]
fn aggregate_single_unknown() {
    let results = vec![SliceResult {
        index: 0,
        result: VerificationResult::Unknown(UnknownReason::Incomplete),
    }];
    match aggregate_slice_results(results) {
        VerificationResult::Unknown(UnknownReason::Incomplete) => {}
        other => panic!("expected Unknown(Incomplete), got {other:?}"),
    }
}

/// The UnknownReason variant should be preserved through aggregation.
#[test]
#[timeout(30000)]
fn aggregate_preserves_unknown_reason_variant() {
    let results = vec![
        SliceResult {
            index: 0,
            result: VerificationResult::Verified(None),
        },
        SliceResult {
            index: 1,
            result: VerificationResult::Unknown(UnknownReason::QuantifierRoundLimit),
        },
    ];
    match aggregate_slice_results(results) {
        VerificationResult::Unknown(UnknownReason::QuantifierRoundLimit) => {}
        other => panic!("expected Unknown(QuantifierRoundLimit), got {other:?}"),
    }
}

// ── Quantified Boolean equivalence split ─────────────────────────────
//
// `forall vs. L == R` with a quantifier on one side is a Boolean
// equivalence, so it is sliced into its two directions. Both slices must
// verify for the aggregate to verify (`aggregate_slice_results`), so the
// rewrite adds obligations and can never widen acceptance; it exists because
// the solver declines a quantifier nested under an iff (cc/fset `map_spec`).

#[test]
#[timeout(30000)]
fn quantified_bool_iff_splits_into_both_directions() {
    // forall y. contains(y) == (exists x. mem(x))
    let lhs = method_call(var("s"), "contains", vec![var("y")]);
    let rhs = exists_with_sort(
        "x",
        ExprSort::Int,
        method_call(var("s"), "mem", vec![var("x")]),
    );
    let ensures = vec![forall("y", eq(lhs.clone(), rhs.clone()))];
    let slices = split_ensures(&ensures);
    assert_eq!(
        slices.len(),
        2,
        "both directions must be sliced: {slices:?}"
    );
    assert!(slices.iter().all(|s| s.index == 0));
    let forward = forall(
        "y",
        PureExpr::BinOp(Arc::new(lhs.clone()), BinOp::Implies, Arc::new(rhs.clone())),
    );
    let backward = forall(
        "y",
        PureExpr::BinOp(Arc::new(rhs), BinOp::Implies, Arc::new(lhs)),
    );
    assert_eq!(slices[0].ensure.as_ref(), &forward);
    assert_eq!(slices[1].ensure.as_ref(), &backward);
}

#[test]
#[timeout(30000)]
fn quantified_bool_iff_split_needs_a_quantifier_side() {
    // No quantifier on either side: left intact, one slice.
    let ensures = vec![forall(
        "y",
        eq(
            method_call(var("s"), "contains", vec![var("y")]),
            method_call(var("t"), "contains", vec![var("y")]),
        ),
    )];
    let slices = split_ensures(&ensures);
    assert_eq!(slices.len(), 1);
    assert_eq!(slices[0].ensure.as_ref(), &ensures[0]);
}

#[test]
#[timeout(30000)]
fn quantified_iff_split_refuses_an_arithmetic_side() {
    // An arithmetic side is not a Boolean equivalence: splitting it would read
    // both operands through the bool coercion and be WEAKER than the equality.
    // The fail-closed answer is to leave the obligation whole.
    let arithmetic = add(var("n"), int(1));
    let quantified = exists_with_sort("x", ExprSort::Int, gt(var("x"), int(0)));
    let ensures = vec![forall("y", eq(arithmetic, quantified))];
    let slices = split_ensures(&ensures);
    assert_eq!(
        slices.len(),
        1,
        "arithmetic side must not be split: {slices:?}"
    );
    assert_eq!(slices[0].ensure.as_ref(), &ensures[0]);
}

#[test]
#[timeout(30000)]
fn quantified_iff_split_needs_a_binder() {
    // Unquantified `L == R` keeps its existing handling (no binder to rebuild).
    let ensures = vec![eq(
        method_call(var("s"), "contains", vec![var("y")]),
        exists_with_sort(
            "x",
            ExprSort::Int,
            method_call(var("s"), "mem", vec![var("x")]),
        ),
    )];
    let slices = split_ensures(&ensures);
    assert_eq!(slices.len(), 1);
    assert_eq!(slices[0].ensure.as_ref(), &ensures[0]);
}
