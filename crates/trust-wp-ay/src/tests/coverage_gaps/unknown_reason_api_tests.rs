// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for previously untested `UnknownReason` and `VerificationResult`
//! API methods, plus `negate_existential_postcondition()` direct unit tests.
//!
//! Part of #1481 (zero-coverage production function tests).

use ntest::timeout;

use super::*;

// ── UnknownReason::is_quantifier ────────────────────────────────────

#[test]
#[timeout(5000)]
fn test_is_quantifier_returns_true_for_all_quantifier_variants() {
    assert!(UnknownReason::Quantifiers.is_quantifier());
    assert!(UnknownReason::QuantifierRoundLimit.is_quantifier());
    assert!(UnknownReason::QuantifierDeferred.is_quantifier());
    assert!(UnknownReason::QuantifierUnhandled.is_quantifier());
    assert!(UnknownReason::QuantifierCegqiIncomplete.is_quantifier());
    assert!(UnknownReason::QuantifierEmatchingExistsIncomplete.is_quantifier());
}

#[test]
#[timeout(5000)]
fn test_is_quantifier_returns_false_for_non_quantifier_variants() {
    assert!(!UnknownReason::Timeout.is_quantifier());
    assert!(!UnknownReason::Incomplete.is_quantifier());
    assert!(!UnknownReason::SatModel.is_quantifier());
    assert!(!UnknownReason::MemoryOut.is_quantifier());
    assert!(!UnknownReason::UnsupportedMixedCollection.is_quantifier());
    assert!(!UnknownReason::Unspecified.is_quantifier());
    assert!(!UnknownReason::Demoted("sort_fallback".to_string()).is_quantifier());
    assert!(!UnknownReason::SolverPanic("crash".to_string()).is_quantifier());
    assert!(!UnknownReason::SolverMessage("custom".to_string()).is_quantifier());
}

// ── UnknownReason::is_timeout ───────────────────────────────────────

#[test]
#[timeout(5000)]
fn test_is_timeout_returns_true_only_for_timeout() {
    assert!(UnknownReason::Timeout.is_timeout());
}

#[test]
#[timeout(5000)]
fn test_is_timeout_returns_false_for_non_timeout_variants() {
    assert!(!UnknownReason::Incomplete.is_timeout());
    assert!(!UnknownReason::Quantifiers.is_timeout());
    assert!(!UnknownReason::QuantifierRoundLimit.is_timeout());
    assert!(!UnknownReason::SatModel.is_timeout());
    assert!(!UnknownReason::MemoryOut.is_timeout());
    assert!(!UnknownReason::UnsupportedMixedCollection.is_timeout());
    assert!(!UnknownReason::Unspecified.is_timeout());
    assert!(!UnknownReason::Demoted("detail".to_string()).is_timeout());
    assert!(!UnknownReason::SolverPanic("panic".to_string()).is_timeout());
    assert!(!UnknownReason::SolverMessage("msg".to_string()).is_timeout());
}

// ── UnknownReason::from_ay_unknown_reason ───────────────────────────

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_timeout() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::Timeout),
        UnknownReason::Timeout
    );
}

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_incomplete() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::Incomplete),
        UnknownReason::Incomplete
    );
}

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_memory_limit() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::MemoryLimit),
        UnknownReason::MemoryOut
    );
}

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_quantifier_round_limit() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::QuantifierRoundLimit),
        UnknownReason::QuantifierRoundLimit
    );
}

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_quantifier_deferred() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::QuantifierDeferred),
        UnknownReason::QuantifierDeferred
    );
}

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_quantifier_unhandled() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::QuantifierUnhandled),
        UnknownReason::QuantifierUnhandled
    );
}

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_quantifier_cegqi_incomplete() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::QuantifierCegqiIncomplete),
        UnknownReason::QuantifierCegqiIncomplete
    );
}

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_quantifier_ematching_exists_incomplete() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(
            &ay_dpll::UnknownReason::QuantifierEmatchingExistsIncomplete
        ),
        UnknownReason::QuantifierEmatchingExistsIncomplete
    );
}

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_resource_limit() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::ResourceLimit),
        UnknownReason::ResourceOut
    );
}

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_interrupted() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::Interrupted),
        UnknownReason::Interrupted
    );
}

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_split_limit() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::SplitLimit),
        UnknownReason::Incomplete
    );
}

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_expression_split() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::ExpressionSplit),
        UnknownReason::Incomplete
    );
}

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_unknown() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::Unknown),
        UnknownReason::Unspecified
    );
}

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_unsupported() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::Unsupported),
        UnknownReason::Unsupported
    );
}

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_unsupported_mixed_collection() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::UnsupportedMixedCollection),
        UnknownReason::UnsupportedMixedCollection
    );
}

#[test]
#[timeout(5000)]
fn test_from_ay_unknown_reason_internal_error() {
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&ay_dpll::UnknownReason::InternalError),
        UnknownReason::InternalError
    );
}

// ── VerificationResult::unknown_reason_str ──────────────────────────

#[test]
#[timeout(5000)]
fn test_unknown_reason_str_returns_str_for_unknown() {
    let result = VerificationResult::Unknown(UnknownReason::Timeout);
    assert_eq!(result.unknown_reason_str(), Some("timeout"));
}

#[test]
#[timeout(5000)]
fn test_unknown_reason_str_quantifier_round_limit() {
    let result = VerificationResult::Unknown(UnknownReason::QuantifierRoundLimit);
    assert_eq!(result.unknown_reason_str(), Some("quantifier-round-limit"));
}

#[test]
#[timeout(5000)]
fn test_unknown_reason_str_returns_none_for_verified() {
    let result = VerificationResult::Verified(None);
    assert_eq!(result.unknown_reason_str(), None);
}

#[test]
#[timeout(5000)]
fn test_unknown_reason_str_returns_none_for_failed() {
    let result = VerificationResult::Failed(Counterexample {
        values: vec![],
        violated_postcondition: None,
    });
    assert_eq!(result.unknown_reason_str(), None);
}

#[test]
#[timeout(5000)]
fn test_unknown_reason_str_returns_none_for_assumed() {
    let result = VerificationResult::Assumed("axiom-only".to_string());
    assert_eq!(result.unknown_reason_str(), None);
}

#[test]
#[timeout(5000)]
fn test_unknown_reason_str_solver_message() {
    let result =
        VerificationResult::Unknown(UnknownReason::SolverMessage("custom-reason".to_string()));
    assert_eq!(result.unknown_reason_str(), Some("custom-reason"));
}

#[test]
#[timeout(5000)]
fn test_unknown_reason_str_demoted() {
    let result =
        VerificationResult::Unknown(UnknownReason::Demoted("sort_fallback_to_int".to_string()));
    assert_eq!(result.unknown_reason_str(), Some("sort_fallback_to_int"));
}

// ── as_str for new quantifier variants ──────────────────────────────

#[test]
#[timeout(5000)]
fn test_as_str_for_new_quantifier_variants() {
    assert_eq!(
        UnknownReason::QuantifierRoundLimit.as_str(),
        "quantifier-round-limit"
    );
    assert_eq!(
        UnknownReason::QuantifierDeferred.as_str(),
        "quantifier-deferred"
    );
    assert_eq!(
        UnknownReason::QuantifierUnhandled.as_str(),
        "quantifier-unhandled"
    );
    assert_eq!(
        UnknownReason::QuantifierCegqiIncomplete.as_str(),
        "quantifier-cegqi-incomplete"
    );
    assert_eq!(
        UnknownReason::QuantifierEmatchingExistsIncomplete.as_str(),
        "quantifier-ematching-exists-incomplete"
    );
}

// ── negate_existential_postcondition ────────────────────────────────

use crate::verify::negate_existential_postcondition;

#[test]
#[timeout(5000)]
fn test_negate_existential_non_exists_returns_none() {
    let expr = gt(var("x"), int(0));
    assert!(negate_existential_postcondition(&expr).is_none());
}

#[test]
#[timeout(5000)]
fn test_negate_existential_simple_exists() {
    let expr = exists("a", gt(var("a"), int(0)));
    let result = negate_existential_postcondition(&expr);
    assert!(result.is_some());
    let result = result.unwrap();
    match &result {
        PureExpr::Forall { var, body, .. } => {
            assert_eq!(var, "a");
            assert!(matches!(
                body.as_ref(),
                PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, _)
            ));
        }
        other => panic!("expected Forall, got: {other:?}"),
    }
}

#[test]
#[timeout(5000)]
fn test_negate_existential_nested_exists() {
    let expr = exists("a", exists("b", gt(var("a"), var("b"))));
    let result = negate_existential_postcondition(&expr).unwrap();
    match &result {
        PureExpr::Forall {
            var: outer_var,
            body: outer_body,
            ..
        } => {
            assert_eq!(outer_var, "a");
            match outer_body.as_ref() {
                PureExpr::Forall {
                    var: inner_var,
                    body: inner_body,
                    ..
                } => {
                    assert_eq!(inner_var, "b");
                    assert!(matches!(
                        inner_body.as_ref(),
                        PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, _)
                    ));
                }
                other => panic!("expected inner Forall, got: {other:?}"),
            }
        }
        other => panic!("expected outer Forall, got: {other:?}"),
    }
}

#[test]
#[timeout(5000)]
fn test_negate_existential_var_returns_none() {
    assert!(negate_existential_postcondition(&var("result")).is_none());
}

#[test]
#[timeout(5000)]
fn test_negate_existential_bool_returns_none() {
    assert!(negate_existential_postcondition(&bool_expr(true)).is_none());
}

#[test]
#[timeout(5000)]
fn test_negate_existential_forall_returns_none() {
    let expr = forall("x", gt(var("x"), int(0)));
    assert!(negate_existential_postcondition(&expr).is_none());
}

#[test]
#[timeout(5000)]
fn test_negate_existential_preserves_triggers() {
    let trigger = vec![vec![method_call(var("a"), "len", vec![])]];
    let expr = exists_with_triggers("a", gt(var("a"), int(0)), trigger.clone());
    let result = negate_existential_postcondition(&expr).unwrap();
    match &result {
        PureExpr::Forall { triggers, .. } => {
            assert_eq!(triggers.len(), 1);
            assert_eq!(triggers, &trigger);
        }
        other => panic!("expected Forall with triggers, got: {other:?}"),
    }
}

#[test]
#[timeout(5000)]
fn test_negate_existential_preserves_var_sort() {
    let expr = exists_with_sort("a", ExprSort::Int, gt(var("a"), int(0)));
    let result = negate_existential_postcondition(&expr).unwrap();
    match &result {
        PureExpr::Forall { var_sort, .. } => {
            assert_eq!(*var_sort, Some(ExprSort::Int));
        }
        other => panic!("expected Forall with var_sort, got: {other:?}"),
    }
}

// ── SolveStatisticsSnapshot ─────────────────────────────────────────

#[test]
#[timeout(5000)]
fn test_solve_statistics_snapshot_default_is_zeroed() {
    let snapshot = SolveStatisticsSnapshot::default();
    assert_eq!(snapshot.decisions, 0);
    assert_eq!(snapshot.conflicts, 0);
    assert_eq!(snapshot.propagations, 0);
    assert_eq!(snapshot.theory_conflicts, 0);
    assert_eq!(snapshot.theory_propagations, 0);
    assert_eq!(snapshot.num_vars, 0);
    assert_eq!(snapshot.num_clauses, 0);
    assert_eq!(snapshot.num_assertions, 0);
}

#[test]
#[timeout(5000)]
fn test_solve_statistics_snapshot_eq_and_clone() {
    let a = SolveStatisticsSnapshot::default();
    let b = a.clone();
    assert_eq!(a, b);
}
