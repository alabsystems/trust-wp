// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod prepare_clauses;

use std::{collections::HashMap, sync::Arc};

use trust_wp_ay::{verify_function_with_modes, VerificationRequest, VerificationResult};
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use super::{
    build_post_refinement_obligations, build_pre_refinement_obligations, plan_external_refinement,
    report::{aggregate_refinement_counts, report_refinement_result, RefinementOutcome},
    ExternalRefinementPlan,
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

    assert!(
        obligations.is_empty(),
        "a trait ensures stated verbatim by the impl leaves no goal"
    );
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

    assert!(obligations.is_empty());
}

fn gt(var: &str, n: i64) -> PureExpr {
    PureExpr::BinOp(
        Arc::new(PureExpr::Var(var.to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(n.into())),
    )
}

/// WP-07 (1a): a trait method without a contract has `requires` = `true`, so
/// an impl precondition is a real goal, never dropped.
#[test]
fn test_pre_refinement_contractless_trait_keeps_impl_requires() {
    let obligations = build_pre_refinement_obligations(&[], &[gt("x", 0)]);
    assert_eq!(obligations, vec![gt("x", 0)]);
}

#[test]
fn test_pre_refinement_verbatim_and_true_clauses_are_dropped() {
    let obligations = build_pre_refinement_obligations(
        &[gt("x", 0)],
        &[gt("x", 0), PureExpr::Bool(true), gt("x", 5)],
    );
    assert_eq!(obligations, vec![gt("x", 5)]);
}

#[test]
fn test_pre_refinement_empty_impl_requires_has_no_goal() {
    assert!(build_pre_refinement_obligations(&[gt("x", 10)], &[]).is_empty());
}

/// WP-07 (1b): a weaker impl ensures still yields `impl_post => trait_post`.
#[test]
fn test_post_refinement_weaker_impl_ensures_is_a_goal() {
    let obligations = build_post_refinement_obligations(&[gt("result", -1)], &[gt("result", 0)]);
    assert_eq!(
        obligations,
        vec![PureExpr::BinOp(
            Arc::new(gt("result", -1)),
            BinOp::Implies,
            Arc::new(gt("result", 0)),
        )]
    );
}

#[test]
fn test_post_refinement_empty_trait_ensures_has_no_goal() {
    assert!(build_post_refinement_obligations(&[gt("result", 0)], &[]).is_empty());
    assert!(build_post_refinement_obligations(&[], &[PureExpr::Bool(true)]).is_empty());
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

/// WP-07 (1c): an external trait impl that adds `requires` is checked against
/// trust-wp's spec when there is one, and is `unknown` (an error) otherwise;
/// an impl without `requires` has no precondition goal and is never credited.
#[test]
fn test_external_refinement_plan() {
    assert_eq!(
        plan_external_refinement(true, true),
        ExternalRefinementPlan::CheckPrecondition
    );
    assert_eq!(
        plan_external_refinement(true, false),
        ExternalRefinementPlan::UnknownNoTraitContract
    );
    assert_eq!(
        plan_external_refinement(false, true),
        ExternalRefinementPlan::NoImplRequires
    );
    assert_eq!(
        plan_external_refinement(false, false),
        ExternalRefinementPlan::NoImplRequires
    );
}

/// A precondition-only (external trait) check never prints or credits
/// `refinement verified`, and is not an error when both directions hold.
#[test]
fn test_precondition_only_all_verified_is_not_an_error() {
    let counts = aggregate_refinement_counts(
        RefinementOutcome::Verified,
        RefinementOutcome::Verified,
        true,
        "test",
        EncodingErrorBreakdown::default(),
    );
    assert_eq!(counts.verified_delta, 0);
    assert_eq!(counts.failed_delta, 0);
    assert_eq!(counts.error_delta, 0);
}

/// `exists<x: Int> x == y@ && x > 0`
fn exists_binder_capture_clause() -> PureExpr {
    let x = || PureExpr::Var("x".to_string(), None);
    PureExpr::Exists {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(x()),
                BinOp::Eq,
                Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "y".to_string(),
                    None,
                )))),
            )),
            BinOp::And,
            Arc::new(PureExpr::BinOp(
                Arc::new(x()),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            )),
        )),
        triggers: Vec::new(),
    }
}

#[test]
fn test_param_rename_avoids_binder_capture() {
    let subs: HashMap<String, PureExpr> =
        [("y".to_string(), PureExpr::Var("x".to_string(), None))].into();
    let renamed = super::prepare::rename_impl_params(&exists_binder_capture_clause(), &subs);
    let PureExpr::Exists { var, body, .. } = &renamed else {
        panic!("expected exists, got {renamed:?}");
    };
    assert_ne!(var, "x", "binder must be alpha-renamed: {renamed:?}");
    // The renamed parameter stays free; the binder does not capture it.
    assert!(
        renamed.free_vars().contains("x"),
        "trait parameter x must remain free: {renamed:?}"
    );
    assert!(
        body.free_vars().contains(var.as_str()),
        "body must still use the (renamed) binder: {renamed:?}"
    );
}

#[test]
fn test_pre_refinement_captured_rename_is_not_a_verbatim_tautology() {
    let subs: HashMap<String, PureExpr> =
        [("y".to_string(), PureExpr::Var("x".to_string(), None))].into();
    let impl_pre = super::prepare::rename_impl_params(&exists_binder_capture_clause(), &subs);
    let goals = build_pre_refinement_obligations(&[PureExpr::Bool(true)], &[impl_pre]);
    assert_eq!(goals.len(), 1, "the impl requires is a goal: {goals:?}");
}

mod scope_closure {
    use std::collections::HashSet;

    use trust_wp_core::contract_parser::{parse_contract, parse_contract_written_types};

    use super::super::scope::{
        first_scope_dependent_name, first_unrecorded_written_type, ClauseKind,
    };

    fn check(clause: &str, params: &[&str]) -> Option<String> {
        let expr = parse_contract(clause).expect("clause parses");
        let params: HashSet<&str> = params.iter().copied().collect();
        first_scope_dependent_name(&expr, &params, ClauseKind::Ensures)
    }

    #[test]
    fn parameters_result_literals_and_operators_are_scope_free() {
        for clause in [
            "x@ > 0",
            "result@ == x@ + 1 && !(y@ < 3)",
            "old(x@) <= ^x@",
            "if x@ > 0 { result } else { true }",
            "forall<i: Int> 0 <= i && i < x@ ==> i < 100",
            "exists<i: Int> i == x@",
            "(x, y).0 == x",
            "x.field == y",
            "match x { (a, _) => a == y, _ => false }",
        ] {
            assert_eq!(check(clause, &["x", "y"]), None, "{clause}");
        }
    }

    fn check_requires(clause: &str, params: &[&str]) -> Option<String> {
        let expr = parse_contract(clause).expect("clause parses");
        let params: HashSet<&str> = params.iter().copied().collect();
        first_scope_dependent_name(&expr, &params, ClauseKind::Requires)
    }

    /// Review F2: `result` is the return value only in a postcondition.
    #[test]
    fn result_is_refused_in_a_precondition() {
        assert_eq!(check_requires("x@ > 0", &["x"]), None);
        assert!(check_requires("result == 0", &["x"]).is_some());
        assert!(check_requires("x == 0 && result == x", &["x"]).is_some());
        assert_eq!(check("result == 0", &["x"]), None);
    }

    /// Names in the synthesized `__trust_wp_` namespace, and binders named
    /// `result`, could alias the refinement's own positional names.
    #[test]
    fn reserved_identifiers_and_binders_are_refused() {
        for clause in [
            "__trust_wp_p0 == x",
            "forall<__trust_wp_p0: Int> __trust_wp_p0 == x@",
            "exists<result: Int> result == x@",
            "match x { __trust_wp_p1 => true }",
        ] {
            assert!(check(clause, &["x"]).is_some(), "{clause}");
        }
    }

    #[test]
    fn a_binder_shadowing_a_constant_name_is_scope_free() {
        assert_eq!(check("forall<K: Int> K > x@ || K <= x@", &["x"]), None);
    }

    #[test]
    fn free_constants_and_paths_are_refused() {
        assert_eq!(check("x > K", &["x"]).as_deref(), Some("identifier `K`"));
        assert!(check("x@ > a::K", &["x"]).is_some());
        assert!(check("x@ > <T as Tr>::K", &["x"]).is_some());
        // A name bound only inside a quantifier is free outside it.
        assert_eq!(
            check("(forall<y: Int> y > 0) && y > 0", &["x"]).as_deref(),
            Some("identifier `y`")
        );
        // Parameters of the other side are not parameters here.
        assert_eq!(check("y@ > 0", &["x"]).as_deref(), Some("identifier `y`"));
    }

    #[test]
    fn calls_and_method_calls_are_refused() {
        assert_eq!(check("x@ > k()", &["x"]).as_deref(), Some("call `k(..)`"));
        assert!(check("x@ > crate::a::k()", &["x"]).is_some());
        assert!(check("x.invariant()", &["x"]).is_some());
        assert!(check("x@.len() > 0", &["x"]).is_some());
        assert!(check("x == S { f: 1 }", &["x"]).is_some());
    }

    #[test]
    fn constructor_patterns_are_refused() {
        assert!(check("match x { Some(v) => v == 1, None => true }", &["x"]).is_some());
    }

    /// Refusal reason from the clause's AST or its written types.
    fn refusal(clause: &str, params: &[&str]) -> Option<String> {
        check(clause, params).or_else(|| {
            let written = parse_contract_written_types(clause).expect("clause parses");
            first_unrecorded_written_type(&written)
        })
    }

    #[test]
    fn binder_annotations_without_a_faithful_sort_are_refused() {
        // q1: a type alias. Both the AST (no sort) and the text refuse.
        assert_eq!(
            check("forall<v: Wd> v@ < 256", &["x"]).as_deref(),
            Some("binder `v` whose type has no faithful sort")
        );
        for (clause, reason) in [
            ("forall<v: Wd> v@ < 256", "type `Wd`"),
            // q3: a tuple of an alias.
            ("forall<p: (Wd, bool)> p.0@ < 256", "type `(Wd, bool)`"),
            ("forall<p: (u8, bool)> p.0@ < 256", "type `(u8, bool)`"),
            // Pointers and references.
            ("exists<v: *const Wd> v == v", "type `*const Wd`"),
            ("exists<v: &Int> v == v", "type `&Int`"),
            // Paths.
            ("forall<v: crate::t::Wd> v@ < 256", "type `crate::t::Wd`"),
            // Machine integers parse to the unbounded Int sort: the range is lost.
            ("forall<v: u8> v@ < 256", "type `u8`"),
            ("exists<v: usize> v@ == x@", "type `usize`"),
            // Elided binder types.
            (
                "exists<v> v == x",
                "a quantifier binder with no written type",
            ),
            // Closure parameters.
            ("(|v: Wd| v@ < 256) == (|v: Wd| v@ < 256)", "type `Wd`"),
            (
                "(|v| v) == (|v| v)",
                "a closure parameter with no written type",
            ),
            (
                "(|(a, b)| a) == (|(a, b)| a)",
                "a closure parameter with no written type",
            ),
        ] {
            let written = parse_contract_written_types(clause).expect("clause parses");
            assert_eq!(
                first_unrecorded_written_type(&written).as_deref(),
                Some(reason),
                "{clause}"
            );
        }
    }

    #[test]
    fn int_and_bool_binders_are_accepted() {
        for clause in [
            "forall<i: Int> 0 <= i && i < x@ ==> i < 100",
            "exists<b: bool> b == (x@ > 0)",
            "(|i: Int| i + 1) == (|i: Int| i + 1)",
        ] {
            assert_eq!(refusal(clause, &["x"]), None, "{clause}");
        }
    }

    #[test]
    fn casts_ascriptions_and_let_annotations_are_refused() {
        // A cast to anything but a fixed-width integer type of at most 64
        // bits (here a scope-dependent alias, and `Int`) does not parse, so
        // no refinement is ever built from it.
        for clause in ["(x as Wd)@ == 0", "(x as Int) == 0"] {
            assert!(parse_contract(clause).is_err(), "{clause}");
            assert!(parse_contract_written_types(clause).is_err(), "{clause}");
        }
        for (clause, reason) in [
            // q4: a primitive cast, which the AST now carries as Rust's `as`.
            ("(x as u8)@ == 0", "cast `as u8`"),
            ("(x : u32)@ == 0", "type ascription `: u32`"),
            ("{ let y: Wd = x; y@ < 256 }", "`let` annotation `: Wd`"),
            ("{ let y: Int = x@; y < 256 }", "`let` annotation `: Int`"),
            // Literal suffixes: the value is kept, the machine type dropped.
            ("255u8 + 1u8 == 0u8", "literal type suffix `u8`"),
            ("x@ == 1int", "literal type suffix `int`"),
            ("x == 0x10usize", "literal type suffix `usize`"),
            ("x == 1.5f32", "literal type suffix `f32`"),
        ] {
            assert_eq!(refusal(clause, &["x"]).as_deref(), Some(reason), "{clause}");
        }
    }

    /// The verbatim shortcut drops a goal when the trait and impl clause ASTs
    /// are equal. Clauses that differ only in a written type must never both
    /// pass the scope check with equal ASTs.
    #[test]
    fn clauses_differing_only_in_a_written_type_are_never_verbatim_equal() {
        for (trait_clause, impl_clause) in [
            ("(x as u8)@ == 0", "x@ == 0"),
            ("(x as u8)@ == 0", "(x as u16)@ == 0"),
            ("(x : u32)@ == 0", "x@ == 0"),
            ("forall<v: Wd> v@ < 256", "forall<v: Wd> v@ < 256"),
            ("forall<v: u8> v@ < 256", "forall<v: u64> v@ < 256"),
            ("forall<v: Int> v < 256", "forall<v: u8> v < 256"),
            ("forall<v: Int> v == v", "forall<v: bool> v == v"),
            ("forall<v> v@ < 256", "forall<v: u8> v@ < 256"),
            (
                "forall<p: (Wd, bool)> p.0@ < 256",
                "forall<p: (Wd, bool)> p.0@ < 256",
            ),
            ("exists<v: *const Wd> v == v", "exists<v: *const u8> v == v"),
            (
                "(|v: Wd| v@ < 256) == (|v: Wd| v@ < 256)",
                "(|v| v@ < 256) == (|v| v@ < 256)",
            ),
            (
                "{ let y: u8 = x; y@ < 256 }",
                "{ let y: u64 = x; y@ < 256 }",
            ),
            ("255u8 + 1u8 == 0u8", "255u16 + 1u16 == 0u16"),
            ("255u8 + 1u8 == 0u8", "255 + 1 == 0"),
            ("x == 1.5f32", "x == 1.5f64"),
        ] {
            let both_accepted =
                refusal(trait_clause, &["x"]).is_none() && refusal(impl_clause, &["x"]).is_none();
            let verbatim_equal =
                parse_contract(trait_clause).unwrap() == parse_contract(impl_clause).unwrap();
            assert!(
                !(both_accepted && verbatim_equal),
                "`{trait_clause}` and `{impl_clause}` would be dropped as verbatim"
            );
        }
        // Where both are accepted, the written type is in the AST.
        assert_ne!(
            parse_contract("forall<v: Int> v == v").unwrap(),
            parse_contract("forall<v: bool> v == v").unwrap()
        );
    }
}
