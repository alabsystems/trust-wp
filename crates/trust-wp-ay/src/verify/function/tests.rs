// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for function verification — extracted from inline tests (#1669).

use std::sync::Arc;

use ay_dpll::api::{SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::{
    formula::{
        intern_sort_name,
        internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_name},
        named_struct_ctor_name, ExprSort, MatchArm, Pattern, PureExpr,
    },
    logic::{LogicFnDef, LogicMode, TypeInvariantDef},
    TrackLevel,
};

use super::{
    super::setup::{setup_verification_encoder, VerificationSetup},
    assert_by_value_alias_constraints, expr_contains_embedded_existential,
    expr_contains_embedded_universal, extract_invariant_receiver_var, has_open_logic_fns,
    instantiate_embedded_existentials_with_body_witness, is_axiom_only_function,
    is_universal_quantifier,
    obligation::{
        sequence_tail_reverse_push_front_index_proof_assert_follows_requires,
        sequence_tail_reverse_push_front_index_proof_assert_matches,
    },
    precheck_ghost_context_postconditions, precheck_logic_body_postconditions,
    precheck_result_constructor_match_postconditions,
    precheck_result_match_ite_constructor_postconditions, skolemize_negated_universal,
    verify_function_with_modes, verify_function_with_modes_outcome,
};
use crate::{
    encoder::AYEncoder,
    tests::helpers::{
        add, and, bool_expr, deref, eq, exists, final_expr, forall, ge, gt, implies, int, ite, le,
        logic_fn_call, lt, match_expr, mul, not, or, sub, var, var_with_sort, view,
    },
    verify::{expr_contains_result_var, VerificationRequest, VerificationResult},
};

fn method_call(receiver: PureExpr, method: &str) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args: vec![],
    }
}

fn method_call_with_args(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

#[test]
#[timeout(30000)]
fn verify_function_with_modes_empty_obligation_has_accepted_evidence() {
    let x = var("x");
    let requires = vec![ge(x, int(0))];
    let request = VerificationRequest::new(&requires, &[]);

    let outcome = verify_function_with_modes_outcome(request.clone())
        .expect("empty-obligation outcome should encode");
    assert!(
        matches!(outcome.result, VerificationResult::Verified(_)),
        "outcome API should keep the verified result: {:?}",
        outcome.result
    );
    let evidence = outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .expect("empty-obligation outcome should carry solver evidence");
    assert!(
        evidence.accepted_for_consumer,
        "empty-obligation solver evidence should be accepted for consumers: {evidence:?}"
    );
    assert!(
        evidence.result.eq_ignore_ascii_case("unsat") || evidence.result.starts_with("Unsat"),
        "empty-obligation evidence should be UNSAT, got {}",
        evidence.result
    );

    let legacy = verify_function_with_modes(request).expect("legacy wrapper should encode");
    assert!(
        matches!(legacy, VerificationResult::Verified(_)),
        "legacy wrapper should preserve verified result with accepted evidence: {legacy:?}"
    );
}

#[test]
#[timeout(30000)]
fn requirement_entails_same_logic_postcondition_with_accepted_evidence() {
    let t = var("t");
    let post = ge(logic_fn_call("tree_size", vec![t.clone()]), int(0));
    let recursive_tree_size = open_logic_fn(
        "tree_size",
        vec!["tree"],
        logic_fn_call("tree_size", vec![var("tree")]),
    );
    let requires = vec![post.clone()];
    let ensures = vec![post];
    let logic_fns = vec![recursive_tree_size];

    let request = VerificationRequest::new(&requires, &ensures).logic_fns(Some(&logic_fns));
    let outcome = verify_function_with_modes_outcome(request.clone())
        .expect("self-entailment over logic calls should encode");

    assert!(
        matches!(outcome.result, VerificationResult::Verified(_)),
        "requirement-identical postcondition should verify structurally: {:?}",
        outcome.result
    );
    let evidence = outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .expect("structural verification should carry accepted evidence");
    assert!(
        evidence.accepted_for_consumer,
        "structural evidence should be accepted for consumers: {evidence:?}"
    );

    let legacy = verify_function_with_modes(request).expect("legacy wrapper should encode");
    assert!(
        matches!(legacy, VerificationResult::Verified(_)),
        "legacy wrapper should accept structural evidence: {legacy:?}"
    );
}

#[test]
#[timeout(30000)]
fn closure_postcondition_mut_does_not_match_current_receiver_as_final_receiver() {
    let requires = vec![method_call_with_args(
        var("c_current"),
        "postcondition_mut",
        vec![var("x"), final_expr(var("c_current")), var("call_0")],
    )];
    let ensures = vec![method_call_with_args(
        var("c"),
        "postcondition_mut",
        vec![var("x"), final_expr(var("c")), var("result")],
    )];
    let return_expr = var("call_0");

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("stale receiver test should encode");

    assert!(
        !matches!(result, VerificationResult::Verified(_)),
        "a stale/current closure receiver must not structurally discharge a final receiver \
         postcondition_mut: {result:?}"
    );
}

fn proof_assert_ghost_seq_state_2616() -> (Vec<PureExpr>, Vec<PureExpr>, Vec<PureExpr>) {
    let seq_sort = ExprSort::Datatype(intern_sort_name("creusot_std::Seq"));
    let call_4 = var_with_sort("call_4", seq_sort.clone());
    let v = var_with_sort("v", seq_sort);
    let ghost_alias = eq(v, final_expr(call_4.clone()));
    let requires = vec![
        ghost_alias.clone(),
        eq(call_4.clone(), logic_fn_call("seq_empty", vec![])),
        eq(method_call_with_args(call_4.clone(), "len", vec![]), int(0)),
        eq(
            view(final_expr(call_4.clone())),
            method_call_with_args(call_4.clone(), "push_back", vec![int(30)]),
        ),
    ];
    let ensures = vec![eq(
        method_call_with_args(
            method_call_with_args(call_4, "push_back", vec![int(30)]),
            "index_logic",
            vec![int(0)],
        ),
        int(30),
    )];
    (requires, ensures, vec![ghost_alias])
}

#[test]
#[timeout(30000)]
fn final_borrows_select_field_option_selector_verifies() {
    let tuple_get_0 = tuple_field_logic_fn_name(0);
    let tuple_get_1 = tuple_field_logic_fn_name(1);
    let x_sort = ExprSort::MutRef(Box::new(ExprSort::Tuple(2)));
    let elem_ref_sort = ExprSort::MutRef(Box::new(ExprSort::Int));
    let x = var_with_sort("x", x_sort);
    let result = var_with_sort("result", elem_ref_sort.clone());
    let r = var("r");

    let x0 = logic_fn_call(&tuple_get_0, vec![x.clone()]);
    let x1 = logic_fn_call(&tuple_get_1, vec![x.clone()]);
    let some_payload = logic_fn_call(&tuple_get_0, vec![x0.clone()]);
    let discriminant = method_call(x0.clone(), "discriminant");

    let return_expr = PureExpr::LetAssume {
        assumption: Arc::new(or(
            eq(discriminant.clone(), int(0)),
            eq(discriminant.clone(), int(1)),
        )),
        body: Arc::new(ite(eq(discriminant, int(0)), x1.clone(), some_payload)),
    };

    let some_arm_body = and(
        and(
            eq(result.clone(), r.clone()),
            eq(
                logic_fn_call(&tuple_get_0, vec![deref(x.clone())]),
                logic_fn_call("Some", vec![deref(r.clone())]),
            ),
        ),
        eq(
            logic_fn_call(&tuple_get_0, vec![final_expr(x)]),
            logic_fn_call("Some", vec![final_expr(r)]),
        ),
    );
    let ensures = vec![PureExpr::Match {
        scrutinee: Arc::new(x0),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                body: eq(result.clone(), x1),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Wildcard)),
                },
                body: PureExpr::Exists {
                    var: "r".to_string(),
                    var_sort: Some(elem_ref_sort),
                    body: Arc::new(some_arm_body),
                    triggers: vec![],
                },
            },
        ],
    }];

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "final_borrows select_field selector shape should verify: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn final_borrows_result_as_mut_selector_verifies() {
    let tuple_get_0 = tuple_field_logic_fn_name(0);
    let result_sort = ExprSort::Datatype(intern_sort_name("OwnResult"));
    let self_sort = ExprSort::MutRef(Box::new(result_sort.clone()));
    let t_sort = ExprSort::MutRef(Box::new(ExprSort::TypeParam(intern_sort_name("T"))));
    let e_sort = ExprSort::MutRef(Box::new(ExprSort::TypeParam(intern_sort_name("E"))));

    let self_var = var_with_sort("self", self_sort);
    let result = var_with_sort("result", result_sort);
    let t = var("t");
    let e = var("e");
    let payload = logic_fn_call(&tuple_get_0, vec![self_var.clone()]);
    let discr = method_call(deref(self_var.clone()), "discriminant");
    let ok_result = logic_fn_call("OwnResult::Ok", vec![payload.clone()]);
    let err_result = logic_fn_call("OwnResult::Err", vec![payload]);

    let return_expr = PureExpr::LetAssume {
        assumption: Arc::new(or(eq(discr.clone(), int(0)), eq(discr.clone(), int(1)))),
        body: Arc::new(ite(eq(discr, int(0)), ok_result, err_result)),
    };

    let ok_body = and(
        and(
            eq(
                deref(self_var.clone()),
                logic_fn_call("OwnResult::Ok", vec![deref(t.clone())]),
            ),
            eq(
                final_expr(self_var.clone()),
                logic_fn_call("OwnResult::Ok", vec![final_expr(t.clone())]),
            ),
        ),
        eq(
            result.clone(),
            logic_fn_call("OwnResult::Ok", vec![t.clone()]),
        ),
    );
    let err_body = and(
        and(
            eq(
                deref(self_var.clone()),
                logic_fn_call("OwnResult::Err", vec![deref(e.clone())]),
            ),
            eq(
                final_expr(self_var),
                logic_fn_call("OwnResult::Err", vec![final_expr(e.clone())]),
            ),
        ),
        eq(result, logic_fn_call("OwnResult::Err", vec![e.clone()])),
    );
    let ensures = vec![PureExpr::Exists {
        var: "t".to_string(),
        var_sort: Some(t_sort),
        body: Arc::new(or(
            ok_body,
            PureExpr::Exists {
                var: "e".to_string(),
                var_sort: Some(e_sort),
                body: Arc::new(err_body),
                triggers: vec![],
            },
        )),
        triggers: vec![],
    }];

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "OwnResult::as_mut selector shape should verify: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn extracts_var_from_direct_method_call() {
    // x.__trust_wp_invariant_Vec()
    let expr = method_call(var("x"), "__trust_wp_invariant_Vec");
    assert_eq!(
        extract_invariant_receiver_var(&expr, "__trust_wp_invariant_Vec"),
        Some("x".to_string())
    );
}

#[test]
#[timeout(30000)]
fn extracts_var_through_deref() {
    // (*x).__trust_wp_invariant_Vec()
    let expr = method_call(
        PureExpr::Deref(Arc::new(var("x"))),
        "__trust_wp_invariant_Vec",
    );
    assert_eq!(
        extract_invariant_receiver_var(&expr, "__trust_wp_invariant_Vec"),
        Some("x".to_string())
    );
}

#[test]
#[timeout(30000)]
fn returns_none_for_wrong_method_name() {
    let expr = method_call(var("x"), "__trust_wp_invariant_Vec");
    assert_eq!(
        extract_invariant_receiver_var(&expr, "__trust_wp_invariant_HashMap"),
        None
    );
}

#[test]
#[timeout(30000)]
fn returns_none_for_non_method_call() {
    assert_eq!(
        extract_invariant_receiver_var(&var("x"), "__trust_wp_invariant_Vec"),
        None
    );
}

#[test]
#[timeout(30000)]
fn returns_none_for_non_var_receiver() {
    // (a + b).__trust_wp_invariant_Vec() — receiver is BinOp, not Var
    let expr = method_call(
        PureExpr::BinOp(
            Arc::new(var("a")),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(var("b")),
        ),
        "__trust_wp_invariant_Vec",
    );
    assert_eq!(
        extract_invariant_receiver_var(&expr, "__trust_wp_invariant_Vec"),
        None
    );
}

#[test]
#[timeout(30000)]
fn returns_none_for_nested_deref() {
    // (**x).__trust_wp_invariant_Vec() — double deref, inner is Deref not Var
    let expr = method_call(
        PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(var("x"))))),
        "__trust_wp_invariant_Vec",
    );
    assert_eq!(
        extract_invariant_receiver_var(&expr, "__trust_wp_invariant_Vec"),
        None
    );
}

// ── Vacuity guard regression tests (#2663) ─────────────────────────────────
//
// These tests verify that ay-level function encoding correctly produces
// non-vacuous proofs for simple patterns. They also test that the vacuity
// guard correctly detects contradictory preconditions and false assumptions.

/// Simple function with precondition and postcondition.
///
/// `f(x: i32) -> i32` with `requires(x > 0)`, `ensures(result > x)`,
/// body `return_expr = x + 1`.
#[test]
#[timeout(30000)]
fn test_vacuity_simple_function_non_vacuous() {
    let requires = vec![gt(var("x"), int(0))];
    let ensures = vec![gt(var("result"), var("x"))];
    let return_expr = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    let is_vacuous = matches!(
        &result,
        VerificationResult::Unknown(ref reason) if reason.as_str().contains("vacuous")
    );
    assert!(
        !is_vacuous,
        "simple function must not be vacuous at ay level: {result:?}"
    );
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "simple function should verify: x+1 > x when x > 0: {result:?}"
    );
}

/// Contradictory requires should trigger vacuity detection.
///
/// `requires(x > 0 && x < 0)` is UNSAT on its own → vacuous proof.
#[test]
#[timeout(30000)]
fn test_vacuity_contradictory_requires_detected() {
    let requires = vec![and(gt(var("x"), int(0)), lt(var("x"), int(0)))];
    let ensures = vec![bool_expr(true)]; // trivial postcondition

    let result = verify_function_with_modes(VerificationRequest::new(&requires, &ensures))
        .expect("encoding should succeed");

    let is_vacuous = matches!(
        &result,
        VerificationResult::Unknown(ref reason) if reason.as_str().contains("vacuous")
    );
    assert!(
        is_vacuous,
        "contradictory requires must be detected as vacuous: {result:?}"
    );
}

/// False assumption injected as call_assumption should trigger vacuity.
///
/// This simulates what happens when a trusted function with `#[ensures(false)]`
/// is called — its postcondition `false` becomes a caller assumption.
#[test]
#[timeout(30000)]
fn test_vacuity_false_assumption_detected() {
    let requires = vec![
        gt(var("x"), int(0)),
        bool_expr(false), // simulates #[ensures(false)] from trusted callee
    ];
    let ensures = vec![eq(var("result"), int(42))]; // any postcondition
    let return_expr = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    let is_vacuous = matches!(
        &result,
        VerificationResult::Unknown(ref reason) if reason.as_str().contains("vacuous")
    );
    assert!(
        is_vacuous,
        "false assumption must be detected as vacuous: {result:?}"
    );
}

/// A literal false obligation after an already-verified slice is classified
/// against fresh base state, not the reused incremental solver.
#[test]
#[timeout(30000)]
fn literal_false_after_verified_slice_uses_fresh_base_state() {
    let ensures = vec![
        eq(var("result"), int(0)),
        bool_expr(false),
        gt(var("result"), int(0)),
    ];
    let return_expr = int(0);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    match &result {
        VerificationResult::Failed(_) => {}
        VerificationResult::Verified(_) => {
            panic!("literal false obligation must not verify");
        }
        other => {
            panic!("expected Failed for literal false slice on satisfiable base, got: {other:?}")
        }
    }
}

#[test]
#[timeout(30000)]
fn hashmap_list_resize_positive_size_shape_false_postcondition_is_not_verified() {
    let ensures = vec![lt(int(0), mul(int(-1), int(2)))];

    let result = verify_function_with_modes(VerificationRequest::new(&[], &ensures))
        .expect("encoding should succeed");

    assert!(
        !matches!(result, VerificationResult::Verified(_)),
        "retired hashmap/list positive-size shortcut shape must not verify false arithmetic: {result:?}"
    );
}

fn result_match_ensure(some_body: PureExpr, none_body: PureExpr) -> PureExpr {
    PureExpr::Match {
        scrutinee: Arc::new(var("result")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("n".to_string()))),
                },
                body: some_body,
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                body: none_body,
            },
        ],
    }
}

fn open_logic_fn(name: &str, params: Vec<&str>, body: PureExpr) -> LogicFnDef {
    LogicFnDef::new(
        name.to_string(),
        format!("crate::{name}"),
        params.into_iter().map(str::to_string).collect(),
        body,
    )
    .with_mode(LogicMode::Open)
}

#[test]
#[timeout(30000)]
fn result_constructor_precheck_rejects_nontrivial_selected_arm() {
    let ensures = vec![result_match_ensure(eq(var("n"), int(1)), bool_expr(true))];
    let return_expr = logic_fn_call("Some", vec![int(2)]);

    let result =
        precheck_result_constructor_match_postconditions(&[], &ensures, Some(&return_expr));

    assert!(
        !matches!(result, Some(VerificationResult::Verified(_))),
        "constructor-match precheck must not verify a selected arm that is not trivially true: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn result_constructor_precheck_accepts_multi_field_tuple_arm() {
    let ensures = vec![PureExpr::Match {
        scrutinee: Arc::new(var("result")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Pair".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("x0".to_string()),
                        Pattern::Binding("x1".to_string()),
                    ]))),
                },
                body: and(eq(var("x0"), int(0)), eq(var("x1"), int(1))),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: bool_expr(false),
            },
        ],
    }];
    let return_expr = logic_fn_call("Pair", vec![int(0), int(1)]);

    let result =
        precheck_result_constructor_match_postconditions(&[], &ensures, Some(&return_expr));

    assert!(
        matches!(result, Some(VerificationResult::Verified(_))),
        "constructor-match precheck should verify selected tuple arm: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn result_match_ite_precheck_rejects_false_selected_branch() {
    let ensures = vec![result_match_ensure(eq(var("n"), int(1)), bool_expr(true))];
    let return_expr = ite(
        var_with_sort("flag", ExprSort::Bool),
        logic_fn_call("Some", vec![int(2)]),
        logic_fn_call("None", vec![]),
    );

    let result =
        precheck_result_match_ite_constructor_postconditions(&[], &ensures, Some(&return_expr));

    assert!(
        !matches!(result, Some(VerificationResult::Verified(_))),
        "ITE result-match precheck must not verify a branch whose selected arm is false: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn logic_body_precheck_rejects_unmet_logic_fn_requires() {
    let guarded_inc = LogicFnDef::new_with_requires(
        "guarded_inc".to_string(),
        "crate::guarded_inc".to_string(),
        vec!["x".to_string()],
        vec![gt(var("x"), int(0))],
        add(var("x"), int(1)),
    )
    .with_mode(LogicMode::Open);
    let ensures = vec![eq(
        var("result"),
        logic_fn_call("guarded_inc", vec![var("x")]),
    )];
    let return_expr = add(var("x"), int(1));
    let logic_fns = vec![guarded_inc];

    let result =
        precheck_logic_body_postconditions(&[], &ensures, Some(&return_expr), Some(&logic_fns));

    assert!(
        !matches!(result, Some(VerificationResult::Verified(_))),
        "logic-body precheck must not inline a logic body whose requires are not established: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn logic_body_precheck_rejects_mismatched_visible_body_equality() {
    let inc = open_logic_fn("inc", vec!["x"], add(var("x"), int(1)));
    let ensures = vec![eq(var("result"), logic_fn_call("inc", vec![var("x")]))];
    let return_expr = add(var("x"), int(2));
    let logic_fns = vec![inc];

    let result =
        precheck_logic_body_postconditions(&[], &ensures, Some(&return_expr), Some(&logic_fns));

    assert!(
        !matches!(result, Some(VerificationResult::Verified(_))),
        "logic-body precheck must not verify a return expression that differs from the visible body: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn logic_body_precheck_fails_body_expanded_false_postcondition() {
    let always_false = open_logic_fn("always_false", vec![], bool_expr(false));
    let ensures = vec![logic_fn_call("always_false", vec![])];
    let logic_fns = vec![always_false];

    let result = precheck_logic_body_postconditions(&[], &ensures, None, Some(&logic_fns));

    assert!(
        matches!(result, Some(VerificationResult::Failed(_))),
        "logic-body precheck must classify an expanded false postcondition as failed, got: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn ghost_context_precheck_rejects_wrong_context_fact() {
    let ghost_context = vec![eq(var("x"), int(42))];
    let ensures = vec![eq(var("x"), int(43))];

    let result =
        precheck_ghost_context_postconditions(&[], &ensures, None, Some(&ghost_context), None);

    assert!(
        !matches!(result, Some(VerificationResult::Verified(_))),
        "ghost-context precheck must not verify a postcondition from a mismatched context fact: {result:?}"
    );
}

fn seq_len(seq: PureExpr) -> PureExpr {
    method_call_with_args(seq, "len", vec![])
}

fn seq_index(seq: PureExpr, index: PureExpr) -> PureExpr {
    method_call_with_args(seq, "index_logic", vec![index])
}

fn seq_reverse(seq: PureExpr) -> PureExpr {
    method_call_with_args(seq, "reverse", vec![])
}

fn seq_tail_reverse_push_front(seq: PureExpr) -> PureExpr {
    let tail = method_call_with_args(
        seq.clone(),
        "subsequence",
        vec![int(1), seq_len(seq.clone())],
    );
    method_call_with_args(
        seq_reverse(tail),
        "push_front",
        vec![seq_index(seq, int(0))],
    )
}

fn sequence_lasso_quantifier(seq: PureExpr, use_previous_reverse_index: bool) -> PureExpr {
    let i = var("i");
    let reverse_index = if use_previous_reverse_index {
        sub(i.clone(), int(1))
    } else {
        i.clone()
    };
    forall(
        "i",
        implies(
            and(le(int(0), i.clone()), lt(i.clone(), seq_len(seq.clone()))),
            eq(
                seq_index(seq_tail_reverse_push_front(seq.clone()), i.clone()),
                ite(
                    eq(i.clone(), int(0)),
                    seq_index(seq.clone(), int(0)),
                    seq_index(seq_reverse(seq), reverse_index),
                ),
            ),
        ),
    )
}

fn sequence_lasso_guarded_obligation(use_previous_reverse_index: bool) -> PureExpr {
    let seq = var("s");
    implies(
        gt(seq_len(seq.clone()), int(0)),
        sequence_lasso_quantifier(seq, use_previous_reverse_index),
    )
}

#[test]
#[timeout(30000)]
fn sequence_lasso_direct_check_accepts_exact_guarded_shape() {
    let ensure = sequence_lasso_guarded_obligation(true);

    assert!(
        sequence_tail_reverse_push_front_index_proof_assert_matches(&ensure),
        "exact guarded sequence lasso proof_assert shape should match"
    );
}

#[test]
#[timeout(30000)]
fn sequence_lasso_direct_check_verifies_before_smt() {
    let ensure = sequence_lasso_guarded_obligation(true);

    let outcome = verify_function_with_modes_outcome(VerificationRequest::new(&[], &[ensure]))
        .expect("encoding");

    assert!(
        matches!(outcome.result, VerificationResult::Verified(_)),
        "exact guarded sequence lasso proof_assert should verify directly: {:?}",
        outcome.result
    );
}

#[test]
#[timeout(30000)]
fn sequence_lasso_direct_check_rejects_missing_len_guard() {
    let ensure = sequence_lasso_quantifier(var("s"), true);

    assert!(
        !sequence_tail_reverse_push_front_index_proof_assert_matches(&ensure),
        "sequence lasso shape must require the explicit s.len() > 0 guard"
    );
}

#[test]
#[timeout(30000)]
fn sequence_lasso_direct_check_accepts_bare_forall_with_required_guard() {
    let seq = var("s");
    let ensure = sequence_lasso_quantifier(seq.clone(), true);
    let requires = vec![gt(seq_len(seq), int(0))];

    assert!(
        sequence_tail_reverse_push_front_index_proof_assert_follows_requires(&ensure, &requires),
        "bare proof_assert forall should match when s.len() > 0 is an explicit requirement"
    );
}

#[test]
#[timeout(30000)]
fn sequence_lasso_direct_check_accepts_bare_forall_with_required_alias_guard() {
    let seq = var("s");
    let alias = var("s_view");
    let ensure = sequence_lasso_quantifier(alias.clone(), true);
    let requires = vec![gt(seq_len(seq.clone()), int(0)), eq(seq, alias)];

    assert!(
        sequence_tail_reverse_push_front_index_proof_assert_follows_requires(&ensure, &requires),
        "bare proof_assert forall should match an explicitly aliased guarded sequence"
    );
}

#[test]
#[timeout(30000)]
fn sequence_lasso_direct_check_accepts_bare_forall_with_required_view_alias_guard() {
    let seq = var("s");
    let alias = var("s_view");
    let ensure = sequence_lasso_quantifier(alias.clone(), true);
    let requires = vec![gt(seq_len(seq.clone()), int(0)), eq(view(seq), alias)];

    assert!(
        sequence_tail_reverse_push_front_index_proof_assert_follows_requires(&ensure, &requires),
        "bare proof_assert forall should match a transparent view alias of the guarded sequence"
    );
}

#[test]
#[timeout(30000)]
fn sequence_lasso_direct_check_rejects_alias_without_explicit_equality() {
    let seq = var("s");
    let alias = var("s_view");
    let ensure = sequence_lasso_quantifier(alias, true);
    let requires = vec![gt(seq_len(seq), int(0))];

    assert!(
        !sequence_tail_reverse_push_front_index_proof_assert_follows_requires(&ensure, &requires),
        "bare proof_assert forall over an alias must require an explicit sequence equality"
    );
}

#[test]
#[timeout(30000)]
fn sequence_lasso_direct_check_rejects_alias_for_different_guarded_sequence() {
    let seq = var("s");
    let other = var("t");
    let alias = var("s_view");
    let ensure = sequence_lasso_quantifier(alias.clone(), true);
    let requires = vec![gt(seq_len(seq), int(0)), eq(other, alias)];

    assert!(
        !sequence_tail_reverse_push_front_index_proof_assert_follows_requires(&ensure, &requires),
        "bare proof_assert forall must not use an alias equality for a different sequence"
    );
}

#[test]
#[timeout(30000)]
fn sequence_lasso_direct_check_rejects_aliased_mismatched_body() {
    let seq = var("s");
    let alias = var("s_view");
    let ensure = sequence_lasso_quantifier(alias.clone(), false);
    let requires = vec![gt(seq_len(seq.clone()), int(0)), eq(seq, alias)];

    assert!(
        !sequence_tail_reverse_push_front_index_proof_assert_follows_requires(&ensure, &requires),
        "sequence lasso alias path must keep the exact theorem body check"
    );
}

#[test]
#[timeout(30000)]
fn sequence_lasso_direct_check_rejects_bare_forall_without_required_guard() {
    let ensure = sequence_lasso_quantifier(var("s"), true);

    assert!(
        !sequence_tail_reverse_push_front_index_proof_assert_follows_requires(&ensure, &[]),
        "bare proof_assert forall must not match without an explicit s.len() > 0 requirement"
    );
}

#[test]
#[timeout(30000)]
fn sequence_lasso_direct_check_rejects_mismatched_body() {
    let ensure = sequence_lasso_guarded_obligation(false);

    assert!(
        !sequence_tail_reverse_push_front_index_proof_assert_matches(&ensure),
        "sequence lasso shape must reject a body that does not use s.reverse()[i - 1]"
    );
}

fn option_result_nonnegative_postcondition() -> PureExpr {
    match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                eq(var("x"), int(0)),
            ),
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("j".to_string()))),
                },
                ge(var("j"), int(0)),
            ),
        ],
    )
}

fn recursive_option_contract_callee() -> LogicFnDef {
    let mut callee = LogicFnDef::new_with_requires(
        "find_lasso_aux".to_string(),
        "test::find_lasso_aux".to_string(),
        vec!["x".to_string()],
        vec![ge(var("x"), int(0))],
        logic_fn_call("None", vec![]),
    )
    .with_mode(LogicMode::Default)
    .with_return_sort(Some(ExprSort::Datatype(intern_sort_name("OptionInt"))));
    callee.set_is_recursive(true);
    callee.set_ensures(vec![option_result_nonnegative_postcondition()]);
    callee
}

#[test]
#[timeout(30000)]
fn direct_recursive_call_result_match_uses_callee_contract() {
    let callee = recursive_option_contract_callee();
    let requires = vec![ge(var("x"), int(0))];
    let ensures = vec![option_result_nonnegative_postcondition()];
    let return_expr = logic_fn_call("find_lasso_aux", vec![var("x")]);
    let logic_fns = vec![callee];

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&return_expr))
            .logic_fns(Some(&logic_fns)),
    );

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "direct recursive-call result-match postcondition should verify from the callee contract: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn direct_recursive_call_contract_requires_must_hold() {
    let callee = recursive_option_contract_callee();
    let ensures = vec![option_result_nonnegative_postcondition()];
    let return_expr = logic_fn_call("find_lasso_aux", vec![var("x")]);
    let logic_fns = vec![callee];

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .return_expr(Some(&return_expr))
            .logic_fns(Some(&logic_fns)),
    );

    assert!(
        !matches!(result, Ok(VerificationResult::Verified(_))),
        "callee contract must not be used when instantiated requires are unavailable: {result:?}"
    );
}

fn condition_bool_contract_callee() -> LogicFnDef {
    let mut callee = LogicFnDef::new_with_requires(
        "branch_fact".to_string(),
        "test::branch_fact".to_string(),
        vec!["x".to_string()],
        vec![ge(var("x"), int(0))],
        var_with_sort("opaque_branch_fact_body", ExprSort::Bool),
    )
    .with_opaque(true)
    .with_return_sort(Some(ExprSort::Bool));
    callee.set_ensures(vec![var("result")]);
    callee
}

#[test]
#[timeout(30000)]
fn logic_call_in_ite_condition_asserts_callee_contract() {
    let callee = condition_bool_contract_callee();
    let requires = vec![ge(var("x"), int(0))];
    let ensures = vec![eq(var("result"), int(0))];
    let return_expr = ite(logic_fn_call("branch_fact", vec![var("x")]), int(0), int(1));
    let logic_fns = vec![callee];

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&return_expr))
            .logic_fns(Some(&logic_fns)),
    );

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "callee contract from an ITE condition should make the false branch unreachable: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn logic_call_in_ite_condition_requires_must_hold() {
    let callee = condition_bool_contract_callee();
    let ensures = vec![eq(var("result"), int(0))];
    let return_expr = ite(logic_fn_call("branch_fact", vec![var("x")]), int(0), int(1));
    let logic_fns = vec![callee];

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .return_expr(Some(&return_expr))
            .logic_fns(Some(&logic_fns)),
    );

    assert!(
        !matches!(result, Ok(VerificationResult::Verified(_))),
        "callee contract from an ITE condition must not be used without its requires: {result:?}"
    );
}

/// Regression test for bug/181_ident (#5): a logic function whose body contains
/// an Int-valued `if a < b { b } else { a }` ITE must be encodable inside the
/// defining-axiom `forall` body without leaking a global ITE auxiliary
/// constant.
///
/// Before the fix, `encode_pure` for an Int-sorted ITE always declared a
/// top-level `__trust_wp_ite_int_aux_N` constant and asserted the two implication
/// guards globally — even while encoding the body of a quantified defining
/// axiom. That made the bound parameters `a`/`b` reference a free constant
/// outside the quantifier, pinning `logic_max(a, b)` to a single arbitrary
/// value and turning `result == logic_max(a@, b@)` into an Unknown VC.
///
/// After the fix, the encoder emits a real `ite` term via `safe_ite` when
/// `quantifier_depth > 0`, so the axiom reads
/// `forall a, b. logic_max(a, b) = ite(a < b, b, a)` (rewritten by `eq_term`
/// to `forall a, b. ite(a < b, logic_max(a, b) = b, logic_max(a, b) = a)`),
/// and the postcondition trigger on `logic_max(a, b)` correctly fires for the
/// ground call.
#[test]
#[timeout(30000)]
fn open_logic_ite_int_body_axiom_verifies_max_postcondition() {
    // logic fn max_int(a: Int, b: Int) -> Int { if a < b { b } else { a } }
    let max_int = open_logic_fn(
        "max_int",
        vec!["a", "b"],
        ite(lt(var("a"), var("b")), var("b"), var("a")),
    );

    // The function under verification:
    //   #[ensures(result == max_int(a, b))]
    //   fn max_runtime(a: Int, b: Int) -> Int { if a < b { b } else { a } }
    //
    // We model this by returning the same ITE expression as the logic body and
    // asserting the postcondition references the logic function.
    let return_expr = ite(lt(var("a"), var("b")), var("b"), var("a"));
    let ensures = vec![eq(
        var("result"),
        logic_fn_call("max_int", vec![var("a"), var("b")]),
    )];
    let logic_fns = vec![max_int];

    let request = VerificationRequest::new(&[], &ensures)
        .return_expr(Some(&return_expr))
        .logic_fns(Some(&logic_fns));

    let outcome =
        verify_function_with_modes_outcome(request.clone()).expect("encoding should succeed");
    assert!(
        matches!(outcome.result, VerificationResult::Verified(_)),
        "Open-mode logic fn with Int-ITE body must verify against the same \
         runtime ITE return: got {:?}",
        outcome.result
    );

    let result = verify_function_with_modes(request).expect("encoding should succeed");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "legacy wrapper should preserve verified result with accepted solver \
         evidence (not demote via evidence gap): got {result:?}"
    );
}

#[cfg(test)]
mod alias_constraints;
#[cfg(test)]
mod axiom_detection;
#[cfg(test)]
mod axiom_only;
#[cfg(test)]
mod deep_model;
#[cfg(test)]
mod ghost_context_consumption;
#[cfg(test)]
mod ghost_context_logic;
#[cfg(test)]
mod ghost_data_structure;
#[cfg(test)]
mod instantiate_embedded_existentials;
#[cfg(test)]
mod skolemize;
#[cfg(test)]
mod tuple_results;
#[cfg(test)]
mod universal_quantifier;

// ────────────────────────────────────────────────────────────────────
// tract19 — prophecy-fold soundness pins (Final-collapse audit)
//
// `^e` names the value a mutable borrow holds when it EXPIRES; the expression
// underneath is the borrowed place's value in the CURRENT state. Every
// syntactic rule whose `true` DISCHARGES an obligation must therefore be
// opaque to `Final`. The permissive collapse survives on refusal-only paths,
// where it can misclassify but never manufacture a proof — those are pinned
// here too, so that the split stays deliberate rather than accidental.
// ────────────────────────────────────────────────────────────────────

#[test]
#[timeout(10000)]
fn prophecy_is_opaque_to_the_accepting_literal_folders() {
    use super::{eval_simple_bool_literal, eval_simple_int_literal, ProphecyFold};

    let prophecy = final_expr(int(3));
    assert_eq!(
        eval_simple_int_literal(&prophecy, ProphecyFold::Opaque),
        None,
        "`^3` must not evaluate to 3 on an accepting path"
    );
    assert_eq!(
        eval_simple_int_literal(&prophecy, ProphecyFold::Collapse),
        Some(3),
        "the refusal-only fold is retained deliberately"
    );

    // The shape that made `bug/final_borrows::not_final_borrow_works`'s
    // premise fold, mirrored into the ACCEPTING direction: `(^3)@ == 3`.
    // (This is the family of the closed false accept; the encoder-side
    // refusal is pinned in `encoder/final_collapse_guard.rs`.)
    let accepting_shape = eq(view(final_expr(int(3))), int(3));
    assert_eq!(
        eval_simple_bool_literal(&accepting_shape, ProphecyFold::Opaque),
        None,
        "`(^3)@ == 3` must not fold to `true` — that is the false accept"
    );
    assert_eq!(
        eval_simple_bool_literal(&accepting_shape, ProphecyFold::Collapse),
        Some(true),
    );

    // Same-state projections stay foldable in both modes.
    for fold in [ProphecyFold::Opaque, ProphecyFold::Collapse] {
        assert_eq!(eval_simple_int_literal(&view(int(7)), fold), Some(7));
        assert_eq!(eval_simple_int_literal(&deref(int(7)), fold), Some(7));
        assert_eq!(
            eval_simple_int_literal(&PureExpr::Old(Arc::new(int(7))), fold),
            Some(7)
        );
    }
}

/// `postcondition_true_under_context`'s OWN literal folders no longer see
/// through a prophecy. A `true` from this function returns `Verified` with no
/// solver call.
///
/// ★ RESIDUAL, pinned honestly: its first disjunct is
/// `is_trivially_true_postcondition`, whose evaluators live in
/// `verify/postcondition.rs` and DO still fold `^e`. They are deliberately
/// left folding — see the `★ RESIDUAL` comment on `eval_int_literal_expr`
/// there: at that layer `Final(<literal>)` is ambiguous between the driver's
/// borrowed-place substitution (dangerous) and binder-erasing substitution of a
/// logic-fn formal or quantifier binder (licensed by Phase 1, and measurably
/// load-bearing). The probe below therefore uses a division shape, which
/// `is_trivially_true_postcondition` refuses outright
/// (`expr_contains_div_or_mod`), so it isolates this function's own folders.
#[test]
#[timeout(10000)]
fn postcondition_true_under_context_does_not_see_through_a_prophecy() {
    use std::sync::Arc;

    use trust_wp_core::formula::BinOp;

    use super::{postcondition_true_under_context, ProphecyFold};

    // `(^6)@ / 2 == 3` — true under the old collapse, refused now.
    let prophecy_div = eq(
        view(PureExpr::BinOp(
            Arc::new(final_expr(int(6))),
            BinOp::Div,
            Arc::new(int(2)),
        )),
        int(3),
    );
    assert_eq!(
        super::eval_simple_bool_literal(&prophecy_div, ProphecyFold::Collapse),
        Some(true),
        "sanity: the old collapse did fold this to `true`"
    );
    assert!(
        !postcondition_true_under_context(&[], None, &prophecy_div),
        "`(^6)@ / 2 == 3` must not be accepted without a solve"
    );

    // The non-prophecy sibling still short-circuits.
    let plain_div = eq(
        view(PureExpr::BinOp(
            Arc::new(int(6)),
            BinOp::Div,
            Arc::new(int(2)),
        )),
        int(3),
    );
    assert!(postcondition_true_under_context(&[], None, &plain_div));
}

#[test]
#[timeout(10000)]
fn expr_equiv_for_arithmetic_refuses_the_asymmetric_prophecy_collapse() {
    use super::expr_equiv_for_arithmetic;

    // `^x` is NOT the same arithmetic expression as `x`.
    assert!(!expr_equiv_for_arithmetic(&final_expr(var("x")), &var("x")));
    assert!(!expr_equiv_for_arithmetic(&var("x"), &final_expr(var("x"))));
    // Two prophecies of the same shape stay comparable.
    assert!(expr_equiv_for_arithmetic(
        &final_expr(var("x")),
        &final_expr(var("x"))
    ));
    // A same-state `View` projection over a prophecy is still peeled.
    assert!(expr_equiv_for_arithmetic(
        &view(final_expr(var("x"))),
        &final_expr(var("x"))
    ));
    // `Old`/`Deref` remain same-state projections and keep collapsing.
    assert!(expr_equiv_for_arithmetic(&deref(var("x")), &var("x")));
}

#[test]
#[timeout(10000)]
fn strict_positivity_does_not_transfer_through_a_prophecy() {
    use super::expr_is_strictly_positive_under_requirements;

    let requires = vec![gt(var("x"), int(0))];
    assert!(
        expr_is_strictly_positive_under_requirements(&var("x"), requires.iter()),
        "`x > 0` discharges `x > 0`"
    );
    assert!(
        !expr_is_strictly_positive_under_requirements(&final_expr(var("x")), requires.iter()),
        "`x > 0` must NOT discharge `^x > 0` — the prophecy names another state"
    );
}

#[test]
#[timeout(10000)]
fn vacuity_precheck_keeps_the_refusal_only_prophecy_fold() {
    use super::requirements_are_obviously_contradictory;

    // The refusal-only fold over `^<constant>` is RETAINED: a premise set
    // containing `(^1)@ == 7` is still flagged obviously contradictory,
    // because the only outcome of this function is a vacuity DEMOTION — a
    // refusal, never a proof. (Historical note: the driver used to MINT this
    // very premise for `bug/final_borrows::not_final_borrow_works` by
    // advancing borrow-chain bases as `Final(<their constant value>)`; #124
    // fixed the driver to mint per-borrow prophecy carriers instead, so the
    // shape no longer occurs on the honest path — but if it ever reappears,
    // demoting remains the correct fail-closed answer.)
    assert!(requirements_are_obviously_contradictory(&[eq(
        view(final_expr(int(1))),
        int(7)
    )]));

    // ★#124 — the HONEST path: the driver now mints the premise with a real
    // per-borrow carrier (`(^r1)@ == 7` over a MutRef-sorted variable). That
    // premise is satisfiable and must NOT be flagged contradictory — the
    // fabricated vacuity demotion is gone and the obligation gets a real
    // solve (`not_final_borrow_works` verifies honestly).
    {
        use trust_wp_core::formula::ExprSort;
        let carrier = PureExpr::Var(
            "r1".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        );
        assert!(
            !requirements_are_obviously_contradictory(&[eq(
                view(PureExpr::Final(std::sync::Arc::new(carrier))),
                int(7)
            )]),
            "a prophecy over a real per-borrow carrier is a satisfiable premise — \
             it must reach the solver, not the vacuity demotion"
        );
    }
}
