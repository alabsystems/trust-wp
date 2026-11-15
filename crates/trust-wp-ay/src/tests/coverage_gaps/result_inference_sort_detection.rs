// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for result_inference.rs sort detection edge cases.
//!
//! `expr_contains_result_var` is called at every BinOp(Eq/Ne) node during
//! constructor-equality datatype inference. It must correctly traverse all
//! PureExpr variants to detect whether `result` appears as a free variable.
//! An incorrect traversal silently skips datatype inference for that
//! postcondition shape, causing result to default to Int (unsound).
//!
//! Coverage targets:
//! - `expr_contains_result_var` — all PureExpr variant traversal arms
//! - `result_match_datatype_from_postcondition` — multi-clause edge cases
//!
//! Part of #1946 (result_inference.rs unit tests).

use std::sync::Arc;

use super::*;
use crate::{
    encoder::match_enc::MatchDatatypeKind,
    verify::{
        expr_contains_result_var, expr_requires_result_bool, result_is_bool_by_postcondition,
        result_match_datatype_from_postcondition,
    },
    AYEncoder,
};

#[path = "result_inference_sort_detection/result_collection_sort_from_postcondition.rs"]
mod result_collection_sort_from_postcondition;

// ── expr_contains_result_var: leaf cases ────────────────────────────

/// Var("result") is detected.
#[test]
#[timeout(30000)]
fn contains_result_var_direct() {
    assert!(expr_contains_result_var(&var("result")));
}

/// Var("x") is not detected.
#[test]
#[timeout(30000)]
fn contains_result_var_different_name() {
    assert!(!expr_contains_result_var(&var("x")));
}

/// Int literal does not contain result.
#[test]
#[timeout(30000)]
fn contains_result_var_int_literal() {
    assert!(!expr_contains_result_var(&int(42)));
}

/// Bool literal does not contain result.
#[test]
#[timeout(30000)]
fn contains_result_var_bool_literal() {
    assert!(!expr_contains_result_var(&bool_expr(true)));
}

// ── expr_contains_result_var: unary wrappers ────────────────────────

/// Deref(result) is detected.
#[test]
#[timeout(30000)]
fn contains_result_var_in_deref() {
    assert!(expr_contains_result_var(&deref(var("result"))));
}

/// Final(result) is detected.
#[test]
#[timeout(30000)]
fn contains_result_var_in_final() {
    assert!(expr_contains_result_var(&final_expr(var("result"))));
}

/// View(result) is detected.
#[test]
#[timeout(30000)]
fn contains_result_var_in_view() {
    assert!(expr_contains_result_var(&view(var("result"))));
}

/// Old(result) is detected.
#[test]
#[timeout(30000)]
fn contains_result_var_in_old() {
    assert!(expr_contains_result_var(&old(var("result"))));
}

/// UnOp(Not, result) is detected.
#[test]
#[timeout(30000)]
fn contains_result_var_in_not() {
    assert!(expr_contains_result_var(&not(var("result"))));
}

/// UnOp(Neg, result) is detected.
#[test]
#[timeout(30000)]
fn contains_result_var_in_neg() {
    assert!(expr_contains_result_var(&neg(var("result"))));
}

/// Deref(x) does not contain result.
#[test]
#[timeout(30000)]
fn contains_result_var_in_deref_no_result() {
    assert!(!expr_contains_result_var(&deref(var("x"))));
}

// ── expr_contains_result_var: BinOp arms ────────────────────────────

/// result in BinOp left operand.
#[test]
#[timeout(30000)]
fn contains_result_var_binop_left() {
    assert!(expr_contains_result_var(&gt(var("result"), int(0))));
}

/// result in BinOp right operand.
#[test]
#[timeout(30000)]
fn contains_result_var_binop_right() {
    assert!(expr_contains_result_var(&gt(int(0), var("result"))));
}

/// No result in either BinOp operand.
#[test]
#[timeout(30000)]
fn contains_result_var_binop_neither() {
    assert!(!expr_contains_result_var(&gt(var("x"), int(0))));
}

// ── expr_contains_result_var: Ite arms ──────────────────────────────

/// result in Ite condition.
#[test]
#[timeout(30000)]
fn contains_result_var_ite_condition() {
    assert!(expr_contains_result_var(&ite(
        var("result"),
        int(1),
        int(0)
    )));
}

/// result in Ite then-branch.
#[test]
#[timeout(30000)]
fn contains_result_var_ite_then() {
    assert!(expr_contains_result_var(&ite(
        bool_expr(true),
        var("result"),
        int(0)
    )));
}

/// result in Ite else-branch.
#[test]
#[timeout(30000)]
fn contains_result_var_ite_else() {
    assert!(expr_contains_result_var(&ite(
        bool_expr(true),
        int(1),
        var("result")
    )));
}

/// No result in any Ite arm.
#[test]
#[timeout(30000)]
fn contains_result_var_ite_none() {
    assert!(!expr_contains_result_var(&ite(
        bool_expr(true),
        int(1),
        int(0)
    )));
}

// ── expr_contains_result_var: MethodCall ─────────────────────────────

/// result in MethodCall receiver.
#[test]
#[timeout(30000)]
fn contains_result_var_method_call_receiver() {
    assert!(expr_contains_result_var(&method_call(
        var("result"),
        "len",
        vec![]
    )));
}

/// result in MethodCall args.
#[test]
#[timeout(30000)]
fn contains_result_var_method_call_args() {
    assert!(expr_contains_result_var(&method_call(
        var("x"),
        "push",
        vec![var("result")]
    )));
}

/// No result in MethodCall.
#[test]
#[timeout(30000)]
fn contains_result_var_method_call_none() {
    assert!(!expr_contains_result_var(&method_call(
        var("x"),
        "push",
        vec![int(1)]
    )));
}

// ── expr_contains_result_var: LogicFnCall ────────────────────────────

/// result in LogicFnCall args.
#[test]
#[timeout(30000)]
fn contains_result_var_logic_fn_call() {
    assert!(expr_contains_result_var(&logic_fn_call(
        "Some",
        vec![var("result")]
    )));
}

/// No result in LogicFnCall args.
#[test]
#[timeout(30000)]
fn contains_result_var_logic_fn_call_no_result() {
    assert!(!expr_contains_result_var(&logic_fn_call(
        "Some",
        vec![int(42)]
    )));
}

// ── expr_contains_result_var: quantifiers ────────────────────────────

/// result inside Forall body.
#[test]
#[timeout(30000)]
fn contains_result_var_forall_body() {
    assert!(expr_contains_result_var(&forall(
        "x",
        gt(var("result"), var("x"))
    )));
}

/// result inside Exists body.
#[test]
#[timeout(30000)]
fn contains_result_var_exists_body() {
    assert!(expr_contains_result_var(&exists(
        "x",
        eq(var("result"), var("x"))
    )));
}

/// No result inside quantifier.
#[test]
#[timeout(30000)]
fn contains_result_var_quantifier_no_result() {
    assert!(!expr_contains_result_var(&forall(
        "x",
        gt(var("x"), int(0))
    )));
}

// ── expr_contains_result_var: Match ──────────────────────────────────

/// result in Match scrutinee.
#[test]
#[timeout(30000)]
fn contains_result_var_match_scrutinee() {
    let expr = match_expr(var("result"), vec![(Pattern::Wildcard, int(0))]);
    assert!(expr_contains_result_var(&expr));
}

/// result in Match arm body.
#[test]
#[timeout(30000)]
fn contains_result_var_match_arm_body() {
    let expr = match_expr(
        var("x"),
        vec![(Pattern::Wildcard, eq(var("result"), int(0)))],
    );
    assert!(expr_contains_result_var(&expr));
}

/// No result in Match.
#[test]
#[timeout(30000)]
fn contains_result_var_match_no_result() {
    let expr = match_expr(var("x"), vec![(Pattern::Wildcard, int(0))]);
    assert!(!expr_contains_result_var(&expr));
}

// ── expr_contains_result_var: Let ────────────────────────────────────

/// result in Let value.
#[test]
#[timeout(30000)]
fn contains_result_var_let_value() {
    let expr = let_bind("x", var("result"), int(0));
    assert!(expr_contains_result_var(&expr));
}

/// result in Let body.
#[test]
#[timeout(30000)]
fn contains_result_var_let_body() {
    let expr = let_bind("x", int(0), var("result"));
    assert!(expr_contains_result_var(&expr));
}

/// No result in Let.
#[test]
#[timeout(30000)]
fn contains_result_var_let_no_result() {
    let expr = let_bind("x", int(0), var("x"));
    assert!(!expr_contains_result_var(&expr));
}

// ── expr_contains_result_var: LetAssume ──────────────────────────────

/// result in LetAssume assumption.
#[test]
#[timeout(30000)]
fn contains_result_var_let_assume_assumption() {
    let expr = let_assume(gt(var("result"), int(0)), bool_expr(true));
    assert!(expr_contains_result_var(&expr));
}

/// result in LetAssume body.
#[test]
#[timeout(30000)]
fn contains_result_var_let_assume_body() {
    let expr = let_assume(bool_expr(true), var("result"));
    assert!(expr_contains_result_var(&expr));
}

/// No result in LetAssume.
#[test]
#[timeout(30000)]
fn contains_result_var_let_assume_no_result() {
    let expr = let_assume(bool_expr(true), var("x"));
    assert!(!expr_contains_result_var(&expr));
}

// ── expr_contains_result_var: LetObligation ──────────────────────────

/// result in LetObligation obligation.
#[test]
#[timeout(30000)]
fn contains_result_var_let_obligation_obligation() {
    let expr = let_obligation(gt(var("result"), int(0)), bool_expr(true));
    assert!(expr_contains_result_var(&expr));
}

/// result in LetObligation body.
#[test]
#[timeout(30000)]
fn contains_result_var_let_obligation_body() {
    let expr = let_obligation(bool_expr(true), var("result"));
    assert!(expr_contains_result_var(&expr));
}

/// No result in LetObligation.
#[test]
#[timeout(30000)]
fn contains_result_var_let_obligation_no_result() {
    let expr = let_obligation(bool_expr(true), var("x"));
    assert!(!expr_contains_result_var(&expr));
}

// ── expr_contains_result_var: Closure ────────────────────────────────

/// result in Closure body.
#[test]
#[timeout(30000)]
fn contains_result_var_closure_body() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(eq(var("result"), var("x"))),
    };
    assert!(expr_contains_result_var(&expr));
}

/// No result in Closure body.
#[test]
#[timeout(30000)]
fn contains_result_var_closure_no_result() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(var("x")),
    };
    assert!(!expr_contains_result_var(&expr));
}

// ── expr_contains_result_var: deep nesting ──────────────────────────

/// result deeply nested through multiple expression forms.
#[test]
#[timeout(30000)]
fn contains_result_var_deeply_nested() {
    // and(forall("x", ite(true, let_bind("y", 0, old(deref(result))), false)), true)
    let deep = and(
        forall(
            "x",
            ite(
                bool_expr(true),
                let_bind("y", int(0), old(deref(var("result")))),
                bool_expr(false),
            ),
        ),
        bool_expr(true),
    );
    assert!(expr_contains_result_var(&deep));
}

/// Same structure without result returns false.
#[test]
#[timeout(30000)]
fn contains_result_var_deeply_nested_no_result() {
    let deep = and(
        forall(
            "x",
            ite(
                bool_expr(true),
                let_bind("y", int(0), old(deref(var("z")))),
                bool_expr(false),
            ),
        ),
        bool_expr(true),
    );
    assert!(!expr_contains_result_var(&deep));
}

// ── expr_requires_result_bool: edge cases not in verify/tests.rs ────

/// result == true inside implies connector is detected.
#[test]
#[timeout(30000)]
fn requires_result_bool_implies_with_eq_true() {
    // implies(x > 0, result == true)
    let expr = implies(gt(var("x"), int(0)), eq(var("result"), bool_expr(true)));
    assert!(expr_requires_result_bool(&expr));
}

/// Ite with result in then/else branches is NOT detected (only condition).
#[test]
#[timeout(30000)]
fn requires_result_bool_ite_result_in_branch_not_detected() {
    // ite(true, result, false) — result is in then-branch, not condition
    let expr = ite(bool_expr(true), var("result"), bool_expr(false));
    assert!(!expr_requires_result_bool(&expr));
}

/// LetAssume preserves Bool-context result detection through its body.
#[test]
#[timeout(30000)]
fn requires_result_bool_let_assume_returns_true() {
    let expr = let_assume(bool_expr(true), var("result"));
    assert!(expr_requires_result_bool(&expr));
}

/// LetObligation preserves Bool-context result detection through its body.
#[test]
#[timeout(30000)]
fn requires_result_bool_let_obligation_returns_true() {
    let expr = let_obligation(bool_expr(true), var("result"));
    assert!(expr_requires_result_bool(&expr));
}

// ── result_is_bool_by_postcondition: multi-clause ───────────────────

/// Second postcondition clause with result as Bool is detected.
#[test]
#[timeout(30000)]
fn result_is_bool_multiple_clauses_second_matches() {
    let ensures = vec![
        gt(var("x"), int(0)),               // First: no result Bool signal
        eq(var("result"), bool_expr(true)), // Second: result == true
    ];
    assert!(result_is_bool_by_postcondition(&ensures));
}

/// All postconditions are Int comparisons — not Bool.
#[test]
#[timeout(30000)]
fn result_is_bool_all_int_comparisons() {
    let ensures = vec![gt(var("result"), int(0)), lt(var("result"), int(100))];
    assert!(!result_is_bool_by_postcondition(&ensures));
}

// ── result_match_datatype_from_postcondition: edge cases ────────────

/// Constructor equality on the left side of Eq: Some(v) == result.
#[test]
#[timeout(30000)]
fn constructor_eq_reversed_operand_order() {
    let ensures = vec![eq(logic_fn_call("Some", vec![var("v")]), var("result"))];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt),
    );
}

/// Ne with constructor: result != None implies OptionInt.
#[test]
#[timeout(30000)]
fn constructor_ne_implies_datatype() {
    let ensures = vec![ne(var("result"), var("None"))];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt),
    );
}

/// Constructor inside Ite then-branch: ite(c, result == Some(v), true).
#[test]
#[timeout(30000)]
fn constructor_eq_inside_ite() {
    let ensures = vec![ite(
        var("c"),
        eq(var("result"), logic_fn_call("Some", vec![var("v")])),
        bool_expr(true),
    )];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt),
    );
}

/// Constructor inside Forall body.
#[test]
#[timeout(30000)]
fn constructor_eq_inside_forall() {
    let ensures = vec![forall(
        "x",
        implies(
            gt(var("x"), int(0)),
            eq(var("result"), logic_fn_call("Ok", vec![var("x")])),
        ),
    )];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::ResultIntInt),
    );
}

/// Constructor inside MethodCall arg — traversal must reach it.
#[test]
#[timeout(30000)]
fn constructor_eq_inside_method_call_arg() {
    let ensures = vec![method_call(
        var("self"),
        "check",
        vec![eq(var("result"), logic_fn_call("Some", vec![int(1)]))],
    )];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt),
    );
}

/// Constructor inside LogicFnCall arg.
#[test]
#[timeout(30000)]
fn constructor_eq_inside_logic_fn_call_arg() {
    let ensures = vec![logic_fn_call(
        "invariant",
        vec![eq(var("result"), logic_fn_call("Err", vec![int(0)]))],
    )];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::ResultIntInt),
    );
}

/// Constructor inside Let value.
#[test]
#[timeout(30000)]
fn constructor_eq_inside_let_value() {
    let ensures = vec![let_bind(
        "check",
        eq(var("result"), logic_fn_call("Some", vec![int(1)])),
        var("check"),
    )];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt),
    );
}

/// Constructor inside LetAssume assumption.
#[test]
#[timeout(30000)]
fn constructor_eq_inside_let_assume_assumption() {
    let ensures = vec![let_assume(
        eq(var("result"), logic_fn_call("Ok", vec![var("v")])),
        gt(var("v"), int(0)),
    )];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::ResultIntInt),
    );
}

/// Constructor inside LetObligation obligation.
#[test]
#[timeout(30000)]
fn constructor_eq_inside_let_obligation() {
    let ensures = vec![let_obligation(
        eq(var("result"), logic_fn_call("Some", vec![int(5)])),
        bool_expr(true),
    )];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt),
    );
}

/// Constructor inside Closure body.
#[test]
#[timeout(30000)]
fn constructor_eq_inside_closure() {
    let ensures = vec![PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(eq(var("result"), logic_fn_call("Some", vec![var("x")]))),
    }];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt),
    );
}

/// Constructor inside Match arm body (not as scrutinee-based detection).
#[test]
#[timeout(30000)]
fn constructor_eq_inside_match_arm_body() {
    let ensures = vec![match_expr(
        var("flag"),
        vec![(
            Pattern::Wildcard,
            eq(var("result"), logic_fn_call("Ok", vec![int(0)])),
        )],
    )];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::ResultIntInt),
    );
}

/// Constructor inside Exists body.
#[test]
#[timeout(30000)]
fn constructor_eq_inside_exists() {
    let ensures = vec![exists(
        "v",
        eq(var("result"), logic_fn_call("Some", vec![var("v")])),
    )];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt),
    );
}

/// Constructor inside wrapper (Old, Deref, Final, View).
#[test]
#[timeout(30000)]
fn constructor_eq_inside_old_wrapper() {
    let ensures = vec![old(eq(var("result"), logic_fn_call("None", vec![])))];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt),
    );
}

/// Consistent constructors across multiple ensures clauses.
#[test]
#[timeout(30000)]
fn constructor_eq_consistent_across_clauses() {
    let ensures = vec![
        eq(var("result"), logic_fn_call("Some", vec![int(1)])),
        ne(var("result"), var("None")),
    ];
    assert_eq!(
        result_match_datatype_from_postcondition(&ensures),
        Some(MatchDatatypeKind::OptionInt),
    );
}

/// Conflicting constructors across ensures clauses returns None.
#[test]
#[timeout(30000)]
fn constructor_eq_conflicting_across_clauses() {
    let ensures = vec![
        eq(var("result"), logic_fn_call("Some", vec![int(1)])),
        eq(var("result"), logic_fn_call("Ok", vec![int(1)])),
    ];
    assert_eq!(result_match_datatype_from_postcondition(&ensures), None);
}
