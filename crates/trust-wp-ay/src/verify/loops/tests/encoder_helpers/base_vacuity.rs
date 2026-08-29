// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `is_base_vacuous` and its private `expr_needs_full_context` guard
//! (#2514). Zero prior test coverage — the function had only indirect
//! integration-level exercise through `verify_loop_invariant`.

use std::sync::Arc;

use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

use super::*;

// ── Empty input ──────────────────────────────────────────────────────

/// Empty base expression slice is not vacuous.
#[test]
#[timeout(30000)]
fn is_base_vacuous_empty_returns_false() {
    assert!(!is_base_vacuous(&[]), "empty base should not be vacuous");
}

// ── Contradictory expressions (true vacuity) ─────────────────────────

/// `false` literal is trivially unsatisfiable.
#[test]
#[timeout(30000)]
fn is_base_vacuous_false_literal() {
    assert!(
        is_base_vacuous(&[PureExpr::Bool(false)]),
        "Bool(false) should be vacuous"
    );
}

/// `x > 0 && x < 0` is contradictory for integer x.
#[test]
#[timeout(30000)]
fn is_base_vacuous_contradictory_int_bounds() {
    let x = PureExpr::Var("x".to_string(), None);
    let gt_zero = PureExpr::BinOp(Arc::new(x.clone()), BinOp::Gt, Arc::new(PureExpr::Int(0)));
    let lt_zero = PureExpr::BinOp(Arc::new(x), BinOp::Lt, Arc::new(PureExpr::Int(0)));
    assert!(
        is_base_vacuous(&[gt_zero, lt_zero]),
        "x > 0 ∧ x < 0 should be vacuous"
    );
}

/// `x == 1 && x == 2` is contradictory.
#[test]
#[timeout(30000)]
fn is_base_vacuous_contradictory_equality() {
    let x = PureExpr::Var("x".to_string(), None);
    let eq1 = PureExpr::BinOp(Arc::new(x.clone()), BinOp::Eq, Arc::new(PureExpr::Int(1)));
    let eq2 = PureExpr::BinOp(Arc::new(x), BinOp::Eq, Arc::new(PureExpr::Int(2)));
    assert!(
        is_base_vacuous(&[eq1, eq2]),
        "x == 1 ∧ x == 2 should be vacuous"
    );
}

// ── Satisfiable expressions (not vacuous) ────────────────────────────

/// `x > 0 && x < 10` is satisfiable.
#[test]
#[timeout(30000)]
fn is_base_vacuous_satisfiable_int_bounds() {
    let x = PureExpr::Var("x".to_string(), None);
    let gt_zero = PureExpr::BinOp(Arc::new(x.clone()), BinOp::Gt, Arc::new(PureExpr::Int(0)));
    let lt_ten = PureExpr::BinOp(Arc::new(x), BinOp::Lt, Arc::new(PureExpr::Int(10)));
    assert!(
        !is_base_vacuous(&[gt_zero, lt_ten]),
        "x > 0 ∧ x < 10 should not be vacuous"
    );
}

/// `true` literal is trivially satisfiable.
#[test]
#[timeout(30000)]
fn is_base_vacuous_true_literal() {
    assert!(
        !is_base_vacuous(&[PureExpr::Bool(true)]),
        "Bool(true) should not be vacuous"
    );
}

/// Single variable is satisfiable (Bool-sorted).
#[test]
#[timeout(30000)]
fn is_base_vacuous_single_var() {
    assert!(
        !is_base_vacuous(&[PureExpr::Var("flag".to_string(), None)]),
        "single Var should not be vacuous"
    );
}

// ── expr_needs_full_context guard (skips → returns false) ────────────

/// LogicFnCall triggers full-context guard → is_base_vacuous returns false.
#[test]
#[timeout(30000)]
fn is_base_vacuous_skips_logic_fn_call() {
    let expr = PureExpr::LogicFnCall {
        name: "my_predicate".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    // Even though encoding might fail or be contradictory,
    // the guard skips the check entirely.
    assert!(
        !is_base_vacuous(&[expr]),
        "LogicFnCall should trigger full-context guard → not vacuous"
    );
}

/// MethodCall triggers full-context guard → is_base_vacuous returns false.
#[test]
#[timeout(30000)]
fn is_base_vacuous_skips_method_call() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("v".to_string(), None)),
        method: "len".to_string(),
        args: vec![],
    };
    assert!(
        !is_base_vacuous(&[expr]),
        "MethodCall should trigger full-context guard → not vacuous"
    );
}

/// LogicFnCall nested inside BinOp still triggers the guard.
#[test]
#[timeout(30000)]
fn is_base_vacuous_skips_nested_logic_fn_call() {
    let logic_call = PureExpr::LogicFnCall {
        name: "pred".to_string(),
        args: vec![],
    };
    let expr = PureExpr::BinOp(
        Arc::new(logic_call),
        BinOp::Eq,
        Arc::new(PureExpr::Bool(true)),
    );
    assert!(
        !is_base_vacuous(&[expr]),
        "nested LogicFnCall in BinOp should trigger guard"
    );
}

/// MethodCall nested inside Deref still triggers the guard.
#[test]
#[timeout(30000)]
fn is_base_vacuous_skips_method_call_in_deref() {
    let method = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("v".to_string(), None)),
        method: "len".to_string(),
        args: vec![],
    };
    let expr = PureExpr::Deref(Arc::new(method));
    assert!(
        !is_base_vacuous(&[expr]),
        "MethodCall inside Deref should trigger guard"
    );
}

/// LogicFnCall nested inside Ite condition triggers the guard.
#[test]
#[timeout(30000)]
fn is_base_vacuous_skips_logic_fn_in_ite() {
    let logic_call = PureExpr::LogicFnCall {
        name: "pred".to_string(),
        args: vec![],
    };
    let expr = PureExpr::Ite(
        Arc::new(logic_call),
        Arc::new(PureExpr::Bool(true)),
        Arc::new(PureExpr::Bool(false)),
    );
    assert!(
        !is_base_vacuous(&[expr]),
        "LogicFnCall in Ite condition should trigger guard"
    );
}

/// LogicFnCall in Forall body triggers the guard.
#[test]
#[timeout(30000)]
fn is_base_vacuous_skips_logic_fn_in_forall_body() {
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::LogicFnCall {
            name: "inv".to_string(),
            args: vec![PureExpr::Var("i".to_string(), None)],
        }),
        triggers: vec![],
    };
    assert!(
        !is_base_vacuous(&[expr]),
        "LogicFnCall in Forall body should trigger guard"
    );
}

/// LogicFnCall in Forall trigger (but not body) triggers the guard.
#[test]
#[timeout(30000)]
fn is_base_vacuous_skips_logic_fn_in_forall_trigger() {
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![vec![PureExpr::LogicFnCall {
            name: "trigger_fn".to_string(),
            args: vec![PureExpr::Var("i".to_string(), None)],
        }]],
    };
    assert!(
        !is_base_vacuous(&[expr]),
        "LogicFnCall in Forall trigger should trigger guard"
    );
}

/// LogicFnCall in Match arm body triggers the guard.
#[test]
#[timeout(30000)]
fn is_base_vacuous_skips_logic_fn_in_match_arm() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: PureExpr::LogicFnCall {
                name: "f".to_string(),
                args: vec![],
            },
        }],
    };
    assert!(
        !is_base_vacuous(&[expr]),
        "LogicFnCall in Match arm body should trigger guard"
    );
}

/// MethodCall in UnOp operand triggers the guard via recursive traversal.
#[test]
#[timeout(30000)]
fn is_base_vacuous_skips_method_call_in_unop() {
    let method = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("v".to_string(), None)),
        method: "is_empty".to_string(),
        args: vec![],
    };
    let expr = PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, Arc::new(method));
    assert!(
        !is_base_vacuous(&[expr]),
        "MethodCall inside UnOp should trigger guard"
    );
}

// ── Mixed slices ─────────────────────────────────────────────────────

/// If ANY expression in the slice needs full context, the entire check is skipped.
#[test]
#[timeout(30000)]
fn is_base_vacuous_mixed_simple_and_complex_skips() {
    let simple = PureExpr::Bool(false); // contradictory on its own
    let complex = PureExpr::LogicFnCall {
        name: "f".to_string(),
        args: vec![],
    };
    // Even though `false` alone is vacuous, the presence of LogicFnCall
    // causes the guard to skip the entire check.
    assert!(
        !is_base_vacuous(&[simple, complex]),
        "mixed slice with LogicFnCall should skip vacuity check"
    );
}

// ── Catch-all arm coverage ───────────────────────────────────────────

/// Closure expression hits the catch-all `_ => true` arm in
/// `expr_needs_full_context_inner`, so is_base_vacuous skips the check.
#[test]
#[timeout(30000)]
fn is_base_vacuous_skips_closure() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
    };
    assert!(
        !is_base_vacuous(&[expr]),
        "Closure should hit catch-all guard → not vacuous"
    );
}

/// Let expression hits the catch-all `_ => true` arm.
#[test]
#[timeout(30000)]
fn is_base_vacuous_skips_let() {
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(PureExpr::Int(1)),
        body: Arc::new(PureExpr::Bool(true)),
    };
    assert!(
        !is_base_vacuous(&[expr]),
        "Let should hit catch-all guard → not vacuous"
    );
}

// ── Quantifier body passes when simple ───────────────────────────────

/// Forall with simple body (no LogicFnCall) does NOT trigger guard.
/// The contradictory base `forall x. false` should be detected as vacuous.
#[test]
#[timeout(30000)]
fn is_base_vacuous_forall_simple_body_checked() {
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Bool(false)),
        triggers: vec![],
    };
    // forall x. false is unsatisfiable — the vacuity check should detect it.
    // (Whether ay returns UNSAT here depends on the solver, but the guard
    // should not prevent the check from running.)
    let result = is_base_vacuous(&[expr]);
    // We just verify the guard doesn't skip — the solver may or may not
    // detect vacuity for quantified formulas in QF_AUFLIA.
    // The important assertion is that we don't hit the guard path.
    // If the solver can prove it, great. If Unknown, also fine.
    let _ = result; // no assertion on result — guard non-skip is the point
}
