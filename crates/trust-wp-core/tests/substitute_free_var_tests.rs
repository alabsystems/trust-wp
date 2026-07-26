// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for `expr_has_free_occurrence` and `rename_free_var`.
//!
//! Coverage gap: `substitute.rs` (1137 LOC) has zero `#[cfg(test)]` blocks.
//! These two pub functions are used by capture-avoiding substitution but had
//! no direct correctness tests verifying binding-aware free variable detection
//! and alpha-renaming.

use std::sync::Arc;

use trust_wp_core::formula::{
    expr_has_free_occurrence, rename_free_var, BinOp, CaptureAvoidingSubstOptions, MatchArm,
    Pattern, PureExpr,
};

fn opts() -> CaptureAvoidingSubstOptions {
    CaptureAvoidingSubstOptions { depth_limit: None }
}

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn int(v: i64) -> PureExpr {
    PureExpr::Int(v)
}

fn binop(l: PureExpr, op: BinOp, r: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(l), op, Arc::new(r))
}

fn forall(v: &str, body: PureExpr) -> PureExpr {
    PureExpr::Forall {
        var: v.to_string(),
        var_sort: None,
        body: Arc::new(body),
        triggers: vec![],
    }
}

fn exists(v: &str, body: PureExpr) -> PureExpr {
    PureExpr::Exists {
        var: v.to_string(),
        var_sort: None,
        body: Arc::new(body),
        triggers: vec![],
    }
}

fn let_expr(v: &str, value: PureExpr, body: PureExpr) -> PureExpr {
    PureExpr::Let {
        var: v.to_string(),
        value: Arc::new(value),
        body: Arc::new(body),
    }
}

fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

// === expr_has_free_occurrence ===

#[test]
fn free_occurrence_simple_var() {
    assert!(expr_has_free_occurrence(&var("x"), "x", &opts()));
}

#[test]
fn free_occurrence_absent_var() {
    assert!(!expr_has_free_occurrence(&var("y"), "x", &opts()));
}

#[test]
fn free_occurrence_literal_false() {
    assert!(!expr_has_free_occurrence(&int(42), "x", &opts()));
    assert!(!expr_has_free_occurrence(
        &PureExpr::Bool(true),
        "x",
        &opts()
    ));
}

#[test]
fn free_occurrence_in_binop() {
    let expr = binop(var("x"), BinOp::Add, int(1));
    assert!(expr_has_free_occurrence(&expr, "x", &opts()));
    assert!(!expr_has_free_occurrence(&expr, "y", &opts()));
}

#[test]
fn free_occurrence_in_binop_right() {
    let expr = binop(int(1), BinOp::Eq, var("x"));
    assert!(expr_has_free_occurrence(&expr, "x", &opts()));
}

#[test]
fn free_occurrence_shadowed_by_forall() {
    let expr = forall("x", var("x"));
    assert!(!expr_has_free_occurrence(&expr, "x", &opts()));
}

#[test]
fn free_occurrence_not_shadowed_by_different_forall() {
    let expr = forall("y", var("x"));
    assert!(expr_has_free_occurrence(&expr, "x", &opts()));
}

#[test]
fn free_occurrence_shadowed_by_exists() {
    let expr = exists("x", binop(var("x"), BinOp::Gt, int(0)));
    assert!(!expr_has_free_occurrence(&expr, "x", &opts()));
}

#[test]
fn free_occurrence_shadowed_by_let_body() {
    // let x = 1 in x — x is not free in body
    let expr = let_expr("x", int(1), var("x"));
    assert!(!expr_has_free_occurrence(&expr, "x", &opts()));
}

#[test]
fn free_occurrence_free_in_let_value() {
    // let y = x in y — x is free in value
    let expr = let_expr("y", var("x"), var("y"));
    assert!(expr_has_free_occurrence(&expr, "x", &opts()));
}

#[test]
fn free_occurrence_in_ite() {
    let expr = PureExpr::Ite(Arc::new(var("c")), Arc::new(var("x")), Arc::new(int(0)));
    assert!(expr_has_free_occurrence(&expr, "x", &opts()));
    assert!(expr_has_free_occurrence(&expr, "c", &opts()));
    assert!(!expr_has_free_occurrence(&expr, "y", &opts()));
}

#[test]
fn free_occurrence_in_method_call() {
    let expr = method_call(var("self"), "len", vec![var("x")]);
    assert!(expr_has_free_occurrence(&expr, "self", &opts()));
    assert!(expr_has_free_occurrence(&expr, "x", &opts()));
    assert!(!expr_has_free_occurrence(&expr, "y", &opts()));
}

#[test]
fn free_occurrence_in_logic_fn_call() {
    let expr = PureExpr::LogicFnCall {
        name: "my_fn".to_string(),
        args: vec![var("a"), var("b")],
    };
    assert!(expr_has_free_occurrence(&expr, "a", &opts()));
    assert!(expr_has_free_occurrence(&expr, "b", &opts()));
    assert!(!expr_has_free_occurrence(&expr, "c", &opts()));
}

#[test]
fn free_occurrence_through_view() {
    let expr = PureExpr::View(Arc::new(var("x")));
    assert!(expr_has_free_occurrence(&expr, "x", &opts()));
}

#[test]
fn free_occurrence_through_deref() {
    let expr = PureExpr::Deref(Arc::new(var("x")));
    assert!(expr_has_free_occurrence(&expr, "x", &opts()));
}

#[test]
fn free_occurrence_through_final() {
    let expr = PureExpr::Final(Arc::new(var("x")));
    assert!(expr_has_free_occurrence(&expr, "x", &opts()));
}

#[test]
fn free_occurrence_through_old() {
    let expr = PureExpr::Old(Arc::new(var("x")));
    assert!(expr_has_free_occurrence(&expr, "x", &opts()));
}

#[test]
fn free_occurrence_shadowed_by_match_pattern() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(var("opt")),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: "Some".to_string(),
                inner: Some(Box::new(Pattern::Binding("x".to_string()))),
            },
            body: var("x"),
        }],
    };
    // x is bound by the match arm pattern
    assert!(!expr_has_free_occurrence(&expr, "x", &opts()));
    // opt is free in the scrutinee
    assert!(expr_has_free_occurrence(&expr, "opt", &opts()));
}

#[test]
fn free_occurrence_depth_limit_returns_true() {
    let opts = CaptureAvoidingSubstOptions {
        depth_limit: Some(0),
    };
    // With depth_limit=0, even a simple nested expression should conservatively return true
    let expr = binop(var("y"), BinOp::Add, int(1));
    assert!(expr_has_free_occurrence(&expr, "x", &opts));
}

#[test]
fn free_occurrence_closure_shadows_param() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(var("x")),
    };
    assert!(!expr_has_free_occurrence(&expr, "x", &opts()));
}

#[test]
fn free_occurrence_closure_free_non_param() {
    let expr = PureExpr::Closure {
        params: vec![("y".to_string(), None)],
        body: Arc::new(binop(var("y"), BinOp::Add, var("x"))),
    };
    assert!(expr_has_free_occurrence(&expr, "x", &opts()));
    assert!(!expr_has_free_occurrence(&expr, "y", &opts()));
}

// === rename_free_var ===

#[test]
fn rename_simple_var() {
    let result = rename_free_var(&var("x"), "x", "y", &opts());
    assert_eq!(result, var("y"));
}

#[test]
fn rename_unaffected_var() {
    let result = rename_free_var(&var("z"), "x", "y", &opts());
    assert_eq!(result, var("z"));
}

#[test]
fn rename_literal_unchanged() {
    assert_eq!(rename_free_var(&int(42), "x", "y", &opts()), int(42));
}

#[test]
fn rename_in_binop() {
    let expr = binop(var("x"), BinOp::Add, var("x"));
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, binop(var("y"), BinOp::Add, var("y")));
}

#[test]
fn rename_respects_forall_shadow() {
    // forall x. x — x is bound, should NOT be renamed
    let expr = forall("x", var("x"));
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, forall("x", var("x")));
}

#[test]
fn rename_through_forall_non_shadow() {
    // forall z. x — x is free
    let expr = forall("z", var("x"));
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, forall("z", var("y")));
}

#[test]
fn rename_respects_exists_shadow() {
    let expr = exists("x", var("x"));
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, exists("x", var("x")));
}

#[test]
fn rename_respects_let_shadow() {
    // let x = 1 in x — body x is bound
    let expr = let_expr("x", int(1), var("x"));
    let result = rename_free_var(&expr, "x", "y", &opts());
    // x in the value position is free (but it's 1 here), body x is bound
    assert_eq!(result, let_expr("x", int(1), var("x")));
}

#[test]
fn rename_in_let_value() {
    // let y = x in y — x is free in value
    let expr = let_expr("y", var("x"), var("y"));
    let result = rename_free_var(&expr, "x", "z", &opts());
    assert_eq!(result, let_expr("y", var("z"), var("y")));
}

#[test]
fn rename_in_ite() {
    let expr = PureExpr::Ite(Arc::new(var("x")), Arc::new(var("x")), Arc::new(int(0)));
    let result = rename_free_var(&expr, "x", "y", &opts());
    let expected = PureExpr::Ite(Arc::new(var("y")), Arc::new(var("y")), Arc::new(int(0)));
    assert_eq!(result, expected);
}

#[test]
fn rename_in_method_call() {
    let expr = method_call(var("x"), "len", vec![]);
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, method_call(var("y"), "len", vec![]));
}

#[test]
fn rename_in_method_call_args() {
    let expr = method_call(var("self"), "push", vec![var("x")]);
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, method_call(var("self"), "push", vec![var("y")]));
}

#[test]
fn rename_through_view() {
    let expr = PureExpr::View(Arc::new(var("x")));
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, PureExpr::View(Arc::new(var("y"))));
}

#[test]
fn rename_through_final() {
    let expr = PureExpr::Final(Arc::new(var("x")));
    let result = rename_free_var(&expr, "x", "y", &opts());
    assert_eq!(result, PureExpr::Final(Arc::new(var("y"))));
}

#[test]
fn rename_in_logic_fn_call() {
    let expr = PureExpr::LogicFnCall {
        name: "f".to_string(),
        args: vec![var("x"), int(1)],
    };
    let result = rename_free_var(&expr, "x", "y", &opts());
    let expected = PureExpr::LogicFnCall {
        name: "f".to_string(),
        args: vec![var("y"), int(1)],
    };
    assert_eq!(result, expected);
}

#[test]
fn rename_depth_limit_stops_recursion() {
    let opts = CaptureAvoidingSubstOptions {
        depth_limit: Some(0),
    };
    // With depth_limit=0, the expression is returned unchanged
    let expr = binop(var("x"), BinOp::Add, int(1));
    let result = rename_free_var(&expr, "x", "y", &opts);
    assert_eq!(result, expr);
}
