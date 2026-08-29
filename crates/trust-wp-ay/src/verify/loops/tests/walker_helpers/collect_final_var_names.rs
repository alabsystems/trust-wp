// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// ── collect_final_var_names tests ─────────────────────────────────────

/// `collect_final_var_names` finds Final(Var(x)) and returns {"x"}.
#[test]
#[timeout(30000)]
fn collect_final_var_names_basic_final_var() {
    let expr = PureExpr::Final(Arc::new(PureExpr::Var("x".to_string(), None)));
    let names = collect_final_var_names(&[expr]);
    assert!(
        names.contains("x"),
        "should collect 'x' from Final(Var(x)): got {names:?}"
    );
    assert_eq!(names.len(), 1, "should collect exactly one name");
}

/// `collect_final_var_names` returns empty set for expressions without Final.
#[test]
#[timeout(30000)]
fn collect_final_var_names_empty_on_no_final() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let names = collect_final_var_names(&[expr]);
    assert!(
        names.is_empty(),
        "no Final nodes means empty set: got {names:?}"
    );
}

/// `collect_final_var_names` finds multiple Final vars across expressions.
#[test]
#[timeout(30000)]
fn collect_final_var_names_multiple_exprs() {
    let e1 = PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "a".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "b".to_string(),
            None,
        )))),
    );
    let e2 = PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None)));
    let names = collect_final_var_names(&[e1, e2]);
    assert_eq!(
        names.len(),
        3,
        "should find 3 distinct final vars: got {names:?}"
    );
    assert!(names.contains("a"));
    assert!(names.contains("b"));
    assert!(names.contains("c"));
}

/// `collect_final_var_names` finds Final(Var) nested inside Ite.
#[test]
#[timeout(30000)]
fn collect_final_var_names_in_ite() {
    let expr = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        Arc::new(PureExpr::Int(0)),
    );
    let names = collect_final_var_names(&[expr]);
    assert!(
        names.contains("x"),
        "should find Final(Var(x)) inside Ite then-branch"
    );
}

/// `collect_final_var_names` does NOT collect Var without Final wrapper.
#[test]
#[timeout(30000)]
fn collect_final_var_names_ignores_bare_var() {
    let expr = PureExpr::Var("x".to_string(), None);
    let names = collect_final_var_names(&[expr]);
    assert!(
        names.is_empty(),
        "bare Var should not be collected: got {names:?}"
    );
}

// ── UnOp / MethodCall / LetAssume / LetObligation gaps (#2514) ──

/// `collect_final_var_names` finds Final(Var) nested inside UnOp.
#[test]
#[timeout(30000)]
fn collect_final_var_names_in_unop() {
    let expr = PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )),
    );
    let names = collect_final_var_names(&[expr]);
    assert!(
        names.contains("x"),
        "should find Final(Var(x)) inside UnOp: got {names:?}"
    );
}

/// `collect_final_var_names` finds Final(Var) in MethodCall receiver.
#[test]
#[timeout(30000)]
fn collect_final_var_names_in_method_call_receiver() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "v".to_string(),
            None,
        )))),
        method: "len".to_string(),
        args: vec![],
    };
    let names = collect_final_var_names(&[expr]);
    assert!(
        names.contains("v"),
        "should find Final(Var(v)) in MethodCall receiver: got {names:?}"
    );
}

/// `collect_final_var_names` finds Final(Var) in LetAssume body.
#[test]
#[timeout(30000)]
fn collect_final_var_names_in_let_assume() {
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::Bool(true)),
        body: Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
    };
    let names = collect_final_var_names(&[expr]);
    assert!(
        names.contains("x"),
        "should find Final(Var(x)) in LetAssume body: got {names:?}"
    );
}

/// `collect_final_var_names` finds Final(Var) in LetObligation obligation.
#[test]
#[timeout(30000)]
fn collect_final_var_names_in_let_obligation() {
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        body: Arc::new(PureExpr::Int(0)),
    };
    let names = collect_final_var_names(&[expr]);
    assert!(
        names.contains("x"),
        "should find Final(Var(x)) in LetObligation obligation: got {names:?}"
    );
}

/// `collect_final_var_names` handles Final(Deref(Var(x))) — recurses past Final.
#[test]
#[timeout(30000)]
fn collect_final_var_names_final_deref_var() {
    // Final(Deref(Var("x"))): the immediate child of Final is Deref, not Var,
    // so "x" is NOT collected by the `PureExpr::Var` match inside `PureExpr::Final`.
    let expr = PureExpr::Final(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
        "x".to_string(),
        None,
    )))));
    let names = collect_final_var_names(&[expr]);
    assert!(
        names.is_empty(),
        "Final(Deref(Var(x))): Var is not direct child of Final: got {names:?}"
    );
}
