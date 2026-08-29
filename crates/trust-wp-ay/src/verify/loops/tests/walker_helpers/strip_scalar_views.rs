// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// ── strip_scalar_views tests ──────────────────────────────────────────

/// `strip_scalar_views` removes View(Var(x)) → Var(x) for scalar variables.
#[test]
#[timeout(30000)]
fn strip_scalar_views_removes_view_of_var() {
    let expr = PureExpr::View(Arc::new(PureExpr::Var("x".to_string(), None)));
    let stripped = strip_scalar_views(&expr);
    assert_eq!(
        stripped,
        PureExpr::Var("x".to_string(), None),
        "View(Var(x)) should simplify to Var(x)"
    );
}

/// `strip_scalar_views` removes View(Deref(Var(x))) → Deref(Var(x)).
#[test]
#[timeout(30000)]
fn strip_scalar_views_removes_view_of_deref() {
    let expr = PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
        "x".to_string(),
        None,
    )))));
    let stripped = strip_scalar_views(&expr);
    assert_eq!(
        stripped,
        PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None))),
        "View(Deref(Var(x))) should simplify to Deref(Var(x))"
    );
}

/// `strip_scalar_views` removes View(Final(Var(x))) → Final(Var(x)).
#[test]
#[timeout(30000)]
fn strip_scalar_views_removes_view_of_final() {
    let expr = PureExpr::View(Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
        "x".to_string(),
        None,
    )))));
    let stripped = strip_scalar_views(&expr);
    assert_eq!(
        stripped,
        PureExpr::Final(Arc::new(PureExpr::Var("x".to_string(), None))),
        "View(Final(Var(x))) should simplify to Final(Var(x))"
    );
}

/// `strip_scalar_views` preserves View of complex expressions (non-scalar).
#[test]
#[timeout(30000)]
fn strip_scalar_views_preserves_view_of_method_call() {
    let method_call = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("v".to_string(), None)),
        method: "len".to_string(),
        args: vec![],
    };
    let expr = PureExpr::View(Arc::new(method_call.clone()));
    let stripped = strip_scalar_views(&expr);
    // View of MethodCall is NOT scalar — should be preserved
    assert!(
        matches!(&stripped, PureExpr::View(inner) if matches!(inner.as_ref(), PureExpr::MethodCall { .. })),
        "View(MethodCall) should be preserved: got {stripped:?}"
    );
}

/// `strip_scalar_views` recurses through BinOp.
#[test]
#[timeout(30000)]
fn strip_scalar_views_recurses_into_binop() {
    // (View(Var(x)) + View(Var(y))) should become (Var(x) + Var(y))
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        BinOp::Add,
        Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "y".to_string(),
            None,
        )))),
    );
    let stripped = strip_scalar_views(&expr);
    assert_eq!(
        stripped,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("y".to_string(), None)),
        ),
        "strip_scalar_views should recurse through BinOp operands"
    );
}

/// `strip_scalar_views` recurses through Ite.
#[test]
#[timeout(30000)]
fn strip_scalar_views_recurses_into_ite() {
    let expr = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "a".to_string(),
            None,
        )))),
        Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "b".to_string(),
            None,
        )))),
    );
    let stripped = strip_scalar_views(&expr);
    assert_eq!(
        stripped,
        PureExpr::Ite(
            Arc::new(PureExpr::Bool(true)),
            Arc::new(PureExpr::Var("a".to_string(), None)),
            Arc::new(PureExpr::Var("b".to_string(), None)),
        ),
        "strip_scalar_views should recurse through Ite branches"
    );
}

// ── UnOp / Old / Deref / Final recursion gaps (#2514) ──

/// `strip_scalar_views` recurses through UnOp.
#[test]
#[timeout(30000)]
fn strip_scalar_views_recurses_into_unop() {
    let expr = PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Not,
        Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "flag".to_string(),
            None,
        )))),
    );
    let stripped = strip_scalar_views(&expr);
    assert_eq!(
        stripped,
        PureExpr::UnOp(
            trust_wp_core::formula::UnOp::Not,
            Arc::new(PureExpr::Var("flag".to_string(), None)),
        ),
        "strip_scalar_views should recurse through UnOp and strip inner View"
    );
}

/// `strip_scalar_views` recurses through Old.
#[test]
#[timeout(30000)]
fn strip_scalar_views_recurses_into_old() {
    let expr = PureExpr::Old(Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
        "x".to_string(),
        None,
    )))));
    let stripped = strip_scalar_views(&expr);
    assert_eq!(
        stripped,
        PureExpr::Old(Arc::new(PureExpr::Var("x".to_string(), None))),
        "strip_scalar_views should recurse through Old and strip inner View"
    );
}

/// `strip_scalar_views` recurses through Deref.
#[test]
#[timeout(30000)]
fn strip_scalar_views_recurses_into_deref() {
    let expr = PureExpr::Deref(Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
        "r".to_string(),
        None,
    )))));
    let stripped = strip_scalar_views(&expr);
    assert_eq!(
        stripped,
        PureExpr::Deref(Arc::new(PureExpr::Var("r".to_string(), None))),
        "strip_scalar_views should recurse through Deref and strip inner View"
    );
}

/// `strip_scalar_views` recurses through Final.
#[test]
#[timeout(30000)]
fn strip_scalar_views_recurses_into_final() {
    let expr = PureExpr::Final(Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
        "r".to_string(),
        None,
    )))));
    let stripped = strip_scalar_views(&expr);
    assert_eq!(
        stripped,
        PureExpr::Final(Arc::new(PureExpr::Var("r".to_string(), None))),
        "strip_scalar_views should recurse through Final and strip inner View"
    );
}

/// `strip_scalar_views` is identity for expressions without View.
#[test]
#[timeout(30000)]
fn strip_scalar_views_identity_on_plain_expr() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let stripped = strip_scalar_views(&expr);
    assert_eq!(
        stripped, expr,
        "Expressions without View should pass through unchanged"
    );
}
