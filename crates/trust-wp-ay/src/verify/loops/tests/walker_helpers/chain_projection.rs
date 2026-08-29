// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// ── expr_has_chain_projection tests ───────────────────────────────────

/// `expr_has_chain_projection` returns true for Deref.
#[test]
#[timeout(30000)]
fn expr_has_chain_projection_deref() {
    let expr = PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None)));
    assert!(
        expr_has_chain_projection(&expr),
        "Deref should be detected as chain projection"
    );
}

/// `expr_has_chain_projection` returns true for Final.
#[test]
#[timeout(30000)]
fn expr_has_chain_projection_final() {
    let expr = PureExpr::Final(Arc::new(PureExpr::Var("x".to_string(), None)));
    assert!(
        expr_has_chain_projection(&expr),
        "Final should be detected as chain projection"
    );
}

/// `expr_has_chain_projection` returns true for View.
#[test]
#[timeout(30000)]
fn expr_has_chain_projection_view() {
    let expr = PureExpr::View(Arc::new(PureExpr::Var("x".to_string(), None)));
    assert!(
        expr_has_chain_projection(&expr),
        "View should be detected as chain projection"
    );
}

/// `expr_has_chain_projection` returns true for Old.
#[test]
#[timeout(30000)]
fn expr_has_chain_projection_old() {
    let expr = PureExpr::Old(Arc::new(PureExpr::Var("x".to_string(), None)));
    assert!(
        expr_has_chain_projection(&expr),
        "Old should be detected as chain projection"
    );
}

/// `expr_has_chain_projection` returns false for plain arithmetic.
#[test]
#[timeout(30000)]
fn expr_has_chain_projection_false_for_arithmetic() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    assert!(
        !expr_has_chain_projection(&expr),
        "Plain arithmetic should not have chain projections"
    );
}

/// `expr_has_chain_projection` returns false for literals.
#[test]
#[timeout(30000)]
fn expr_has_chain_projection_false_for_literals() {
    assert!(!expr_has_chain_projection(&PureExpr::Int(42)));
    assert!(!expr_has_chain_projection(&PureExpr::Bool(true)));
    assert!(!expr_has_chain_projection(&PureExpr::Var(
        "x".to_string(),
        None
    )));
}

/// `expr_has_chain_projection` finds Deref nested in BinOp.
#[test]
#[timeout(30000)]
fn expr_has_chain_projection_nested_in_binop() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    assert!(
        expr_has_chain_projection(&expr),
        "Deref nested in BinOp lhs should be detected"
    );
}

/// `expr_has_chain_projection` finds Final in MethodCall receiver.
#[test]
#[timeout(30000)]
fn expr_has_chain_projection_in_method_call() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "self".to_string(),
            None,
        )))),
        method: "len".to_string(),
        args: vec![],
    };
    assert!(
        expr_has_chain_projection(&expr),
        "Final in MethodCall receiver should be detected"
    );
}

/// `expr_has_chain_projection` finds View in LogicFnCall args.
#[test]
#[timeout(30000)]
fn expr_has_chain_projection_in_logic_fn_call() {
    let expr = PureExpr::LogicFnCall {
        name: "foo".to_string(),
        args: vec![PureExpr::View(Arc::new(PureExpr::Var(
            "v".to_string(),
            None,
        )))],
    };
    assert!(
        expr_has_chain_projection(&expr),
        "View in LogicFnCall args should be detected"
    );
}

/// `expr_has_chain_projection` finds projection in Ite.
#[test]
#[timeout(30000)]
fn expr_has_chain_projection_in_ite() {
    let expr = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(PureExpr::Int(1)),
        Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
    );
    assert!(
        expr_has_chain_projection(&expr),
        "Old in Ite else-branch should be detected"
    );
}

// ── depth-guard polarity tests (Part of #2473) ──────────────────────

/// At depth > MAX_ENCODING_DEPTH, `expr_has_chain_projection` must return
/// `true` (fail-closed) even when the tree contains no projections.
///
/// Rationale: false negatives would skip alias assertions, potentially
/// causing unsound verification of loop invariants involving
/// deref/final/view/old chains.
#[test]
#[timeout(30000)]
#[allow(clippy::cast_possible_wrap)] // test data: small usize values safely fit i64
fn depth_guard_chain_projection_fails_closed() {
    let depth = crate::encoder::MAX_ENCODING_DEPTH + 10;
    // Build a deep BinOp tree with NO projections (just arithmetic).
    let mut expr = PureExpr::Int(0);
    for i in 0..depth {
        expr = PureExpr::BinOp(
            Arc::new(expr),
            BinOp::Add,
            Arc::new(PureExpr::Int(i as i64)),
        );
    }
    assert!(
        expr_has_chain_projection(&expr),
        "expr_has_chain_projection must return true at depth limit (fail-closed); \
         got false for a {depth}-deep tree with no projections"
    );
}

/// Below MAX_ENCODING_DEPTH, a plain arithmetic tree returns false.
#[test]
#[timeout(30000)]
fn depth_guard_chain_projection_normal_false() {
    let mut expr = PureExpr::Int(0);
    for i in 0..10 {
        expr = PureExpr::BinOp(Arc::new(expr), BinOp::Add, Arc::new(PureExpr::Int(i)));
    }
    assert!(
        !expr_has_chain_projection(&expr),
        "expr_has_chain_projection should return false for plain tree below depth limit"
    );
}
