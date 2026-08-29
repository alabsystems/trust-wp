// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
// --- strip_receiver_state_wrappers / strip_deref_wrappers / final_receiver_state_expr tests ---
use super::{final_receiver_state_expr, strip_deref_wrappers, strip_receiver_state_wrappers};

/// `strip_receiver_state_wrappers` removes Deref and Final wrappers.
#[test]
fn test_strip_receiver_state_wrappers_deref() {
    let inner = PureExpr::Var("x".to_string(), None);
    let expr = PureExpr::Deref(Arc::new(inner.clone()));
    assert_eq!(strip_receiver_state_wrappers(&expr), inner);
}

#[test]
fn test_strip_receiver_state_wrappers_final() {
    let inner = PureExpr::Var("x".to_string(), None);
    let expr = PureExpr::Final(Arc::new(inner.clone()));
    assert_eq!(strip_receiver_state_wrappers(&expr), inner);
}

#[test]
fn test_strip_receiver_state_wrappers_nested_deref_final() {
    let inner = PureExpr::Var("x".to_string(), None);
    let expr = PureExpr::Deref(Arc::new(PureExpr::Final(Arc::new(inner.clone()))));
    assert_eq!(strip_receiver_state_wrappers(&expr), inner);
}

#[test]
fn test_strip_receiver_state_wrappers_non_wrapper_passes_through() {
    let expr = PureExpr::Int(42);
    assert_eq!(strip_receiver_state_wrappers(&expr), PureExpr::Int(42));
}

/// View is NOT stripped by strip_receiver_state_wrappers (only Deref/Final).
#[test]
fn test_strip_receiver_state_wrappers_view_not_stripped() {
    let inner = PureExpr::Var("x".to_string(), None);
    let expr = PureExpr::View(Arc::new(inner));
    assert_eq!(strip_receiver_state_wrappers(&expr), expr);
}

/// `strip_deref_wrappers` removes only Deref wrappers.
#[test]
fn test_strip_deref_wrappers_deref() {
    let inner = PureExpr::Var("x".to_string(), None);
    let expr = PureExpr::Deref(Arc::new(inner.clone()));
    assert_eq!(strip_deref_wrappers(&expr), inner);
}

#[test]
fn test_strip_deref_wrappers_nested_deref() {
    let inner = PureExpr::Var("x".to_string(), None);
    let expr = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(inner.clone()))));
    assert_eq!(strip_deref_wrappers(&expr), inner);
}

/// Final is NOT stripped by strip_deref_wrappers.
#[test]
fn test_strip_deref_wrappers_final_not_stripped() {
    let inner = PureExpr::Var("x".to_string(), None);
    let expr = PureExpr::Final(Arc::new(inner));
    assert_eq!(strip_deref_wrappers(&expr), expr);
}

/// `final_receiver_state_expr` wraps base in Final for non-tuple expressions.
#[test]
fn test_final_receiver_state_expr_non_tuple() {
    let expr = PureExpr::Deref(Arc::new(PureExpr::Var("self".to_string(), None)));
    let result = final_receiver_state_expr(&expr);
    assert_eq!(
        result,
        PureExpr::Final(Arc::new(PureExpr::Var("self".to_string(), None)))
    );
}

/// For a tuple constructor, `final_receiver_state_expr` wraps each arg in Final.
#[test]
fn test_final_receiver_state_expr_tuple_wraps_each_arg() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name;
    let tuple_name = tuple_logic_fn_name(2);
    let expr = PureExpr::LogicFnCall {
        name: tuple_name.clone(),
        args: vec![
            PureExpr::Var("a".to_string(), None),
            PureExpr::Var("b".to_string(), None),
        ],
    };
    let result = final_receiver_state_expr(&expr);
    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: tuple_name,
            args: vec![
                PureExpr::Final(Arc::new(PureExpr::Var("a".to_string(), None))),
                PureExpr::Final(Arc::new(PureExpr::Var("b".to_string(), None))),
            ],
        }
    );
}

// =============================================================================
// expr_contains_old tests
// =============================================================================

#[test]
fn test_expr_contains_old_true() {
    let expr = PureExpr::Old(Arc::new(PureExpr::Var("x".to_string(), None)));
    assert!(expr_contains_old(&expr));
}

#[test]
fn test_expr_contains_old_nested() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    assert!(expr_contains_old(&expr));
}

#[test]
fn test_expr_contains_old_false_no_old() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    assert!(!expr_contains_old(&expr));
}

#[test]
fn test_expr_contains_old_false_simple_var() {
    let expr = PureExpr::Var("x".to_string(), None);
    assert!(!expr_contains_old(&expr));
}

#[test]
fn test_expr_contains_old_in_method_call_receiver() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
            "v".to_string(),
            Some(ExprSort::Seq),
        )))),
        method: "len".to_string(),
        args: vec![],
    };
    assert!(expr_contains_old(&expr));
}
