// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::callbacks::contract_rewrite::receiver_root_var_name as extract_receiver_root_var_name;

// --- receiver_root_var_name tests ---

/// Direct Var returns the name.
#[test]
fn receiver_root_var_name_direct_var() {
    let expr = PureExpr::Var("self".to_string(), None);
    assert_eq!(extract_receiver_root_var_name(&expr), Some("self"));
}

/// Old(Var) strips through to the root.
#[test]
fn receiver_root_var_name_old_wrapper() {
    let expr = PureExpr::Old(Arc::new(PureExpr::Var("x".to_string(), None)));
    assert_eq!(extract_receiver_root_var_name(&expr), Some("x"));
}

/// Deref(Var) strips through to the root.
#[test]
fn receiver_root_var_name_deref_wrapper() {
    let expr = PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None)));
    assert_eq!(extract_receiver_root_var_name(&expr), Some("x"));
}

/// View(Var) strips through to the root.
#[test]
fn receiver_root_var_name_view_wrapper() {
    let expr = PureExpr::View(Arc::new(PureExpr::Var("x".to_string(), None)));
    assert_eq!(extract_receiver_root_var_name(&expr), Some("x"));
}

/// Final(Var) strips through to the root.
#[test]
fn receiver_root_var_name_final_wrapper() {
    let expr = PureExpr::Final(Arc::new(PureExpr::Var("x".to_string(), None)));
    assert_eq!(extract_receiver_root_var_name(&expr), Some("x"));
}

/// Nested wrappers: View(Deref(Old(Var("self")))) → "self".
#[test]
fn receiver_root_var_name_nested_wrappers() {
    let expr = PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Old(
        Arc::new(PureExpr::Var("self".to_string(), None)),
    )))));
    assert_eq!(extract_receiver_root_var_name(&expr), Some("self"));
}

/// Non-Var base (e.g., Int literal) returns None.
#[test]
fn receiver_root_var_name_non_var_returns_none() {
    let expr = PureExpr::Int(42);
    assert_eq!(extract_receiver_root_var_name(&expr), None);
}

/// LogicFnCall is not a Var — returns None.
#[test]
fn receiver_root_var_name_logic_fn_call_returns_none() {
    let expr = PureExpr::LogicFnCall {
        name: "f".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    assert_eq!(extract_receiver_root_var_name(&expr), None);
}

/// BinOp is not a Var — returns None.
#[test]
fn receiver_root_var_name_binop_returns_none() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    assert_eq!(extract_receiver_root_var_name(&expr), None);
}

/// Deref(non-Var) returns None — wrapper doesn't find a Var underneath.
#[test]
fn receiver_root_var_name_deref_of_non_var_returns_none() {
    let expr = PureExpr::Deref(Arc::new(PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    )));
    assert_eq!(extract_receiver_root_var_name(&expr), None);
}
