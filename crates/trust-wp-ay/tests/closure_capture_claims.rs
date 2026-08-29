// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use ntest::timeout;
use trust_wp_ay::{
    verify_function_with_modes, verify_mut_borrow_function_with_modes, MutBorrowRequest,
    VerificationRequest, VerificationResult,
};
use trust_wp_core::{
    closure::{CaptureField, CaptureKind},
    formula::{BinOp, ExprSort, PureExpr},
};

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn int(value: i64) -> PureExpr {
    PureExpr::Int(value)
}

fn eq(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
}

fn gt(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(lhs), BinOp::Gt, Arc::new(rhs))
}

fn deref(expr: PureExpr) -> PureExpr {
    PureExpr::Deref(Arc::new(expr))
}

/// Regression check for #1485 on the verification request path.
#[test]
#[timeout(10000)]
fn verify_request_rejects_conflicting_closure_capture_signatures() {
    let captures = vec![
        trust_wp_ay::closure_capture_info! {
            def_id: "test::closure#0".to_string(),
            captures: vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByRef)],
            param_name: Some("c".to_string()),
            body_expr: None,
            param_names: None,
            ensures_exprs: None,
        },
        trust_wp_ay::closure_capture_info! {
            def_id: "test::closure#0".to_string(),
            captures: vec![CaptureField::new("x", ExprSort::Bool, CaptureKind::ByRef)],
            param_name: Some("c".to_string()),
            body_expr: None,
            param_names: None,
            ensures_exprs: None,
        },
    ];

    let ensures = [eq(var("result"), int(0))];
    let request = VerificationRequest::new(&[], &ensures).closure_captures(Some(&captures));
    let result = verify_function_with_modes(request);

    assert!(
        result.is_err(),
        "conflicting closure capture signatures should return Err, got: {result:?}"
    );
    let message = format!(
        "{}",
        result.expect_err("expected capture signature mismatch error")
    );
    assert!(
        message.contains("changed capture signature"),
        "error should mention changed capture signature, got: {message}"
    );
}

/// Regression check for #1485 on the mut-borrow request path.
#[test]
#[timeout(10000)]
fn verify_mut_borrow_request_rejects_conflicting_closure_capture_signatures() {
    let captures = vec![
        trust_wp_ay::closure_capture_info! {
            def_id: "test::closure#0".to_string(),
            captures: vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByRef)],
            param_name: Some("c".to_string()),
            body_expr: None,
            param_names: None,
            ensures_exprs: None,
        },
        trust_wp_ay::closure_capture_info! {
            def_id: "test::closure#0".to_string(),
            captures: vec![CaptureField::new("x", ExprSort::Bool, CaptureKind::ByRef)],
            param_name: Some("c".to_string()),
            body_expr: None,
            param_names: None,
            ensures_exprs: None,
        },
    ];

    let final_values = HashMap::new();
    let request = MutBorrowRequest::new(&[], &[], &final_values).closure_captures(Some(&captures));
    let result = verify_mut_borrow_function_with_modes(request);

    assert!(
        result.is_err(),
        "conflicting closure capture signatures should return Err, got: {result:?}"
    );
    let message = format!(
        "{}",
        result.expect_err("expected capture signature mismatch error")
    );
    assert!(
        message.contains("changed capture signature"),
        "mut-borrow error should mention changed capture signature, got: {message}"
    );
}

/// Regression check for #1543 guard negative path:
/// when no capture `_final` exists, projection should be skipped.
/// Uses a non-tautological postcondition that depends on the precondition
/// to verify the standard requires/ensures path still works.
#[test]
#[timeout(10000)]
fn no_capture_final_skips_projection_without_unsound_success() {
    let closure_captures = vec![trust_wp_ay::closure_capture_info! {
        def_id: "test::no_final_closure#0".to_string(),
        captures: vec![
            CaptureField::new("x", ExprSort::Int, CaptureKind::ByRef),
            CaptureField::new("y", ExprSort::Int, CaptureKind::ByRef),
        ],
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    }];

    let final_values = HashMap::new();
    // Non-tautological: ensures(*x > 0) is only provable given requires(*x > 5).
    let requires = [gt(deref(var("x")), int(5))];
    let ensures = [gt(deref(var("x")), int(0))];
    let request = MutBorrowRequest::new(&requires, &ensures, &final_values)
        .closure_captures(Some(&closure_captures));

    let result = verify_mut_borrow_function_with_modes(request);
    assert!(
        result.is_ok(),
        "no-capture-final guard should skip projection without error: {result:?}"
    );
    let verification = result.unwrap();
    assert!(
        matches!(verification, VerificationResult::Verified(_)),
        "precondition-dependent postcondition should verify when projection is skipped, got: {verification:?}"
    );
}

/// Regression check for #1543 partial binding behavior:
/// at least one `_final` binding should enable projection without encoding error.
#[test]
#[timeout(10000)]
fn partial_capture_binding_verifies_bound_capture_postcondition() {
    let closure_captures = vec![trust_wp_ay::closure_capture_info! {
        def_id: "test::partial_closure#0".to_string(),
        captures: vec![
            CaptureField::new("x", ExprSort::Int, CaptureKind::ByRef),
            CaptureField::new("y", ExprSort::Int, CaptureKind::ByRef),
        ],
        param_name: Some("c".to_string()),
        body_expr: None,
        param_names: None,
        ensures_exprs: None,
    }];

    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));

    let requires = [gt(deref(var("x")), int(0))];
    let ensures = [gt(var("x_final"), int(0))];
    let request = MutBorrowRequest::new(&requires, &ensures, &final_values)
        .closure_captures(Some(&closure_captures));

    let result = verify_mut_borrow_function_with_modes(request);
    assert!(
        result.is_ok(),
        "partial capture binding should not error: {result:?}"
    );
    assert!(
        matches!(result.unwrap(), VerificationResult::Verified(_)),
        "postcondition over bound capture should verify"
    );
}
