// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;
use crate::encoder::quantifier_ctor_elim::{arg_is_qvar_reference, extract_scrutinee_var_name};

// ── arg_is_qvar_reference tests ──────────────────────────────────────

/// Direct Var reference matches the quantifier variable name.
#[test]
#[timeout(30000)]
fn test_arg_is_qvar_reference_direct_var_match() {
    let expr = var("v");
    assert!(arg_is_qvar_reference(&expr, "v"));
}

/// Direct Var reference does NOT match a different variable name.
#[test]
#[timeout(30000)]
fn test_arg_is_qvar_reference_direct_var_mismatch() {
    let expr = var("x");
    assert!(!arg_is_qvar_reference(&expr, "v"));
}

/// Deref(Var) should unwrap through Deref and match the inner variable.
#[test]
#[timeout(30000)]
fn test_arg_is_qvar_reference_through_deref() {
    let expr = deref(var("v"));
    assert!(arg_is_qvar_reference(&expr, "v"));
}

/// Old(Var) should unwrap through Old and match the inner variable.
#[test]
#[timeout(30000)]
fn test_arg_is_qvar_reference_through_old() {
    let expr = old(var("v"));
    assert!(arg_is_qvar_reference(&expr, "v"));
}

/// Final(Var) should unwrap through Final and match the inner variable.
#[test]
#[timeout(30000)]
fn test_arg_is_qvar_reference_through_final() {
    let expr = final_expr(var("v"));
    assert!(arg_is_qvar_reference(&expr, "v"));
}

/// View(Var) should unwrap through View and match the inner variable.
#[test]
#[timeout(30000)]
fn test_arg_is_qvar_reference_through_view() {
    let expr = view(var("v"));
    assert!(arg_is_qvar_reference(&expr, "v"));
}

/// Nested wrappers: Deref(Final(Var)) should recursively unwrap and match.
#[test]
#[timeout(30000)]
fn test_arg_is_qvar_reference_nested_wrappers() {
    let expr = deref(final_expr(var("v")));
    assert!(arg_is_qvar_reference(&expr, "v"));
}

/// Non-variable expressions (Int, BinOp, etc.) should never match.
#[test]
#[timeout(30000)]
fn test_arg_is_qvar_reference_non_var_returns_false() {
    assert!(!arg_is_qvar_reference(&int(42), "v"));
    assert!(!arg_is_qvar_reference(&bool_expr(true), "v"));
    assert!(!arg_is_qvar_reference(&add(var("v"), int(1)), "v"));
}

/// MethodCall expressions are not unwrapped — should return false.
#[test]
#[timeout(30000)]
fn test_arg_is_qvar_reference_method_call_returns_false() {
    let expr = method_call(var("v"), "len", vec![]);
    assert!(!arg_is_qvar_reference(&expr, "v"));
}

// ── extract_scrutinee_var_name tests ─────────────────────────────────

/// Direct Var("x") extracts the variable name "x".
#[test]
#[timeout(30000)]
fn test_extract_scrutinee_var_name_direct_var() {
    let expr = var("x");
    assert_eq!(extract_scrutinee_var_name(&expr), Some("x"));
}

/// Deref(Var("self")) extracts "self" through the Deref wrapper.
#[test]
#[timeout(30000)]
fn test_extract_scrutinee_var_name_through_deref() {
    let expr = deref(var("self"));
    assert_eq!(extract_scrutinee_var_name(&expr), Some("self"));
}

/// Old(Var("x")) extracts "x" through Old wrapper.
#[test]
#[timeout(30000)]
fn test_extract_scrutinee_var_name_through_old() {
    let expr = old(var("x"));
    assert_eq!(extract_scrutinee_var_name(&expr), Some("x"));
}

/// Final(Var("x")) extracts "x" through Final wrapper.
#[test]
#[timeout(30000)]
fn test_extract_scrutinee_var_name_through_final() {
    let expr = final_expr(var("x"));
    assert_eq!(extract_scrutinee_var_name(&expr), Some("x"));
}

/// View(Var("x")) extracts "x" through View wrapper.
#[test]
#[timeout(30000)]
fn test_extract_scrutinee_var_name_through_view() {
    let expr = view(var("x"));
    assert_eq!(extract_scrutinee_var_name(&expr), Some("x"));
}

/// Nested wrappers: Deref(Old(Var("x"))) extracts "x" through multiple layers.
#[test]
#[timeout(30000)]
fn test_extract_scrutinee_var_name_nested_wrappers() {
    let expr = deref(old(var("x")));
    assert_eq!(extract_scrutinee_var_name(&expr), Some("x"));
}

/// Non-variable expression (Int, BinOp) returns None.
#[test]
#[timeout(30000)]
fn test_extract_scrutinee_var_name_non_var_returns_none() {
    assert_eq!(extract_scrutinee_var_name(&int(42)), None);
    assert_eq!(extract_scrutinee_var_name(&add(var("x"), int(1))), None);
}

/// MethodCall is not a simple variable reference — returns None.
#[test]
#[timeout(30000)]
fn test_extract_scrutinee_var_name_method_call_returns_none() {
    let expr = method_call(var("x"), "len", vec![]);
    assert_eq!(extract_scrutinee_var_name(&expr), None);
}
