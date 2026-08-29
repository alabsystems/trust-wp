// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// =============================================================================
// Proof coverage: infer_expr_sort — MethodCall Bool predicates
// Prover proof_coverage phase: these method names in sort_inference.rs L80-98
// were only partially tested (invariant + produces). This covers the rest.
// =============================================================================

/// MethodCall "precondition" returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_precondition_returns_bool() {
    let expr = method_call(var("f"), "precondition", vec![var("x")]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "precondition should return Bool"
    );
}

/// MethodCall "postcondition" returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_postcondition_returns_bool() {
    let expr = method_call(var("f"), "postcondition", vec![var("x"), var("y")]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "postcondition should return Bool"
    );
}

/// MethodCall "postcondition_once" returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_postcondition_once_returns_bool() {
    let expr = method_call(var("f"), "postcondition_once", vec![var("x"), var("y")]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "postcondition_once should return Bool"
    );
}

/// MethodCall "postcondition_mut" returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_postcondition_mut_returns_bool() {
    let expr = method_call(var("f"), "postcondition_mut", vec![var("x"), var("y")]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "postcondition_mut should return Bool"
    );
}

/// MethodCall "is_some" returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_is_some_returns_bool() {
    let expr = method_call(var("opt"), "is_some", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "is_some should return Bool"
    );
}

/// MethodCall "is_none" returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_is_none_returns_bool() {
    let expr = method_call(var("opt"), "is_none", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "is_none should return Bool"
    );
}

/// MethodCall "is_ok" returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_is_ok_returns_bool() {
    let expr = method_call(var("res"), "is_ok", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "is_ok should return Bool"
    );
}

/// MethodCall "is_err" returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_is_err_returns_bool() {
    let expr = method_call(var("res"), "is_err", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "is_err should return Bool"
    );
}

/// MethodCall "contains" returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_contains_returns_bool() {
    let expr = method_call(view(var("v")), "contains", vec![int(42)]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "contains should return Bool"
    );
}

/// MethodCall "completed" returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_completed_returns_bool() {
    let expr = method_call(var("iter"), "completed", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "completed should return Bool"
    );
}

/// MethodCall "ext_eq" returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_ext_eq_returns_bool() {
    let expr = method_call(view(var("v")), "ext_eq", vec![view(var("w"))]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "ext_eq should return Bool"
    );
}

/// MethodCall "public" stays on the value-accessor fallback lane.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_public_returns_int_value_fallback() {
    let expr = method_call(var("x"), "public", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "public should stay on the value-accessor fallback lane"
    );
}

/// MethodCall "is_empty" returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_is_empty_returns_bool() {
    let expr = method_call(view(var("v")), "is_empty", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "is_empty should return Bool"
    );
}

/// MethodCall with unrecognized name defaults to Sort::Int (catch-all).
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_unknown_returns_int() {
    let expr = method_call(var("x"), "custom_method", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Unrecognized method should fall to Int via catch-all"
    );
}

/// MethodCall "reverse" returns Seq (reverse is in method_produces_seq).
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_reverse_returns_seq() {
    let expr = method_call(view(var("v")), "reverse", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::seq(Sort::Int),
        "reverse should return Seq"
    );
}

/// MethodCall "tail" returns Seq.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_tail_returns_seq() {
    let expr = method_call(view(var("v")), "tail", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::seq(Sort::Int),
        "tail should return Seq"
    );
}

/// MethodCall "to_owned_seq" returns Seq.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_to_owned_seq_returns_seq() {
    let expr = method_call(view(var("v")), "to_owned_seq", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::seq(Sort::Int),
        "to_owned_seq should return Seq"
    );
}

/// `Snapshot<T>` is a ghost wrapper — at the logical level it represents the
/// inner value. ExprSort::Datatype("creusot_std::Snapshot") should map to Int
/// (not Uninterpreted) so it can participate in equalities with Int-sorted
/// terms without sort mismatches. (#2075)
#[test]
#[timeout(30000)]
fn infer_expr_sort_snapshot_datatype_maps_to_int() {
    use trust_wp_core::formula::intern_sort_name;
    let id = intern_sort_name("creusot_std::Snapshot");
    let expr = PureExpr::Var("snap_x".to_string(), Some(ExprSort::Datatype(id)));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Snapshot<T> should map to Int, not Uninterpreted (#2075)"
    );
}

/// Verify that bare `Snapshot` (without module path) also maps to Int.
#[test]
#[timeout(30000)]
fn infer_expr_sort_snapshot_short_name_maps_to_int() {
    use trust_wp_core::formula::intern_sort_name;
    let id = intern_sort_name("Snapshot");
    let expr = PureExpr::Var("snap_y".to_string(), Some(ExprSort::Datatype(id)));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Snapshot (short name) should also map to Int (#2075)"
    );
}

/// Legacy bare Snapshot datatype annotations still map to Int. (#2075)
///
/// The driver now preserves `Snapshot<bool>` as `ExprSort::Bool`, but
/// `expr_sort_to_ay_sort` intentionally keeps the compatibility behavior for a
/// manually-constructed bare `ExprSort::Datatype("creusot_std::Snapshot")`
/// annotation with no inner-sort information.
#[test]
#[timeout(30000)]
fn infer_expr_sort_snapshot_legacy_datatype_maps_to_int() {
    use trust_wp_core::formula::intern_sort_name;
    let id = intern_sort_name("creusot_std::Snapshot");
    let expr = PureExpr::Var("snap_flag".to_string(), Some(ExprSort::Datatype(id)));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "bare Snapshot datatype annotations should remain Int-compatible without inner-sort data"
    );
}
