// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;

use super::*;

// =============================================================================
// Proof coverage: infer_expr_sort — MethodCall Seq-producing
// =============================================================================

/// MethodCall with unconditional Seq-producing method returns Seq.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_call_push_back_returns_seq() {
    let expr = method_call(view(var("v")), "push_back", vec![int(42)]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::seq(Sort::Int),
        "push_back should return Seq"
    );
}

/// MethodCall with "concat" returns Seq.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_call_concat_returns_seq() {
    let expr = method_call(view(var("v")), "concat", vec![view(var("w"))]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::seq(Sort::Int),
        "concat should return Seq"
    );
}

/// MethodCall with "subsequence" returns Seq.
#[test]
#[timeout(30000)]
fn infer_expr_sort_method_call_subsequence_returns_seq() {
    let expr = method_call(view(var("v")), "subsequence", vec![int(0), int(5)]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::seq(Sort::Int),
        "subsequence should return Seq"
    );
}

// =============================================================================
// Proof coverage: infer_expr_sort — LogicFnCall special cases
// =============================================================================

/// LogicFnCall "resolve" returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_logic_fn_call_resolve_returns_bool() {
    let expr = logic_fn_call("resolve", vec![var("x")]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "LogicFnCall 'resolve' should return Bool"
    );
}

/// LogicFnCall "seq" returns Seq sort.
#[test]
#[timeout(30000)]
fn infer_expr_sort_logic_fn_call_seq_returns_seq() {
    let expr = logic_fn_call("seq", vec![int(1), int(2), int(3)]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::seq(Sort::Int),
        "LogicFnCall 'seq' should return Seq"
    );
}

/// LogicFnCall "seq_empty" returns Seq sort.
#[test]
#[timeout(30000)]
fn infer_expr_sort_logic_fn_call_seq_empty_returns_seq() {
    let expr = logic_fn_call("seq_empty", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::seq(Sort::Int),
        "LogicFnCall 'seq_empty' should return Seq"
    );
}

/// LogicFnCall "Seq::empty" returns Seq sort.
#[test]
#[timeout(30000)]
fn infer_expr_sort_logic_fn_call_seq_colon_empty_returns_seq() {
    let expr = logic_fn_call("Seq::empty", vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::seq(Sort::Int),
        "LogicFnCall 'Seq::empty' should return Seq"
    );
}

/// LogicFnCall with unrecognized name returns Sort::Int (default).
#[test]
#[timeout(30000)]
fn infer_expr_sort_logic_fn_call_unknown_returns_int() {
    let expr = logic_fn_call("my_custom_fn", vec![var("x")]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Unrecognized LogicFnCall should return Int"
    );
}

/// Tuple constructors carry a structural TupleN carrier sort, not the generic Int fallback.
#[test]
#[timeout(30000)]
fn infer_expr_sort_logic_fn_call_tuple_constructor_returns_tuple_sort() {
    let expr = logic_fn_call(
        &trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(2),
        vec![var("x"), var("y")],
    );
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Uninterpreted("Tuple2".to_string()),
        "tuple constructor should infer its TupleN carrier sort"
    );
}

// =============================================================================
// Proof coverage: infer_expr_sort — Old/Deref/Final recursion
// =============================================================================

/// Old(View(Var)) recurses through both wrappers — returns Int for unannotated Var. (#2057)
#[test]
#[timeout(30000)]
fn infer_expr_sort_old_of_view_returns_inner_sort() {
    // Old(View(unannotated Var)) → Int (View recurses, not Seq)
    let expr = old(view(var("v")));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Old(View(unannotated Var)) should return Int (#2057)"
    );
    // Old(View(Seq-producing method)) → Seq
    let expr_seq = old(view(method_call(var("v"), "push_back", vec![int(1)])));
    assert_eq!(
        infer_expr_sort(&expr_seq),
        Sort::seq(Sort::Int),
        "Old(View(Seq-producing method)) should return Seq"
    );
}

/// Deref of an Int expression returns Int.
#[test]
#[timeout(30000)]
fn infer_expr_sort_deref_of_int_returns_int() {
    let expr = deref(var("x"));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Deref of un-annotated var should return Int"
    );
}

/// Final of a Bool comparison returns Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_final_of_bool_returns_bool() {
    let expr = final_expr(gt(var("x"), int(0)));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "Final of comparison should return Bool"
    );
}

// =============================================================================
// Proof coverage: infer_expr_sort — Closure and empty Match (catch-all)
// =============================================================================

/// Closure with Bool body infers as Sort::Bool (#994).
#[test]
#[timeout(30000)]
fn infer_expr_sort_closure_bool_body() {
    let closure = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(bool_expr(true)),
    };
    assert_eq!(
        infer_expr_sort(&closure),
        Sort::Bool,
        "Closure with Bool body should infer as Bool, not trigger SortFallbackToInt"
    );
}

/// Closure with Int body infers as Sort::Int (#994).
#[test]
#[timeout(30000)]
fn infer_expr_sort_closure_int_body() {
    let closure = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(int(42)),
    };
    assert_eq!(
        infer_expr_sort(&closure),
        Sort::Int,
        "Closure with Int body should infer as Int"
    );
}

/// Empty Match returns Sort::Int (catch-all).
#[test]
#[timeout(30000)]
fn infer_expr_sort_empty_match_returns_int() {
    let expr = match_expr(var("x"), vec![]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Empty match should fall to catch-all and return Int"
    );
}
