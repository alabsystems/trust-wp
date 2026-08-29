// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Edge-case tests for `detect_body_constructor_name` and
//! `result_collection_sort_from_postcondition`.
//!
//! The 12 tests in `verify/tests/mod.rs` cover standard constructor names
//! (Some, None, Ok, Err, qualified paths, user variants, literals). These
//! tests cover named-struct brace syntax and underscore-prefixed temporaries.
//!
//! The collection sort tests exercise `result_collection_sort_from_postcondition`
//! through the `expr_collection_sort_for_result` → `infer_expr_sort` path,
//! verifying correct Seq/FMap detection and `normalize_collection_sort` behavior.

use ay_dpll::api::Sort;
use ntest::timeout;

use super::{detect_body_constructor_name, result_collection_sort_from_postcondition};
use crate::{
    tests::helpers::{eq, int, logic_fn_call, var, var_with_sort},
    BinOp, ExprSort, PureExpr,
};

// --- detect_body_constructor_name edge cases ---

/// Named struct literal: `Named{x,y}` → `short_constructor_name` strips braces → "Named".
#[test]
#[timeout(30000)]
fn detect_body_constructor_name_named_struct_literal() {
    let expr = logic_fn_call("Named{x,y}", vec![int(0), int(1)]);
    assert_eq!(detect_body_constructor_name(&expr), Some("Named"));
}

/// Named enum variant: `ENamed::A{x,y}` → strips path and braces → "A".
#[test]
#[timeout(30000)]
fn detect_body_constructor_name_named_variant_literal() {
    let expr = logic_fn_call("ENamed::A{x,y}", vec![int(0), int(1)]);
    assert_eq!(detect_body_constructor_name(&expr), Some("A"));
}

/// Underscore-prefixed MIR temporary (`_call_0`) — lowercase-first, not a constructor.
#[test]
#[timeout(30000)]
fn detect_body_constructor_name_underscore_temporary_returns_none() {
    let expr = var("_call_0");
    assert_eq!(detect_body_constructor_name(&expr), None);
}

/// Numeric string variable (rare MIR artifact) — not uppercase-first.
#[test]
#[timeout(30000)]
fn detect_body_constructor_name_numeric_var_returns_none() {
    let expr = var("0");
    assert_eq!(detect_body_constructor_name(&expr), None);
}

/// Empty-arg LogicFnCall with uppercase name — still detected as constructor.
#[test]
#[timeout(30000)]
fn detect_body_constructor_name_nullary_uppercase() {
    let expr = logic_fn_call("Unit", vec![]);
    assert_eq!(detect_body_constructor_name(&expr), Some("Unit"));
}

// --- result_collection_sort_from_postcondition ---

/// Empty ensures → None.
#[test]
#[timeout(30000)]
fn collection_sort_empty_ensures_returns_none() {
    assert_eq!(result_collection_sort_from_postcondition(&[]), None);
}

/// `result == Var("xs", Seq)` → the RHS has `ExprSort::Seq` which maps to
/// `Sort::seq(Sort::Int)`. The function should detect this as a collection sort.
#[test]
#[timeout(30000)]
fn collection_sort_result_eq_seq_var() {
    let ensures = vec![eq(var("result"), var_with_sort("xs", ExprSort::Seq))];
    let sort = result_collection_sort_from_postcondition(&ensures);
    assert_eq!(sort, Some(Sort::seq(Sort::Int)));
}

/// `Var("xs", Seq) == result` — result on RHS triggers the second branch of
/// `expr_collection_sort_for_result`.
#[test]
#[timeout(30000)]
fn collection_sort_seq_var_eq_result() {
    let ensures = vec![eq(var_with_sort("xs", ExprSort::Seq), var("result"))];
    let sort = result_collection_sort_from_postcondition(&ensures);
    assert_eq!(sort, Some(Sort::seq(Sort::Int)));
}

/// `result == Var("x", Int)` — Int is not a collection sort → None.
#[test]
#[timeout(30000)]
fn collection_sort_result_eq_int_var_returns_none() {
    let ensures = vec![eq(var("result"), var_with_sort("x", ExprSort::Int))];
    assert_eq!(result_collection_sort_from_postcondition(&ensures), None);
}

/// `result == Int(42)` — literal Int is not a collection sort → None.
#[test]
#[timeout(30000)]
fn collection_sort_result_eq_literal_int_returns_none() {
    let ensures = vec![eq(var("result"), int(42))];
    assert_eq!(result_collection_sort_from_postcondition(&ensures), None);
}

/// `result > Var("xs", Seq)` — non-equality comparison does NOT trigger
/// collection sort detection (only Eq/Ne do).
#[test]
#[timeout(30000)]
fn collection_sort_non_eq_comparison_returns_none() {
    let ensures = vec![PureExpr::BinOp(
        std::sync::Arc::new(var("result")),
        BinOp::Gt,
        std::sync::Arc::new(var_with_sort("xs", ExprSort::Seq)),
    )];
    assert_eq!(result_collection_sort_from_postcondition(&ensures), None);
}

/// `result != Var("xs", Seq)` — Ne also triggers collection sort detection.
#[test]
#[timeout(30000)]
fn collection_sort_result_ne_seq_var() {
    let ensures = vec![PureExpr::BinOp(
        std::sync::Arc::new(var("result")),
        BinOp::Ne,
        std::sync::Arc::new(var_with_sort("xs", ExprSort::Seq)),
    )];
    let sort = result_collection_sort_from_postcondition(&ensures);
    assert_eq!(sort, Some(Sort::seq(Sort::Int)));
}

/// `result == Var("x", None)` — unannotated var falls back to Sort::Int,
/// which is not a collection sort → None.
#[test]
#[timeout(30000)]
fn collection_sort_result_eq_unannotated_var_returns_none() {
    let ensures = vec![eq(var("result"), var("x"))];
    assert_eq!(result_collection_sort_from_postcondition(&ensures), None);
}

/// Multiple ensures: first has no collection sort, second does. The function
/// should find the sort from the second ensure.
#[test]
#[timeout(30000)]
fn collection_sort_second_ensure_has_seq() {
    let ensures = vec![
        eq(var("result"), int(0)),
        eq(var("result"), var_with_sort("xs", ExprSort::Seq)),
    ];
    let sort = result_collection_sort_from_postcondition(&ensures);
    assert_eq!(sort, Some(Sort::seq(Sort::Int)));
}

/// No `result` variable anywhere → None.
#[test]
#[timeout(30000)]
fn collection_sort_no_result_var_returns_none() {
    let ensures = vec![eq(
        var_with_sort("x", ExprSort::Seq),
        var_with_sort("y", ExprSort::Seq),
    )];
    assert_eq!(result_collection_sort_from_postcondition(&ensures), None);
}
