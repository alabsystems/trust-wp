// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `NamedBindingValue`.

use trust_wp_core::formula::{ExprSort, NamedBindingValue, PureExpr};

#[test]
fn new_with_sort() {
    let binding = NamedBindingValue::new(Some(ExprSort::Int), PureExpr::Int(42));
    assert_eq!(binding.sort, Some(ExprSort::Int));
    assert_eq!(binding.value, PureExpr::Int(42));
}

#[test]
fn new_without_sort() {
    let binding = NamedBindingValue::new(None, PureExpr::Bool(true));
    assert_eq!(binding.sort, None);
    assert_eq!(binding.value, PureExpr::Bool(true));
}

#[test]
fn untyped_sets_sort_none() {
    let binding = NamedBindingValue::untyped(PureExpr::Int(7));
    assert_eq!(binding.sort, None);
    assert_eq!(binding.value, PureExpr::Int(7));
}

#[test]
fn lhs_var_with_sort() {
    let binding = NamedBindingValue::new(Some(ExprSort::Bool), PureExpr::Bool(true));
    let var = binding.lhs_var("flag");
    assert_eq!(var, PureExpr::Var("flag".to_string(), Some(ExprSort::Bool)));
}

#[test]
fn lhs_var_without_sort() {
    let binding = NamedBindingValue::untyped(PureExpr::Int(0));
    let var = binding.lhs_var("x");
    assert_eq!(var, PureExpr::Var("x".to_string(), None));
}

#[test]
fn lhs_var_preserves_seq_sort() {
    let binding = NamedBindingValue::new(Some(ExprSort::Seq), PureExpr::Int(0));
    let var = binding.lhs_var("items");
    assert_eq!(var, PureExpr::Var("items".to_string(), Some(ExprSort::Seq)));
}

#[test]
fn lhs_var_preserves_fmap_sort() {
    let binding = NamedBindingValue::new(Some(ExprSort::FMap), PureExpr::Int(0));
    let var = binding.lhs_var("map");
    assert_eq!(var, PureExpr::Var("map".to_string(), Some(ExprSort::FMap)));
}

#[test]
fn equality_same_values() {
    let a = NamedBindingValue::new(Some(ExprSort::Int), PureExpr::Int(5));
    let b = NamedBindingValue::new(Some(ExprSort::Int), PureExpr::Int(5));
    assert_eq!(a, b);
}

#[test]
fn inequality_different_sort() {
    let a = NamedBindingValue::new(Some(ExprSort::Int), PureExpr::Int(5));
    let b = NamedBindingValue::new(Some(ExprSort::Bool), PureExpr::Int(5));
    assert_ne!(a, b);
}

#[test]
fn inequality_different_value() {
    let a = NamedBindingValue::new(None, PureExpr::Int(1));
    let b = NamedBindingValue::new(None, PureExpr::Int(2));
    assert_ne!(a, b);
}

#[test]
fn clone_preserves_all_fields() {
    let a = NamedBindingValue::new(Some(ExprSort::Seq), PureExpr::Bool(false));
    let b = a.clone();
    assert_eq!(a, b);
}
