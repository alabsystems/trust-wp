// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

// --- expr_contains_named_field_access tests ---
use trust_wp_core::formula::internal::tuple_lowering::NAMED_FIELD_LOGIC_FN_PREFIX;

use super::{
    super::super::{
        expr_contains_named_field_access, is_known_seq_container, type_path_short_name,
    },
    *,
};

#[test]
fn expr_contains_named_field_access_positive() {
    let expr = PureExpr::LogicFnCall {
        name: format!("{NAMED_FIELD_LOGIC_FN_PREFIX}my_field"),
        args: vec![PureExpr::Var("self".into(), None)],
    };
    assert!(expr_contains_named_field_access(&expr));
}

#[test]
fn expr_contains_named_field_access_negative_plain_logic_fn() {
    let expr = PureExpr::LogicFnCall {
        name: "some_other_fn".to_string(),
        args: vec![PureExpr::Int(1)],
    };
    assert!(!expr_contains_named_field_access(&expr));
}

#[test]
fn expr_contains_named_field_access_negative_literal() {
    assert!(!expr_contains_named_field_access(&PureExpr::Int(42)));
    assert!(!expr_contains_named_field_access(&PureExpr::Bool(true)));
}

#[test]
fn expr_contains_named_field_access_nested_in_binop() {
    let inner = PureExpr::LogicFnCall {
        name: format!("{NAMED_FIELD_LOGIC_FN_PREFIX}x"),
        args: vec![PureExpr::Var("self".into(), None)],
    };
    let expr = PureExpr::BinOp(Arc::new(inner), BinOp::Gt, Arc::new(PureExpr::Int(0)));
    assert!(expr_contains_named_field_access(&expr));
}

#[test]
fn expr_contains_named_field_access_nested_in_forall() {
    let inner = PureExpr::LogicFnCall {
        name: format!("{NAMED_FIELD_LOGIC_FN_PREFIX}value"),
        args: vec![PureExpr::Var("self".into(), None)],
    };
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(inner),
        triggers: vec![],
    };
    assert!(expr_contains_named_field_access(&expr));
}

#[test]
fn expr_contains_named_field_access_method_call_not_matched() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("self".into(), None)),
        method: format!("{NAMED_FIELD_LOGIC_FN_PREFIX}x"),
        args: vec![],
    };
    assert!(
        !expr_contains_named_field_access(&expr),
        "method calls are not logic fn calls — should not match"
    );
}

// --- type_path_short_name tests ---

#[test]
fn type_path_short_name_simple_path() {
    assert_eq!(type_path_short_name("std::vec::Vec"), "Vec");
}

#[test]
fn type_path_short_name_single_segment() {
    assert_eq!(type_path_short_name("Duration"), "Duration");
}

#[test]
fn type_path_short_name_nested_module() {
    assert_eq!(
        type_path_short_name("std::collections::hash_map::HashMap"),
        "HashMap"
    );
}

#[test]
fn type_path_short_name_empty_string() {
    assert_eq!(type_path_short_name(""), "");
}

// --- known_seq_container tests ---

#[test]
fn known_seq_container_matches_std_paths() {
    assert!(is_known_seq_container("Vec"));
    assert!(is_known_seq_container("alloc::vec::Vec"));
    assert!(is_known_seq_container(
        "alloc::collections::vec_deque::VecDeque"
    ));
}

#[test]
fn known_seq_container_rejects_suffix_matches() {
    assert!(!is_known_seq_container("mycrate::FooVec"));
    assert!(!is_known_seq_container("mycrate::VecDequeLike"));
    assert!(!is_known_seq_container(
        "mycrate::collections::vector::VecMap"
    ));
}
