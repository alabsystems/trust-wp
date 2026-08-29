// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use trust_wp_core::formula::ExprSort;

use super::*;

#[test]
fn is_call_result_var_accepts_supported_prefixes() {
    assert!(is_call_result_var("call_0"));
    assert!(is_call_result_var("_call_42"));
    assert!(!is_call_result_var("call"));
    assert!(!is_call_result_var("tmp_0"));
}

#[test]
fn collect_equality_substitutions_uses_call_var_on_lhs() {
    let assumptions = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("call_1".into(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(7)),
    )];

    let substitutions = collect_equality_substitutions(&assumptions);

    let mut expected = HashMap::new();
    expected.insert("call_1".to_string(), PureExpr::Int(7));
    assert_eq!(substitutions, expected);
}

#[test]
fn collect_equality_substitutions_uses_call_var_on_rhs() {
    let assumptions = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Int(7)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("_call_2".into(), None)),
    )];

    let substitutions = collect_equality_substitutions(&assumptions);

    let mut expected = HashMap::new();
    expected.insert("_call_2".to_string(), PureExpr::Int(7));
    assert_eq!(substitutions, expected);
}

#[test]
fn collect_equality_substitutions_uses_deref_call_var_on_lhs() {
    let assumptions = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "_call_3".into(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Var("x".into(), Some(ExprSort::Int))),
    )];

    let substitutions = collect_equality_substitutions(&assumptions);

    let mut expected = HashMap::new();
    expected.insert(
        "_call_3".to_string(),
        PureExpr::Var("x".into(), Some(ExprSort::Int)),
    );
    assert_eq!(substitutions, expected);
}

#[test]
fn collect_equality_substitutions_uses_deref_call_var_on_rhs() {
    let assumptions = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), Some(ExprSort::Int))),
        BinOp::Eq,
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "call_4".into(),
            None,
        )))),
    )];

    let substitutions = collect_equality_substitutions(&assumptions);

    let mut expected = HashMap::new();
    expected.insert(
        "call_4".to_string(),
        PureExpr::Var("x".into(), Some(ExprSort::Int)),
    );
    assert_eq!(substitutions, expected);
}

#[test]
fn collect_equality_substitutions_ignores_non_call_results() {
    let assumptions = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("tmp".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(1)),
        ),
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("call_1".into(), None)),
            method: "get".to_string(),
            args: vec![PureExpr::Int(1)],
        },
    ];

    let substitutions = collect_equality_substitutions(&assumptions);

    assert!(substitutions.is_empty());
}

#[test]
fn normalize_extern_spec_self_expr_strips_deref_for_deref_mut() {
    let self_expr = PureExpr::Deref(Arc::new(PureExpr::Var(
        "x".into(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
    )));

    let normalized =
        normalize_extern_spec_self_expr("core::ops::deref::DerefMut::deref_mut", Some(self_expr));

    assert_eq!(
        normalized,
        Some(PureExpr::Var(
            "x".into(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        ))
    );
}

#[test]
fn normalize_extern_spec_self_expr_leaves_other_receivers_unchanged() {
    let self_expr = PureExpr::Deref(Arc::new(PureExpr::Var(
        "x".into(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
    )));

    let normalized =
        normalize_extern_spec_self_expr("core::ops::deref::Deref::deref", Some(self_expr.clone()));

    assert_eq!(normalized, Some(self_expr));
}
