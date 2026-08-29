// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for verification setup — extracted from inline tests (#1669).

use std::{collections::HashSet, sync::Arc};

use ntest::timeout;
use trust_wp_core::{formula::PureExpr, logic::type_invariant_method_name};

use super::*;
#[test]
#[timeout(30000)]
fn filter_type_invariants_drops_unreferenced_defs() {
    let inv = make_invariant("WithInv");
    let filtered = filter_type_invariants_for_goal(Some(std::slice::from_ref(&inv)), &[], &[], &[])
        .expect("type invariants should remain Some");
    assert!(
        filtered.is_empty(),
        "unreferenced type invariants should be filtered out"
    );
}

#[test]
#[timeout(30000)]
fn filter_type_invariants_keeps_dependency_closure() {
    let elem = make_invariant("Elem");
    let elem_method = type_invariant_method_name("Elem");

    let container =
        make_invariant("Container").with_element_invariant_method(Some(elem_method.clone()));
    let container_method = type_invariant_method_name("Container");

    let ensure = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
        method: container_method,
        args: vec![],
    };
    let filtered = filter_type_invariants_for_goal(
        Some(&[container.clone(), elem.clone()]),
        &[],
        &[ensure],
        &[],
    )
    .expect("type invariants should remain Some");

    let names: HashSet<String> = filtered
        .into_iter()
        .map(|i| i.type_name().to_string())
        .collect();
    assert!(
        names.contains("Container"),
        "referenced container invariant should be kept"
    );
    assert!(
        names.contains("Elem"),
        "element invariant dependency should be kept"
    );
}

/// Regression test for #1919: seq method calls in ensures must trigger
/// quantifier escalation via `any_expr_matches`.
#[test]
#[timeout(30000)]
fn seq_method_in_ensures_triggers_quantifier_detection() {
    use crate::expr_seq::expr_has_seq_method_needing_quantifiers;

    let push_back_ensure = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "v".to_string(),
            None,
        )))),
        method: "push_back".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };

    assert!(
        any_expr_matches(
            &[],
            &[push_back_ensure],
            &[],
            expr_has_seq_method_needing_quantifiers
        ),
        "push_back in ensures should trigger seq method quantifier detection (#1919)"
    );
}

#[test]
#[timeout(30000)]
fn no_seq_method_does_not_trigger_detection() {
    use crate::expr_seq::expr_has_seq_method_needing_quantifiers;

    let simple_ensure = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        trust_wp_core::formula::BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );

    assert!(
        !any_expr_matches(
            &[],
            &[simple_ensure],
            &[],
            expr_has_seq_method_needing_quantifiers
        ),
        "simple integer comparison should not trigger seq method detection"
    );
}

/// Regression test for #1922: BitOr in ensures must trigger quantifier
/// escalation because `encode_int_binop_uf` declares UFs and
/// `assert_bitwise_axioms` injects forall-quantified axioms.
#[test]
#[timeout(30000)]
fn bitwise_op_in_ensures_triggers_quantifier_detection() {
    use crate::expr::expr_has_bitwise_ops;

    let bitor_ensure = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        trust_wp_core::formula::BinOp::BitOr,
        Arc::new(PureExpr::Var("x".to_string(), None)),
    );

    assert!(
        any_expr_matches(&[], &[bitor_ensure], &[], expr_has_bitwise_ops),
        "BitOr in ensures should trigger bitwise detection (#1922)"
    );
}

/// Regression test for #1922: BitXor in requires must also trigger.
#[test]
#[timeout(30000)]
fn bitxor_in_requires_triggers_quantifier_detection() {
    use crate::expr::expr_has_bitwise_ops;

    let bitxor_req = PureExpr::BinOp(
        Arc::new(PureExpr::Var("a".to_string(), None)),
        trust_wp_core::formula::BinOp::BitXor,
        Arc::new(PureExpr::Var("b".to_string(), None)),
    );

    assert!(
        any_expr_matches(&[bitxor_req], &[], &[], expr_has_bitwise_ops),
        "BitXor in requires should trigger bitwise detection (#1922)"
    );
}

/// Regression test for #1923: fset_contains in ensures must trigger
/// UF-method detection because `encode_fset_method` declares UFs.
#[test]
#[timeout(30000)]
fn fset_method_in_ensures_triggers_quantifier_detection() {
    use crate::expr::expr_has_uf_method_call;

    let fset_ensure = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
        method: "fset_contains".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };

    assert!(
        any_expr_matches(&[], &[fset_ensure], &[], expr_has_uf_method_call),
        "fset_contains in ensures should trigger UF method detection (#1923)"
    );
}

/// Regression test for #1923: ext_eq triggers UF injection.
#[test]
#[timeout(30000)]
fn ext_eq_in_ensures_triggers_quantifier_detection() {
    use crate::expr::expr_has_uf_method_call;

    let ext_eq_ensure = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("a".to_string(), None)),
        method: "ext_eq".to_string(),
        args: vec![PureExpr::Var("b".to_string(), None)],
    };

    assert!(
        any_expr_matches(&[], &[ext_eq_ensure], &[], expr_has_uf_method_call),
        "ext_eq in ensures should trigger UF method detection (#1923)"
    );
}

/// Regression test for #1923: deep_model triggers UF injection.
#[test]
#[timeout(30000)]
fn deep_model_in_requires_triggers_quantifier_detection() {
    use crate::expr::expr_has_uf_method_call;

    let deep_model_req = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
        method: "deep_model".to_string(),
        args: vec![],
    };

    assert!(
        any_expr_matches(&[deep_model_req], &[], &[], expr_has_uf_method_call),
        "deep_model in requires should trigger UF method detection (#1923)"
    );
}

/// Negative test: plain integer arithmetic should NOT trigger bitwise
/// or UF-method detection.
#[test]
#[timeout(30000)]
fn plain_arithmetic_does_not_trigger_bitwise_or_uf_detection() {
    use crate::expr::{expr_has_bitwise_ops, expr_has_uf_method_call};

    let arith_ensure = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        trust_wp_core::formula::BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    assert!(
        !any_expr_matches(
            &[],
            std::slice::from_ref(&arith_ensure),
            &[],
            expr_has_bitwise_ops
        ),
        "Add should not trigger bitwise detection"
    );
    assert!(
        !any_expr_matches(
            &[],
            std::slice::from_ref(&arith_ensure),
            &[],
            expr_has_uf_method_call
        ),
        "Add should not trigger UF method detection"
    );
}
