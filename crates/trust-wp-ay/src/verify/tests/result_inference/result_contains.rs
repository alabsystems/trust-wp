// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;

use crate::{
    tests::helpers::{
        bool_expr, deref, let_assume, let_bind, let_obligation, method_call, old, var, view,
    },
    verify::expr_contains_result_var,
    PureExpr,
};

#[test]
#[timeout(30000)]
fn contains_result_in_match_scrutinee() {
    let expr = crate::tests::helpers::match_expr(
        var("result"),
        vec![(crate::Pattern::Wildcard, crate::tests::helpers::int(0))],
    );
    assert!(
        expr_contains_result_var(&expr),
        "result in match scrutinee should be detected"
    );
}

#[test]
#[timeout(30000)]
fn contains_result_in_match_arm_body() {
    let expr = crate::tests::helpers::match_expr(
        var("x"),
        vec![(crate::Pattern::Wildcard, var("result"))],
    );
    assert!(
        expr_contains_result_var(&expr),
        "result in match arm body should be detected"
    );
}

#[test]
#[timeout(30000)]
fn no_result_in_match() {
    let expr =
        crate::tests::helpers::match_expr(var("x"), vec![(crate::Pattern::Wildcard, var("y"))]);
    assert!(
        !expr_contains_result_var(&expr),
        "match with no result var should return false"
    );
}

#[test]
#[timeout(30000)]
fn contains_result_in_let_value() {
    let expr = let_bind("x", var("result"), crate::tests::helpers::int(0));
    assert!(
        expr_contains_result_var(&expr),
        "result in let value position should be detected"
    );
}

#[test]
#[timeout(30000)]
fn contains_result_in_let_body() {
    let expr = let_bind("x", crate::tests::helpers::int(1), var("result"));
    assert!(
        expr_contains_result_var(&expr),
        "result in let body position should be detected"
    );
}

#[test]
#[timeout(30000)]
fn no_result_in_let() {
    let expr = let_bind("x", crate::tests::helpers::int(1), var("y"));
    assert!(
        !expr_contains_result_var(&expr),
        "let with no result var should return false"
    );
}

#[test]
#[timeout(30000)]
fn contains_result_in_let_assume_assumption() {
    let expr = let_assume(var("result"), crate::tests::helpers::int(0));
    assert!(
        expr_contains_result_var(&expr),
        "result in let_assume assumption should be detected"
    );
}

#[test]
#[timeout(30000)]
fn contains_result_in_let_assume_body() {
    let expr = let_assume(bool_expr(true), var("result"));
    assert!(
        expr_contains_result_var(&expr),
        "result in let_assume body should be detected"
    );
}

#[test]
#[timeout(30000)]
fn contains_result_in_let_obligation() {
    let expr = let_obligation(var("result"), crate::tests::helpers::int(0));
    assert!(
        expr_contains_result_var(&expr),
        "result in let_obligation should be detected"
    );
}

#[test]
#[timeout(30000)]
fn contains_result_in_closure_body() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(var("result")),
    };
    assert!(
        expr_contains_result_var(&expr),
        "result in closure body should be detected"
    );
}

#[test]
#[timeout(30000)]
fn no_result_in_closure() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(var("x")),
    };
    assert!(
        !expr_contains_result_var(&expr),
        "closure with no result var should return false"
    );
}

#[test]
#[timeout(30000)]
fn contains_result_in_forall_body() {
    let expr = crate::tests::helpers::forall("x", var("result"));
    assert!(
        expr_contains_result_var(&expr),
        "result in forall body should be detected"
    );
}

#[test]
#[timeout(30000)]
fn contains_result_in_exists_body() {
    let expr = crate::tests::helpers::exists("x", var("result"));
    assert!(
        expr_contains_result_var(&expr),
        "result in exists body should be detected"
    );
}

#[test]
#[timeout(30000)]
fn contains_result_in_old() {
    let expr = old(var("result"));
    assert!(
        expr_contains_result_var(&expr),
        "result inside old() should be detected"
    );
}

#[test]
#[timeout(30000)]
fn contains_result_in_deref() {
    let expr = deref(var("result"));
    assert!(
        expr_contains_result_var(&expr),
        "result inside deref should be detected"
    );
}

#[test]
#[timeout(30000)]
fn contains_result_in_view() {
    let expr = view(var("result"));
    assert!(
        expr_contains_result_var(&expr),
        "result inside view should be detected"
    );
}

#[test]
#[timeout(30000)]
fn contains_result_in_method_call_receiver() {
    let expr = method_call(var("result"), "len", vec![]);
    assert!(
        expr_contains_result_var(&expr),
        "result as method call receiver should be detected"
    );
}

#[test]
#[timeout(30000)]
fn contains_result_in_method_call_args() {
    let expr = method_call(var("x"), "push", vec![var("result")]);
    assert!(
        expr_contains_result_var(&expr),
        "result in method call args should be detected"
    );
}

#[test]
#[timeout(30000)]
fn literal_bool_no_result() {
    assert!(
        !expr_contains_result_var(&bool_expr(true)),
        "bool literal should not contain result var"
    );
}

#[test]
#[timeout(30000)]
fn literal_int_no_result() {
    assert!(
        !expr_contains_result_var(&crate::tests::helpers::int(42)),
        "int literal should not contain result var"
    );
}
