// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
#[timeout(5000)]
fn mentions_bound_var_direct() {
    assert!(expr_mentions_bound_var(&var("x"), &["x".to_string()]));
}

#[test]
#[timeout(5000)]
fn mentions_bound_var_absent() {
    assert!(!expr_mentions_bound_var(&var("y"), &["x".to_string()]));
}

#[test]
#[timeout(5000)]
fn mentions_bound_var_in_binop() {
    let expr = add(var("x"), int(1));
    assert!(expr_mentions_bound_var(&expr, &["x".to_string()]));
    assert!(!expr_mentions_bound_var(&expr, &["y".to_string()]));
}

#[test]
#[timeout(5000)]
fn mentions_bound_var_in_method_call() {
    let expr = method_call(var("v"), "len", vec![var("x")]);
    assert!(expr_mentions_bound_var(&expr, &["x".to_string()]));
    assert!(expr_mentions_bound_var(&expr, &["v".to_string()]));
    assert!(!expr_mentions_bound_var(&expr, &["z".to_string()]));
}

#[test]
#[timeout(5000)]
fn mentions_bound_var_shadowed_by_forall() {
    // forall x. x > 0 — the "x" reference is to the quantifier's own variable,
    // not to an outer bound variable named "x"
    let expr = forall("x", gt(var("x"), int(0)));
    assert!(!expr_mentions_bound_var(&expr, &["x".to_string()]));
}

#[test]
#[timeout(5000)]
fn mentions_bound_var_not_shadowed_different_name() {
    // forall y. x > 0 — "x" is free, not shadowed by "y"
    let expr = forall("y", gt(var("x"), int(0)));
    assert!(expr_mentions_bound_var(&expr, &["x".to_string()]));
}

#[test]
#[timeout(5000)]
fn mentions_bound_var_shadowed_by_let() {
    // let x = 1 in x — the body "x" is the let-bound var, not the outer one
    let expr = let_bind("x", int(1), var("x"));
    assert!(!expr_mentions_bound_var(&expr, &["x".to_string()]));
}

#[test]
#[timeout(5000)]
fn mentions_bound_var_in_let_value_not_shadowed() {
    // let y = x in y — "x" in the value is not shadowed by "y" binder
    let expr = let_bind("y", var("x"), var("y"));
    assert!(expr_mentions_bound_var(&expr, &["x".to_string()]));
}

#[test]
#[timeout(5000)]
fn mentions_bound_var_literal_false() {
    assert!(!expr_mentions_bound_var(&int(42), &["x".to_string()]));
    assert!(!expr_mentions_bound_var(
        &bool_expr(true),
        &["x".to_string()]
    ));
}

#[test]
#[timeout(5000)]
fn mentions_bound_var_in_ite() {
    let expr = ite(var("x"), int(1), int(2));
    assert!(expr_mentions_bound_var(&expr, &["x".to_string()]));
}

#[test]
#[timeout(5000)]
fn mentions_bound_var_closure_shadows() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(var("x")),
    };
    assert!(!expr_mentions_bound_var(&expr, &["x".to_string()]));
}

#[test]
#[timeout(5000)]
fn mentions_bound_var_closure_does_not_shadow_other() {
    let expr = PureExpr::Closure {
        params: vec![("y".to_string(), None)],
        body: Arc::new(var("x")),
    };
    assert!(expr_mentions_bound_var(&expr, &["x".to_string()]));
}

#[test]
#[timeout(5000)]
fn mentions_bound_var_match_arm_shadows_binding() {
    // Match arm pattern binding "x" should shadow the outer bound var "x".
    // Without this shadowing, eager instantiation gets false positives
    // that skip valid ground witnesses. (#1246)
    use trust_wp_core::formula::Pattern;
    let expr = match_expr(
        var("scrutinee"),
        vec![(Pattern::Binding("x".to_string()), var("x"))],
    );
    // "x" in the arm body refers to the pattern binding, not outer "x"
    assert!(!expr_mentions_bound_var(&expr, &["x".to_string()]));
    // But "scrutinee" is still visible
    assert!(expr_mentions_bound_var(&expr, &["scrutinee".to_string()]));
}

#[test]
#[timeout(5000)]
fn mentions_bound_var_exists_shadows() {
    // exists x. x > 0 — "x" in body is the quantifier's own variable
    let expr = exists("x", gt(var("x"), int(0)));
    assert!(!expr_mentions_bound_var(&expr, &["x".to_string()]));
}

#[test]
#[timeout(5000)]
fn mentions_bound_var_let_assume() {
    let expr = let_assume(var("x"), var("y"));
    assert!(expr_mentions_bound_var(&expr, &["x".to_string()]));
    assert!(expr_mentions_bound_var(&expr, &["y".to_string()]));
    assert!(!expr_mentions_bound_var(&expr, &["z".to_string()]));
}

#[test]
#[timeout(5000)]
fn mentions_bound_var_let_obligation() {
    let expr = let_obligation(var("x"), var("y"));
    assert!(expr_mentions_bound_var(&expr, &["x".to_string()]));
    assert!(expr_mentions_bound_var(&expr, &["y".to_string()]));
}
