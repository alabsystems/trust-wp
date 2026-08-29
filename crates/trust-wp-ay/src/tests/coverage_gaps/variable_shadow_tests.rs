// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

/// Regression test for #1135: `expr_mentions_var` must respect quantifier
/// variable shadowing. `forall<x> Var("x")` should NOT report that the
/// outer `x` is mentioned — the inner `x` is a different binding.
#[test]
#[timeout(5000)]
fn test_expr_mentions_var_forall_shadow() {
    // forall<x> x  — the inner x is bound by the forall, not the outer x
    let expr = forall("x", var("x"));
    assert!(
        !crate::expr::expr_mentions_var(&expr, "x"),
        "forall<x> x should shadow the outer x"
    );
}

/// Non-shadow case: `forall<t> Var("x")` still mentions outer `x`.
#[test]
#[timeout(5000)]
fn test_expr_mentions_var_forall_no_shadow() {
    let expr = forall("t", var("x"));
    assert!(
        crate::expr::expr_mentions_var(&expr, "x"),
        "forall<t> x should still mention the outer x"
    );
}

/// Regression test for #1135: `exists<x> Var("x")` shadows correctly.
#[test]
#[timeout(5000)]
fn test_expr_mentions_var_exists_shadow() {
    let expr = exists("x", var("x"));
    assert!(
        !crate::expr::expr_mentions_var(&expr, "x"),
        "exists<x> x should shadow the outer x"
    );
}

/// Regression test for #1135: `let x = y in x` — the body `x` is
/// the let-bound `x`, not the outer one.
#[test]
#[timeout(5000)]
fn test_expr_mentions_var_let_shadow() {
    let expr = let_bind("x", var("y"), var("x"));
    assert!(
        !crate::expr::expr_mentions_var(&expr, "x"),
        "let x = y in x should shadow the outer x in the body"
    );
}

/// Let binding value is NOT in scope of the binding: `let x = x in y`
/// should report that the outer `x` IS mentioned (in the value position).
#[test]
#[timeout(5000)]
fn test_expr_mentions_var_let_value_not_shadowed() {
    let expr = let_bind("x", var("x"), var("y"));
    assert!(
        crate::expr::expr_mentions_var(&expr, "x"),
        "let x = x in y — the value `x` references the outer x"
    );
}

/// Regression test for #1135: match arm pattern binding shadows the variable.
#[test]
#[timeout(5000)]
fn test_expr_mentions_var_match_pattern_shadow() {
    // match(y) { x => x } — the arm body `x` is the pattern-bound x
    let expr = match_expr(var("y"), vec![(Pattern::Binding("x".into()), var("x"))]);
    assert!(
        !crate::expr::expr_mentions_var(&expr, "x"),
        "match arm binding x should shadow the outer x in the body"
    );
}

/// Match scrutinee is NOT shadowed by arm patterns.
#[test]
#[timeout(5000)]
fn test_expr_mentions_var_match_scrutinee_not_shadowed() {
    let expr = match_expr(var("x"), vec![(Pattern::Binding("x".into()), var("y"))]);
    assert!(
        crate::expr::expr_mentions_var(&expr, "x"),
        "match scrutinee should not be shadowed by arm patterns"
    );
}

/// Regression test for #1135: closure parameter shadows the variable.
#[test]
#[timeout(5000)]
fn test_expr_mentions_var_closure_param_shadow() {
    let expr = PureExpr::Closure {
        params: vec![("x".into(), None)],
        body: Arc::new(var("x")),
    };
    assert!(
        !crate::expr::expr_mentions_var(&expr, "x"),
        "closure |x| x should shadow the outer x"
    );
}

/// Regression test for #1135: `body_has_postcondition_mut_with_var`
/// must NOT match through a shadowing quantifier.
/// `forall<s> postcondition_mut(f, a, s, r)` — the `s` is forall-bound,
/// not the outer existential's `s`.
#[test]
#[timeout(5000)]
fn test_body_has_postcondition_mut_forall_shadow() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = forall("s", inner);
    assert!(
        !AYEncoder::body_has_postcondition_mut_with_var(&body, "s"),
        "forall<s> postcondition_mut(..., s, ...) should shadow the outer s"
    );
}

/// Non-shadow: `forall<t> postcondition_mut(f, a, s, r)` should still match.
#[test]
#[timeout(5000)]
fn test_body_has_postcondition_mut_forall_no_shadow() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = forall("t", inner);
    assert!(
        AYEncoder::body_has_postcondition_mut_with_var(&body, "s"),
        "forall<t> postcondition_mut(..., s, ...) — s is not shadowed"
    );
}

/// Let shadow: `let s = x in postcondition_mut(f, a, s, r)` should NOT match.
#[test]
#[timeout(5000)]
fn test_body_has_postcondition_mut_let_shadow() {
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let body = let_bind("s", var("x"), inner);
    assert!(
        !AYEncoder::body_has_postcondition_mut_with_var(&body, "s"),
        "let s = x in postcondition_mut(..., s, ...) — s is shadowed by let"
    );
}

/// Integration: `assert_eager_existential_skolemizations` should NOT fire
/// when the existential variable is shadowed by an inner forall.
#[test]
#[timeout(30000)]
fn test_eager_skolem_skips_shadowed_existential() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register postcondition_mut so it has a declaration
    let mut_expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    encoder
        .encode_pure(&mut_expr)
        .expect("postcondition_mut should encode");

    // exists<s> (forall<s> postcondition_mut(f, a, s, r))
    // The inner s is forall-bound, so Skolemization should NOT fire.
    let inner = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("s"), var("r")],
    );
    let shadowed = exists("s", forall("s", inner));

    // Should succeed without error — just no Skolemization
    encoder
        .assert_eager_existential_skolemizations(&[shadowed])
        .expect("should not error on shadowed existential");
}
