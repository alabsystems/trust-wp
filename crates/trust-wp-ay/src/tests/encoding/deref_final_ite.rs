// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Tests for Deref/Final distribution through Ite expressions (Part of #1006)

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_encode_deref_of_ite_distributes() {
    // *(if c { x } else { y }) should encode as if c { *x } else { *y }
    // instead of returning "complex deref expression" error.
    let mut encoder = AYEncoder::new();

    let expr = deref(ite(var("c"), var("x"), var("y")));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Deref of Ite should succeed via distribution");
    // Both branches should create _current variables
    assert!(
        encoder.vars_for_test().contains_key("x_current"),
        "then-branch deref should create x_current"
    );
    assert!(
        encoder.vars_for_test().contains_key("y_current"),
        "else-branch deref should create y_current"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_final_of_ite_distributes() {
    // ^(if c { x } else { y }) should encode as if c { ^x } else { ^y }
    // instead of returning "complex final expression" error.
    let mut encoder = AYEncoder::new();

    let expr = final_expr(ite(var("c"), var("x"), var("y")));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Final of Ite should succeed via distribution");
    // Both branches should create _final variables
    assert!(
        encoder.vars_for_test().contains_key("x_final"),
        "then-branch final should create x_final"
    );
    assert!(
        encoder.vars_for_test().contains_key("y_final"),
        "else-branch final should create y_final"
    );
}

#[test]
#[timeout(30000)]
fn test_deref_ite_semantic_correctness() {
    // Semantic: c=true, *x=5, *y=10 → *(ite(c, x, y)) == 5
    let mut encoder = AYEncoder::new();

    let expr = deref(ite(var("c"), var("x"), var("y")));
    let term = encoder
        .encode_pure(&expr)
        .expect("Deref(Ite) should encode");

    // Assert c = true
    let c_var = encoder.encode_pure(&var("c")).unwrap();
    encoder.solver.assert_term(c_var);

    // Assert *x = 5
    let x_current = encoder.encode_pure(&deref(var("x"))).unwrap();
    let five = encoder.solver.int_const(5);
    let x_eq = encoder.solver.eq(x_current, five);
    encoder.solver.assert_term(x_eq);

    // Assert *y = 10
    let y_current = encoder.encode_pure(&deref(var("y"))).unwrap();
    let ten = encoder.solver.int_const(10);
    let y_eq = encoder.solver.eq(y_current, ten);
    encoder.solver.assert_term(y_eq);

    // Check *(ite(c, x, y)) == 5
    let result_eq = encoder.solver.eq(term, five);
    encoder.solver.assert_term(result_eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "*(ite(true, x, y)) should equal *x (5)"
    );
}

#[test]
#[timeout(30000)]
fn test_final_ite_semantic_correctness() {
    // Semantic: c=false, ^x=5, ^y=10 → ^(ite(c, x, y)) == 10
    let mut encoder = AYEncoder::new();

    let expr = final_expr(ite(var("c"), var("x"), var("y")));
    let term = encoder
        .encode_pure(&expr)
        .expect("Final(Ite) should encode");

    // Assert c = false
    let c_var = encoder.encode_pure(&var("c")).unwrap();
    let c_false = encoder.solver.not(c_var);
    encoder.solver.assert_term(c_false);

    // Assert ^x = 5
    let x_final = encoder.encode_pure(&final_expr(var("x"))).unwrap();
    let five = encoder.solver.int_const(5);
    let x_eq = encoder.solver.eq(x_final, five);
    encoder.solver.assert_term(x_eq);

    // Assert ^y = 10
    let y_final = encoder.encode_pure(&final_expr(var("y"))).unwrap();
    let ten = encoder.solver.int_const(10);
    let y_eq = encoder.solver.eq(y_final, ten);
    encoder.solver.assert_term(y_eq);

    // Check ^(ite(c, x, y)) == 10
    let result_eq = encoder.solver.eq(term, ten);
    encoder.solver.assert_term(result_eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "^(ite(false, x, y)) should equal ^y (10)"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_deref_of_match_distributes() {
    // *(match s { 1 => x, _ => y }) should encode as
    // match s { 1 => *x, _ => *y } via distribution, instead of returning
    // "complex deref expression" error. Mirrors the Deref(Ite) case.
    let mut encoder = AYEncoder::new();

    let expr = deref(match_expr(
        var("s"),
        vec![
            (Pattern::Literal(int(1)), var("x")),
            (Pattern::Wildcard, var("y")),
        ],
    ));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Deref of Match should succeed via distribution");
    assert!(
        encoder.vars_for_test().contains_key("x_current"),
        "matched-arm deref should create x_current"
    );
    assert!(
        encoder.vars_for_test().contains_key("y_current"),
        "default-arm deref should create y_current"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_final_of_match_distributes() {
    // ^(match s { 1 => x, _ => y }) should distribute the Final wrapper into
    // the arm bodies, mirroring the Final(Ite) case.
    let mut encoder = AYEncoder::new();

    let expr = final_expr(match_expr(
        var("s"),
        vec![
            (Pattern::Literal(int(1)), var("x")),
            (Pattern::Wildcard, var("y")),
        ],
    ));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Final of Match should succeed via distribution");
    assert!(
        encoder.vars_for_test().contains_key("x_final"),
        "matched-arm final should create x_final"
    );
    assert!(
        encoder.vars_for_test().contains_key("y_final"),
        "default-arm final should create y_final"
    );
}

#[test]
#[timeout(30000)]
fn test_deref_match_semantic_correctness() {
    // Semantic: s=1, *x=5, *y=10 → *(match s { 1 => x, _ => y }) == 5
    let mut encoder = AYEncoder::new();

    let expr = deref(match_expr(
        var("s"),
        vec![
            (Pattern::Literal(int(1)), var("x")),
            (Pattern::Wildcard, var("y")),
        ],
    ));
    let term = encoder
        .encode_pure(&expr)
        .expect("Deref(Match) should encode");

    // Assert s = 1 (selects the first arm)
    let s_var = encoder.encode_pure(&var("s")).unwrap();
    let one = encoder.solver.int_const(1);
    let s_eq = encoder.solver.eq(s_var, one);
    encoder.solver.assert_term(s_eq);

    // Assert *x = 5, *y = 10
    let x_current = encoder.encode_pure(&deref(var("x"))).unwrap();
    let five = encoder.solver.int_const(5);
    let x_eq = encoder.solver.eq(x_current, five);
    encoder.solver.assert_term(x_eq);

    let y_current = encoder.encode_pure(&deref(var("y"))).unwrap();
    let ten = encoder.solver.int_const(10);
    let y_eq = encoder.solver.eq(y_current, ten);
    encoder.solver.assert_term(y_eq);

    // Check *(match 1 { 1 => x, _ => y }) == 5
    let result_eq = encoder.solver.eq(term, five);
    encoder.solver.assert_term(result_eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "*(match 1 {{ 1 => x, _ => y }}) should equal *x (5)"
    );
}

#[test]
#[timeout(30000)]
fn test_nested_deref_of_ite_distributes() {
    // **(if c { x } else { y }) should distribute through both Deref layers
    let mut encoder = AYEncoder::new();

    let expr = deref(deref(ite(var("c"), var("x"), var("y"))));

    let _term = encoder
        .encode_pure(&expr)
        .expect("Nested deref of Ite should succeed");
    // Both branches should get double-deref: x_current_current, y_current_current
    assert!(
        encoder.vars_for_test().contains_key("x_current_current"),
        "double deref should create x_current_current"
    );
    assert!(
        encoder.vars_for_test().contains_key("y_current_current"),
        "double deref should create y_current_current"
    );
}
