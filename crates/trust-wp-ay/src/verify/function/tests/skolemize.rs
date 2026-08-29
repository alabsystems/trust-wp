// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// --- skolemize_negated_universal ---
// Coverage gap: 140-line Skolemization function with zero direct tests.
// This is soundness-critical: incorrect Skolemization can cause false
// verification results (both false positives and negatives).

#[test]
#[timeout(30000)]
fn skolemize_non_forall_returns_none() {
    use super::skolemize_negated_universal;

    // Non-forall expression should return None
    assert!(
        skolemize_negated_universal(&int(42)).is_none(),
        "non-forall should return None"
    );
    assert!(
        skolemize_negated_universal(&var("x")).is_none(),
        "bare Var should return None"
    );
}

#[test]
#[timeout(30000)]
fn skolemize_single_forall_creates_skolem_constant() {
    use super::skolemize_negated_universal;

    // forall<x> P(x)  ->  NOT P(sk_x)
    let expr = forall("x", logic_fn_call("P", vec![var("x")]));
    let result = skolemize_negated_universal(&expr).expect("forall should be Skolemized");

    // Result should be NOT(P(sk_x))
    match &result {
        PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, inner) => match inner.as_ref() {
            PureExpr::LogicFnCall { name, args } => {
                assert_eq!(name, "P");
                assert_eq!(args.len(), 1);
                assert_eq!(args[0], var("sk_x"));
            }
            other => panic!("expected LogicFnCall, got {other:?}"),
        },
        other => panic!("expected UnOp(Not, ...), got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn skolemize_nested_forall_creates_multiple_skolem_constants() {
    use super::skolemize_negated_universal;

    // forall<a> forall<b> a < b  ->  NOT(sk_a < sk_b)
    let inner = forall(
        "b",
        PureExpr::BinOp(
            Arc::new(var("a")),
            trust_wp_core::formula::BinOp::Lt,
            Arc::new(var("b")),
        ),
    );
    let expr = forall("a", inner);
    let result = skolemize_negated_universal(&expr).expect("nested forall should be Skolemized");

    match &result {
        PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, inner) => match inner.as_ref() {
            PureExpr::BinOp(left, trust_wp_core::formula::BinOp::Lt, right) => {
                assert_eq!(**left, var("sk_a"), "left should be Skolem constant for a");
                assert_eq!(
                    **right,
                    var("sk_b"),
                    "right should be Skolem constant for b"
                );
            }
            other => panic!("expected BinOp(Lt), got {other:?}"),
        },
        other => panic!("expected UnOp(Not, ...), got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn skolemize_preserves_free_variables() {
    use super::skolemize_negated_universal;
    // forall<x> x + y > 0  ->  NOT(sk_x + y > 0)
    // Free variable "y" should be preserved.
    use crate::tests::helpers::add;
    let body = PureExpr::BinOp(
        Arc::new(add(var("x"), var("y"))),
        trust_wp_core::formula::BinOp::Gt,
        Arc::new(int(0)),
    );
    let expr = forall("x", body);
    let result = skolemize_negated_universal(&expr).expect("should Skolemize");

    // Check that "y" is still "y" (not sk_y) and "x" became "sk_x"
    let result_str = format!("{result:?}");
    assert!(
        result_str.contains("sk_x"),
        "bound var x should become sk_x: {result_str}"
    );
    assert!(
        !result_str.contains("sk_y"),
        "free var y should NOT be Skolemized: {result_str}"
    );
}

#[test]
#[timeout(30000)]
fn skolemize_preserves_declared_variable_sorts() {
    use super::skolemize_negated_universal;
    use crate::tests::helpers::forall_with_sort;

    let expr = forall_with_sort(
        "n",
        ExprSort::Int,
        forall_with_sort(
            "flag",
            ExprSort::Bool,
            and(
                eq(var_with_sort("n", ExprSort::Int), int(1)),
                eq(var_with_sort("flag", ExprSort::Bool), bool_expr(true)),
            ),
        ),
    );

    let result = skolemize_negated_universal(&expr).expect("should Skolemize");

    let expected = not(and(
        eq(var_with_sort("sk_n", ExprSort::Int), int(1)),
        eq(var_with_sort("sk_flag", ExprSort::Bool), bool_expr(true)),
    ));
    assert_eq!(
        result, expected,
        "Skolem constants must preserve declared sorts for downstream encoding"
    );
}

// --- Guard extraction tests (#2696) ---
// When the forall body is an implication `guard ==> consequent`,
// Skolemization decomposes it into `guard[sk] AND NOT consequent[sk]`
// instead of `NOT(guard[sk] ==> consequent[sk])`. This provides
// concrete ground terms from the guard for E-matching.

#[test]
#[timeout(30000)]
fn skolemize_single_implication_extracts_guard() {
    use super::skolemize_negated_universal;

    // forall<i> (i >= 0) ==> P(i)
    // Skolemized with guard extraction:
    //   (sk_i >= 0) AND NOT P(sk_i)
    let body = implies(ge(var("i"), int(0)), logic_fn_call("P", vec![var("i")]));
    let expr = forall("i", body);
    let result = skolemize_negated_universal(&expr).expect("should Skolemize");

    // Expected: ge(sk_i, 0) AND NOT P(sk_i)
    let expected = and(
        ge(var("sk_i"), int(0)),
        not(logic_fn_call("P", vec![var("sk_i")])),
    );
    assert_eq!(
        result, expected,
        "guard extraction should decompose implication into guard AND NOT consequent"
    );
}

#[test]
#[timeout(30000)]
fn skolemize_nested_implications_extracts_all_guards() {
    use super::skolemize_negated_universal;

    // forall<i> (i >= 0) ==> (i < 10) ==> P(i)
    // Skolemized: (sk_i >= 0) AND (sk_i < 10) AND NOT P(sk_i)
    let body = implies(
        ge(var("i"), int(0)),
        implies(lt(var("i"), int(10)), logic_fn_call("P", vec![var("i")])),
    );
    let expr = forall("i", body);
    let result = skolemize_negated_universal(&expr).expect("should Skolemize");

    let expected = and(
        ge(var("sk_i"), int(0)),
        and(
            lt(var("sk_i"), int(10)),
            not(logic_fn_call("P", vec![var("sk_i")])),
        ),
    );
    assert_eq!(
        result, expected,
        "nested implications should extract all guards"
    );
}

#[test]
#[timeout(30000)]
fn skolemize_non_implication_body_negates_directly() {
    use super::skolemize_negated_universal;

    // forall<x> P(x) AND Q(x)  (no implication)
    // Skolemized: NOT(P(sk_x) AND Q(sk_x))
    let body = and(
        logic_fn_call("P", vec![var("x")]),
        logic_fn_call("Q", vec![var("x")]),
    );
    let expr = forall("x", body);
    let result = skolemize_negated_universal(&expr).expect("should Skolemize");

    let expected = not(and(
        logic_fn_call("P", vec![var("sk_x")]),
        logic_fn_call("Q", vec![var("sk_x")]),
    ));
    assert_eq!(
        result, expected,
        "non-implication body should use simple NOT negation"
    );
}

#[test]
#[timeout(30000)]
fn skolemize_nested_forall_with_guard_extraction() {
    use super::skolemize_negated_universal;

    // forall<a> forall<b> (a > 0) ==> (a + b > b)
    // Skolemized: (sk_a > 0) AND NOT(sk_a + sk_b > sk_b)
    let body = implies(gt(var("a"), int(0)), gt(add(var("a"), var("b")), var("b")));
    let inner = forall("b", body);
    let expr = forall("a", inner);
    let result = skolemize_negated_universal(&expr).expect("should Skolemize");

    let expected = and(
        gt(var("sk_a"), int(0)),
        not(gt(add(var("sk_a"), var("sk_b")), var("sk_b"))),
    );
    assert_eq!(
        result, expected,
        "nested forall with guard should extract guard and Skolemize both variables"
    );
}
