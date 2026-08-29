// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// --- instantiate_embedded_existentials_with_body_witness (#2082) ---
// This is the core existential witness extraction, untested prior to this commit.

#[test]
#[timeout(30000)]
fn instantiate_existential_with_matching_constructor_witness() {
    use super::instantiate_embedded_existentials_with_body_witness;
    // Postcondition: exists y. result == Some(y) && y > 0
    // Body result: Some(42)
    // Expected: result == Some(42) && 42 > 0  (y := 42)
    let exists_body = and(
        eq(var("result"), logic_fn_call("Some", vec![var("y")])),
        PureExpr::BinOp(
            Arc::new(var("y")),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(int(0)),
        ),
    );
    let post = exists("y", exists_body);
    let return_expr = logic_fn_call("Some", vec![int(42)]);
    let result = instantiate_embedded_existentials_with_body_witness(&post, Some(&return_expr));

    // Should NOT be an Exists anymore — it should be instantiated
    assert!(
        !matches!(result, PureExpr::Exists { .. }),
        "existential should be instantiated with witness from body: got {result:?}"
    );

    // Verify the witness was actually substituted: the result should contain
    // Int(42) where var("y") used to be. Check both sides of the conjunction.
    let expected = and(
        eq(var("result"), logic_fn_call("Some", vec![int(42)])),
        PureExpr::BinOp(
            Arc::new(int(42)),
            trust_wp_core::formula::BinOp::Gt,
            Arc::new(int(0)),
        ),
    );
    assert_eq!(
        result, expected,
        "y should be substituted with Int(42) in both conjuncts"
    );
}

#[test]
#[timeout(30000)]
fn instantiate_existential_without_body_keeps_exists() {
    use super::instantiate_embedded_existentials_with_body_witness;
    // No body result → no witness → keep exists as-is
    let post = exists(
        "y",
        eq(var("result"), logic_fn_call("Some", vec![var("y")])),
    );
    let result = instantiate_embedded_existentials_with_body_witness(&post, None);
    assert!(
        matches!(result, PureExpr::Exists { .. }),
        "without body, existential should be preserved: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn instantiate_existential_no_matching_constructor_keeps_exists() {
    use super::instantiate_embedded_existentials_with_body_witness;
    // Postcondition expects Some(y), but body returns None() (different constructor)
    let post = exists(
        "y",
        eq(var("result"), logic_fn_call("Some", vec![var("y")])),
    );
    let return_expr = logic_fn_call("None", vec![]);
    let result = instantiate_embedded_existentials_with_body_witness(&post, Some(&return_expr));
    assert!(
        matches!(result, PureExpr::Exists { .. }),
        "mismatched constructor should preserve existential: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn instantiate_existential_ite_body_extracts_from_branch() {
    use super::instantiate_embedded_existentials_with_body_witness;
    // Body: ite(cond, Some(42), Some(0)) — both branches match
    // extract_ctor_arg_from_body tries then-branch first, so witness is 42
    let post = exists(
        "y",
        eq(var("result"), logic_fn_call("Some", vec![var("y")])),
    );
    let return_expr = ite(
        bool_expr(true),
        logic_fn_call("Some", vec![int(42)]),
        logic_fn_call("Some", vec![int(0)]),
    );
    let result = instantiate_embedded_existentials_with_body_witness(&post, Some(&return_expr));
    // Verify substitution: y := 42 (from then-branch)
    let expected = eq(var("result"), logic_fn_call("Some", vec![int(42)]));
    assert_eq!(
        result, expected,
        "ITE body should extract witness 42 from then-branch"
    );
}

#[test]
#[timeout(30000)]
fn instantiate_existential_ite_body_falls_back_to_else_branch() {
    use super::instantiate_embedded_existentials_with_body_witness;
    // Body: ite(cond, None, Some(11)) — the helper should retry the else branch
    // when the then branch does not contain the requested constructor.
    let post = exists(
        "y",
        eq(var("result"), logic_fn_call("Some", vec![var("y")])),
    );
    let return_expr = ite(
        bool_expr(false),
        logic_fn_call("None", vec![]),
        logic_fn_call("Some", vec![int(11)]),
    );

    let result = instantiate_embedded_existentials_with_body_witness(&post, Some(&return_expr));

    let expected = eq(var("result"), logic_fn_call("Some", vec![int(11)]));
    assert_eq!(
        result, expected,
        "ITE witness extraction should fall back to the else branch when needed"
    );
}

#[test]
#[timeout(30000)]
fn instantiate_existential_recurses_into_newly_exposed_nested_exists() {
    use super::instantiate_embedded_existentials_with_body_witness;
    // The outer instantiation should recurse into the resulting body so an
    // inner existential that becomes ground-reachable is instantiated too.
    let inner_exists = exists(
        "z",
        eq(var("result"), logic_fn_call("Some", vec![var("z")])),
    );
    let post = exists(
        "y",
        and(
            eq(var("result"), logic_fn_call("Some", vec![var("y")])),
            inner_exists,
        ),
    );
    let return_expr = logic_fn_call("Some", vec![int(7)]);

    let result = instantiate_embedded_existentials_with_body_witness(&post, Some(&return_expr));

    let expected = and(
        eq(var("result"), logic_fn_call("Some", vec![int(7)])),
        eq(var("result"), logic_fn_call("Some", vec![int(7)])),
    );
    assert_eq!(
        result, expected,
        "instantiation should recurse into nested exists after the outer substitution"
    );
}

#[test]
#[timeout(30000)]
fn instantiate_existential_recurses_through_forall_body() {
    use super::instantiate_embedded_existentials_with_body_witness;
    // Quantified outer structure, including sort/triggers, should be preserved
    // while the inner embedded existential is instantiated against the body result.
    let post = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(exists(
            "y",
            and(
                eq(var("result"), logic_fn_call("Some", vec![var("y")])),
                gt(var("x"), int(0)),
            ),
        )),
        triggers: vec![vec![var("x")]],
    };
    let return_expr = logic_fn_call("Some", vec![int(13)]);

    let result = instantiate_embedded_existentials_with_body_witness(&post, Some(&return_expr));

    let expected = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(and(
            eq(var("result"), logic_fn_call("Some", vec![int(13)])),
            gt(var("x"), int(0)),
        )),
        triggers: vec![vec![var("x")]],
    };
    assert_eq!(
        result, expected,
        "forall metadata should be preserved while its body is recursively instantiated"
    );
}

#[test]
#[timeout(30000)]
fn instantiate_existential_recurses_through_ite_and_unop() {
    use super::instantiate_embedded_existentials_with_body_witness;
    // The recursive rewrite should also traverse control-flow and negation
    // wrappers around an embedded existential, not just plain binops.
    let post = ite(
        bool_expr(true),
        not(exists(
            "y",
            eq(var("result"), logic_fn_call("Some", vec![var("y")])),
        )),
        bool_expr(false),
    );
    let return_expr = logic_fn_call("Some", vec![int(17)]);

    let result = instantiate_embedded_existentials_with_body_witness(&post, Some(&return_expr));

    let expected = ite(
        bool_expr(true),
        not(eq(var("result"), logic_fn_call("Some", vec![int(17)]))),
        bool_expr(false),
    );
    assert_eq!(
        result, expected,
        "ITE and negation wrappers should be preserved while recursively instantiating the inner existential"
    );
}

#[test]
#[timeout(30000)]
fn instantiate_existential_recurses_through_binop() {
    use super::instantiate_embedded_existentials_with_body_witness;
    // Postcondition: P(x) && exists y. result == Some(y)
    // The exists is inside a BinOp — should recurse and instantiate
    let inner_exists = exists(
        "y",
        eq(var("result"), logic_fn_call("Some", vec![var("y")])),
    );
    let post = and(bool_expr(true), inner_exists);
    let return_expr = logic_fn_call("Some", vec![int(7)]);
    let result = instantiate_embedded_existentials_with_body_witness(&post, Some(&return_expr));

    // The BinOp should be preserved, with inner exists instantiated to ground formula
    let expected = and(
        bool_expr(true),
        eq(var("result"), logic_fn_call("Some", vec![int(7)])),
    );
    assert_eq!(
        result, expected,
        "inner existential should be instantiated with y := 7"
    );
}

#[test]
#[timeout(30000)]
fn instantiate_existential_non_existential_expr_unchanged() {
    use super::instantiate_embedded_existentials_with_body_witness;
    // Plain expression should pass through unchanged
    let expr = eq(var("x"), int(42));
    let return_expr = logic_fn_call("Some", vec![int(7)]);
    let result = instantiate_embedded_existentials_with_body_witness(&expr, Some(&return_expr));
    assert_eq!(result, expr, "non-existential expr should be unchanged");
}

#[test]
#[timeout(30000)]
fn instantiate_existential_reverse_equality_pattern() {
    use super::instantiate_embedded_existentials_with_body_witness;
    // Postcondition: exists y. Some(y) == result  (reversed from the typical result == Ctor(y))
    // Body result: Some(42)
    // The find_constructor_matching_var function handles both Ctor(y)==result and result==Ctor(y).
    // This test exercises the Ctor(y)==result branch (axiom_detection.rs:301-310).
    let exists_body = eq(logic_fn_call("Some", vec![var("y")]), var("result"));
    let post = exists("y", exists_body);
    let return_expr = logic_fn_call("Some", vec![int(99)]);
    let result = instantiate_embedded_existentials_with_body_witness(&post, Some(&return_expr));

    let expected = eq(logic_fn_call("Some", vec![int(99)]), var("result"));
    assert_eq!(
        result, expected,
        "reverse equality Ctor(y)==result should also extract witness: y := 99"
    );
}

#[test]
#[timeout(30000)]
fn instantiate_existential_recurses_through_old_wrapper() {
    use super::instantiate_embedded_existentials_with_body_witness;
    // Postcondition: old(exists y. result == Some(y))
    // The Old wrapper should be traversed so the inner existential is instantiated.
    let inner_exists = exists(
        "y",
        eq(var("result"), logic_fn_call("Some", vec![var("y")])),
    );
    let post = PureExpr::Old(Arc::new(inner_exists));
    let return_expr = logic_fn_call("Some", vec![int(5)]);
    let result = instantiate_embedded_existentials_with_body_witness(&post, Some(&return_expr));

    let expected = PureExpr::Old(Arc::new(eq(
        var("result"),
        logic_fn_call("Some", vec![int(5)]),
    )));
    assert_eq!(
        result, expected,
        "Old wrapper should be preserved while inner existential is instantiated"
    );
}

#[test]
#[timeout(30000)]
fn instantiate_existential_recurses_through_final_wrapper() {
    use super::instantiate_embedded_existentials_with_body_witness;
    // Postcondition: final(exists y. result == Some(y))
    // The Final wrapper should be traversed so the inner existential is instantiated.
    let inner_exists = exists(
        "y",
        eq(var("result"), logic_fn_call("Some", vec![var("y")])),
    );
    let post = PureExpr::Final(Arc::new(inner_exists));
    let return_expr = logic_fn_call("Some", vec![int(3)]);
    let result = instantiate_embedded_existentials_with_body_witness(&post, Some(&return_expr));

    let expected = PureExpr::Final(Arc::new(eq(
        var("result"),
        logic_fn_call("Some", vec![int(3)]),
    )));
    assert_eq!(
        result, expected,
        "Final wrapper should be preserved while inner existential is instantiated"
    );
}

#[test]
#[timeout(30000)]
fn instantiate_existential_recurses_through_logic_fn_call_args() {
    use super::instantiate_embedded_existentials_with_body_witness;
    // Postcondition: foo(exists y. result == Some(y))
    // The LogicFnCall args should be traversed so the inner existential is instantiated.
    let inner_exists = exists(
        "y",
        eq(var("result"), logic_fn_call("Some", vec![var("y")])),
    );
    let post = logic_fn_call("foo", vec![inner_exists]);
    let return_expr = logic_fn_call("Some", vec![int(11)]);
    let result = instantiate_embedded_existentials_with_body_witness(&post, Some(&return_expr));

    let expected = logic_fn_call(
        "foo",
        vec![eq(var("result"), logic_fn_call("Some", vec![int(11)]))],
    );
    assert_eq!(
        result, expected,
        "LogicFnCall args should be traversed and inner existential instantiated"
    );
}

#[test]
#[timeout(30000)]
fn instantiate_existential_recurses_through_method_call() {
    use super::instantiate_embedded_existentials_with_body_witness;
    // Postcondition: receiver.method(exists y. result == Some(y))
    // Both receiver and args of MethodCall should be traversed.
    let inner_exists = exists(
        "y",
        eq(var("result"), logic_fn_call("Some", vec![var("y")])),
    );
    let post = method_call_with_args(var("x"), "check", vec![inner_exists.clone()]);
    let return_expr = logic_fn_call("Some", vec![int(23)]);
    let result = instantiate_embedded_existentials_with_body_witness(&post, Some(&return_expr));

    let expected = method_call_with_args(
        var("x"),
        "check",
        vec![eq(var("result"), logic_fn_call("Some", vec![int(23)]))],
    );
    assert_eq!(
        result, expected,
        "MethodCall args should be traversed and inner existential instantiated"
    );
}
