// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::logic::LogicFnDef;

use super::*;

// -- memoization tests (#2021) ----------------------------------------

/// Helper: build a logic fn definition for tests.
fn make_logic_fn(name: &str, params: Vec<&str>, body: PureExpr) -> LogicFnDef {
    LogicFnDef::new(
        name.to_string(),
        format!("crate::test::{name}"),
        params.into_iter().map(ToString::to_string).collect(),
        body,
    )
}

fn make_recursive_fn(name: &str, params: Vec<&str>, body: PureExpr) -> LogicFnDef {
    let mut lf = make_logic_fn(name, params, body);
    lf.set_is_recursive(true);
    lf
}

fn logic_call(name: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::LogicFnCall {
        name: name.to_string(),
        args,
    }
}

fn int(v: i64) -> PureExpr {
    PureExpr::Int(v)
}

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn binop(l: PureExpr, op: trust_wp_core::formula::BinOp, r: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(l), op, Arc::new(r))
}

fn ite(c: PureExpr, t: PureExpr, e: PureExpr) -> PureExpr {
    PureExpr::Ite(Arc::new(c), Arc::new(t), Arc::new(e))
}

/// Fibonacci body: if n <= 1 then n else fib(n-1) + fib(n-2)
///
/// Without memoization, fib(N) requires O(2^N) recursive calls because
/// both branches of the addition re-evaluate overlapping subproblems.
/// With memoization, each unique fib(k) for k in 0..=N is evaluated
/// exactly once, reducing the total work to O(N).
fn fibonacci_body() -> PureExpr {
    ite(
        binop(var("n"), trust_wp_core::formula::BinOp::Le, int(1)),
        var("n"),
        binop(
            logic_call(
                "fib",
                vec![binop(var("n"), trust_wp_core::formula::BinOp::Sub, int(1))],
            ),
            trust_wp_core::formula::BinOp::Add,
            logic_call(
                "fib",
                vec![binop(var("n"), trust_wp_core::formula::BinOp::Sub, int(2))],
            ),
        ),
    )
}

/// Regression test for #2021: Fibonacci evaluation with memoization.
///
/// fib(20) = 6765. Without memoization this would require ~2^20 calls
/// (~1M) and timeout. With memoization it completes in O(20) unique
/// evaluations.
#[test]
#[timeout(5000)]
fn try_evaluate_recursive_fibonacci_memoized() {
    let fib = make_recursive_fn("fib", vec!["n"], fibonacci_body());
    let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("fib", &fib)]);

    // fib(20) = 6765 — would timeout without memoization
    let result = try_evaluate_recursive(&logic_call("fib", vec![int(20)]), &fns, 25);
    assert_eq!(
        result,
        Some(int(6765)),
        "fib(20) should evaluate to 6765 with memoization (#2021)"
    );
}

/// Verify memoization produces correct results for small Fibonacci values.
#[test]
#[timeout(5000)]
fn try_evaluate_recursive_fibonacci_small_values() {
    let fib = make_recursive_fn("fib", vec!["n"], fibonacci_body());
    let fns: HashMap<&str, &LogicFnDef> = HashMap::from([("fib", &fib)]);

    assert_eq!(
        try_evaluate_recursive(&logic_call("fib", vec![int(0)]), &fns, 10),
        Some(int(0))
    );
    assert_eq!(
        try_evaluate_recursive(&logic_call("fib", vec![int(1)]), &fns, 10),
        Some(int(1))
    );
    assert_eq!(
        try_evaluate_recursive(&logic_call("fib", vec![int(5)]), &fns, 10),
        Some(int(5))
    );
    assert_eq!(
        try_evaluate_recursive(&logic_call("fib", vec![int(10)]), &fns, 15),
        Some(int(55))
    );
}

/// Diamond recursion pattern: f(n) calls g(n-1) and h(n-1), both call base(n-1).
///
/// Without memoization, base(k) is evaluated twice for each level, producing
/// O(2^n) calls. Memoization ensures each base(k) is evaluated once.
#[test]
#[timeout(5000)]
fn try_evaluate_recursive_diamond_memoized() {
    // base(n) = if n <= 0 then 1 else base(n-1) + 1
    let base = make_recursive_fn(
        "base",
        vec!["n"],
        ite(
            binop(var("n"), trust_wp_core::formula::BinOp::Le, int(0)),
            int(1),
            binop(
                logic_call(
                    "base",
                    vec![binop(var("n"), trust_wp_core::formula::BinOp::Sub, int(1))],
                ),
                trust_wp_core::formula::BinOp::Add,
                int(1),
            ),
        ),
    );

    // left(n) = base(n)
    let left = make_logic_fn("left", vec!["n"], logic_call("base", vec![var("n")]));

    // right(n) = base(n)
    let right = make_logic_fn("right", vec!["n"], logic_call("base", vec![var("n")]));

    // top(n) = left(n) + right(n)
    let top = make_logic_fn(
        "top",
        vec!["n"],
        binop(
            logic_call("left", vec![var("n")]),
            trust_wp_core::formula::BinOp::Add,
            logic_call("right", vec![var("n")]),
        ),
    );

    let fns: HashMap<&str, &LogicFnDef> = HashMap::from([
        ("base", &base),
        ("left", &left),
        ("right", &right),
        ("top", &top),
    ]);

    // top(10) = base(10) + base(10) = 11 + 11 = 22
    let result = try_evaluate_recursive(&logic_call("top", vec![int(10)]), &fns, 20);
    assert_eq!(
        result,
        Some(int(22)),
        "diamond pattern should evaluate correctly with memoization"
    );
}

// -- simplify_ground boundary condition tests (#904) -----------------

#[test]
#[timeout(30000)]
fn simplify_ground_add_overflow_returns_unevaluated() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(i64::MAX)),
        trust_wp_core::formula::BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    let result = simplify_ground(&expr);
    // Should NOT panic; should return unevaluated BinOp
    assert!(
        matches!(result, PureExpr::BinOp(_, _, _)),
        "i64::MAX + 1 should return unevaluated BinOp, got: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn simplify_ground_sub_underflow_returns_unevaluated() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(i64::MIN)),
        trust_wp_core::formula::BinOp::Sub,
        Arc::new(PureExpr::Int(1)),
    );
    let result = simplify_ground(&expr);
    assert!(
        matches!(result, PureExpr::BinOp(_, _, _)),
        "i64::MIN - 1 should return unevaluated BinOp, got: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn simplify_ground_mul_overflow_returns_unevaluated() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(i64::MAX)),
        trust_wp_core::formula::BinOp::Mul,
        Arc::new(PureExpr::Int(2)),
    );
    let result = simplify_ground(&expr);
    assert!(
        matches!(result, PureExpr::BinOp(_, _, _)),
        "i64::MAX * 2 should return unevaluated BinOp, got: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn simplify_ground_div_min_by_neg_one_returns_unevaluated() {
    // i64::MIN / -1 overflows (result would be i64::MAX + 1)
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(i64::MIN)),
        trust_wp_core::formula::BinOp::Div,
        Arc::new(PureExpr::Int(-1)),
    );
    let result = simplify_ground(&expr);
    assert!(
        matches!(result, PureExpr::BinOp(_, _, _)),
        "i64::MIN / -1 should return unevaluated BinOp, got: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn simplify_ground_mod_min_by_neg_one_returns_unevaluated() {
    // i64::MIN % -1 overflows
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(i64::MIN)),
        trust_wp_core::formula::BinOp::Mod,
        Arc::new(PureExpr::Int(-1)),
    );
    let result = simplify_ground(&expr);
    assert!(
        matches!(result, PureExpr::BinOp(_, _, _)),
        "i64::MIN % -1 should return unevaluated BinOp, got: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn simplify_ground_neg_min_returns_unevaluated() {
    let expr = PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Neg,
        Arc::new(PureExpr::Int(i64::MIN)),
    );
    let result = simplify_ground(&expr);
    assert!(
        matches!(result, PureExpr::UnOp(_, _)),
        "-(i64::MIN) should return unevaluated UnOp, got: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn simplify_ground_normal_arithmetic_still_folds() {
    // Verify normal cases still work after checked arithmetic change
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(10)),
        trust_wp_core::formula::BinOp::Add,
        Arc::new(PureExpr::Int(20)),
    );
    assert_eq!(simplify_ground(&expr), PureExpr::Int(30));

    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(100)),
        trust_wp_core::formula::BinOp::Div,
        Arc::new(PureExpr::Int(3)),
    );
    assert_eq!(simplify_ground(&expr), PureExpr::Int(33));

    let expr = PureExpr::UnOp(
        trust_wp_core::formula::UnOp::Neg,
        Arc::new(PureExpr::Int(42)),
    );
    assert_eq!(simplify_ground(&expr), PureExpr::Int(-42));
}

// -- Euclidean div/mod semantics tests (#2191) ----------------------

#[test]
#[timeout(30000)]
fn simplify_ground_mod_negative_dividend_uses_euclidean_semantics() {
    // SMT-LIB mod is Euclidean: (-5) mod 2 = 1 (always non-negative)
    // Rust checked_rem would give -1 (sign of dividend)
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(-5)),
        trust_wp_core::formula::BinOp::Mod,
        Arc::new(PureExpr::Int(2)),
    );
    assert_eq!(
        simplify_ground(&expr),
        PureExpr::Int(1),
        "(-5) mod 2 should be 1 (Euclidean), not -1 (Rust rem)"
    );
}

#[test]
#[timeout(30000)]
fn simplify_ground_div_negative_dividend_uses_euclidean_semantics() {
    // SMT-LIB div is Euclidean: (-7) div 2 = -4 (floor toward -∞)
    // Rust checked_div would give -3 (truncation toward 0)
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(-7)),
        trust_wp_core::formula::BinOp::Div,
        Arc::new(PureExpr::Int(2)),
    );
    assert_eq!(
        simplify_ground(&expr),
        PureExpr::Int(-4),
        "(-7) div 2 should be -4 (Euclidean floor), not -3 (Rust truncation)"
    );
}

#[test]
#[timeout(30000)]
fn simplify_ground_mod_negative_divisor_uses_euclidean_semantics() {
    // (-5) mod (-3): Euclidean gives 1, Rust rem gives -2
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(-5)),
        trust_wp_core::formula::BinOp::Mod,
        Arc::new(PureExpr::Int(-3)),
    );
    assert_eq!(
        simplify_ground(&expr),
        PureExpr::Int(1),
        "(-5) mod (-3) should be 1 (Euclidean), not -2 (Rust rem)"
    );
}

#[test]
#[timeout(30000)]
fn simplify_ground_div_positive_operands_unchanged() {
    // Positive operands: Euclidean = truncation, no difference
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(7)),
        trust_wp_core::formula::BinOp::Div,
        Arc::new(PureExpr::Int(2)),
    );
    assert_eq!(simplify_ground(&expr), PureExpr::Int(3));
}

#[test]
#[timeout(30000)]
fn simplify_ground_mod_positive_operands_unchanged() {
    // Positive operands: Euclidean = Rust rem, no difference
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Int(7)),
        trust_wp_core::formula::BinOp::Mod,
        Arc::new(PureExpr::Int(2)),
    );
    assert_eq!(simplify_ground(&expr), PureExpr::Int(1));
}

#[test]
#[timeout(30000)]
fn simplify_ground_reuses_shared_children_when_not_foldable() {
    let left = Arc::new(PureExpr::Var("x".to_string(), None));
    let right = Arc::new(PureExpr::Var("y".to_string(), None));
    let expr = PureExpr::BinOp(
        Arc::clone(&left),
        trust_wp_core::formula::BinOp::Add,
        Arc::clone(&right),
    );

    let result = simplify_ground(&expr);

    match result {
        PureExpr::BinOp(new_left, trust_wp_core::formula::BinOp::Add, new_right) => {
            assert!(
                Arc::ptr_eq(&new_left, &left),
                "simplify_ground should preserve unchanged left subtree Arc"
            );
            assert!(
                Arc::ptr_eq(&new_right, &right),
                "simplify_ground should preserve unchanged right subtree Arc"
            );
        }
        other => panic!("expected non-folded binop, got: {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn try_evaluate_recursive_reuses_shared_children_when_not_foldable() {
    let fns = std::collections::HashMap::new();
    let left = Arc::new(PureExpr::Int(i64::MAX));
    let right = Arc::new(PureExpr::Int(1));
    let expr = PureExpr::BinOp(
        Arc::clone(&left),
        trust_wp_core::formula::BinOp::Add,
        Arc::clone(&right),
    );

    let result =
        try_evaluate_recursive(&expr, &fns, 10).expect("ground overflow should stay unevaluated");

    match result {
        PureExpr::BinOp(new_left, trust_wp_core::formula::BinOp::Add, new_right) => {
            assert!(
                Arc::ptr_eq(&new_left, &left),
                "try_evaluate_recursive should preserve unchanged left subtree Arc"
            );
            assert!(
                Arc::ptr_eq(&new_right, &right),
                "try_evaluate_recursive should preserve unchanged right subtree Arc"
            );
        }
        other => panic!("expected non-folded binop, got: {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn try_evaluate_recursive_reuses_shared_operand_when_neg_overflows() {
    let fns = std::collections::HashMap::new();
    let operand = Arc::new(PureExpr::Int(i64::MIN));
    let expr = PureExpr::UnOp(trust_wp_core::formula::UnOp::Neg, Arc::clone(&operand));

    let result =
        try_evaluate_recursive(&expr, &fns, 10).expect("ground overflow should stay unevaluated");

    match result {
        PureExpr::UnOp(trust_wp_core::formula::UnOp::Neg, new_operand) => {
            assert!(
                Arc::ptr_eq(&new_operand, &operand),
                "try_evaluate_recursive should preserve unchanged operand Arc"
            );
        }
        other => panic!("expected non-folded negation, got: {other:?}"),
    }
}

// -- Match-constructor reduction tests (#3318) -----------------------

/// Helper: build a MatchArm.
fn match_arm(pattern: Pattern, body: PureExpr) -> MatchArm {
    MatchArm { pattern, body }
}

/// Helper: build a nullary constructor pattern (e.g., `None`).
fn ctor_pattern(name: &str) -> Pattern {
    Pattern::Constructor {
        name: name.to_string(),
        inner: None,
    }
}

/// Helper: build a unary constructor pattern (e.g., `Some(v)`).
fn ctor_pattern_with(name: &str, inner: Pattern) -> Pattern {
    Pattern::Constructor {
        name: name.to_string(),
        inner: Some(Box::new(inner)),
    }
}

/// Helper: build a Match expression.
fn match_expr(scrutinee: PureExpr, arms: Vec<MatchArm>) -> PureExpr {
    PureExpr::Match {
        scrutinee: Arc::new(scrutinee),
        arms,
    }
}

/// Match with nullary constructor scrutinee: `match None { Some(v) => v, None => 42 }`
/// Should reduce to 42.
#[test]
#[timeout(5000)]
fn simplify_ground_match_nullary_constructor_reduces() {
    let expr = match_expr(
        logic_call("None", vec![]),
        vec![
            match_arm(
                ctor_pattern_with("Some", Pattern::Binding("v".to_string())),
                var("v"),
            ),
            match_arm(ctor_pattern("None"), int(42)),
        ],
    );
    let result = simplify_ground(&expr);
    assert_eq!(
        result,
        int(42),
        "match None against None arm should reduce to 42"
    );
}

/// Match with unary constructor scrutinee: `match Some(7) { Some(v) => v + 1, None => 0 }`
/// The match reduction substitutes v=7 producing `7 + 1`. Since rewrite_bottom_up
/// processes children before the parent, the substituted expression needs another
/// simplify pass to fold the arithmetic. Verify the reduction itself is correct.
#[test]
#[timeout(5000)]
fn simplify_ground_match_unary_constructor_reduces_with_binding() {
    let expr = match_expr(
        logic_call("Some", vec![int(7)]),
        vec![
            match_arm(
                ctor_pattern_with("Some", Pattern::Binding("v".to_string())),
                binop(var("v"), trust_wp_core::formula::BinOp::Add, int(1)),
            ),
            match_arm(ctor_pattern("None"), int(0)),
        ],
    );
    let result = simplify_ground(&expr);
    // First pass reduces match to `7 + 1` (substitution happened).
    assert_eq!(
        result,
        binop(int(7), trust_wp_core::formula::BinOp::Add, int(1)),
        "match Some(7) should substitute v=7 producing 7+1"
    );
    // A second simplify pass folds the arithmetic.
    let fully_folded = simplify_ground(&result);
    assert_eq!(
        fully_folded,
        int(8),
        "second simplify pass should fold 7+1=8"
    );
}

/// Match with Deref-wrapped constructor: `match *None() { Some(v) => v, None => 99 }`
/// Should strip Deref and reduce to 99. This is the critical proof_assert case.
#[test]
#[timeout(5000)]
fn simplify_ground_match_deref_constructor_reduces() {
    let expr = match_expr(
        PureExpr::Deref(Arc::new(logic_call("None", vec![]))),
        vec![
            match_arm(
                ctor_pattern_with("Some", Pattern::Binding("v".to_string())),
                var("v"),
            ),
            match_arm(ctor_pattern("None"), int(99)),
        ],
    );
    let result = simplify_ground(&expr);
    assert_eq!(
        result,
        int(99),
        "match *None() should strip Deref and reduce to 99 (#3318)"
    );
}

/// Match with double-Deref: `match **Some(5) { Some(v) => v, None => 0 }`
/// Should strip both Deref layers and reduce to 5.
#[test]
#[timeout(5000)]
fn simplify_ground_match_double_deref_constructor_reduces() {
    let expr = match_expr(
        PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(logic_call(
            "Some",
            vec![int(5)],
        ))))),
        vec![
            match_arm(
                ctor_pattern_with("Some", Pattern::Binding("v".to_string())),
                var("v"),
            ),
            match_arm(ctor_pattern("None"), int(0)),
        ],
    );
    let result = simplify_ground(&expr);
    assert_eq!(
        result,
        int(5),
        "match **Some(5) should strip both Deref layers"
    );
}

/// Match where the first arm does not match and the second does:
/// `match Some(1) { None => 0, Some(v) => v }`
/// Should skip None arm and reduce via Some arm.
#[test]
#[timeout(5000)]
fn simplify_ground_match_skips_non_matching_arm() {
    let expr = match_expr(
        logic_call("Some", vec![int(1)]),
        vec![
            match_arm(ctor_pattern("None"), int(0)),
            match_arm(
                ctor_pattern_with("Some", Pattern::Binding("v".to_string())),
                var("v"),
            ),
        ],
    );
    let result = simplify_ground(&expr);
    assert_eq!(result, int(1), "should skip non-matching None arm");
}

/// Match with wildcard fallback: `match Ok(3) { Err(e) => e, _ => 100 }`
/// Should fall through to wildcard arm.
#[test]
#[timeout(5000)]
fn simplify_ground_match_wildcard_fallback() {
    let expr = match_expr(
        logic_call("Ok", vec![int(3)]),
        vec![
            match_arm(
                ctor_pattern_with("Err", Pattern::Binding("e".to_string())),
                var("e"),
            ),
            match_arm(Pattern::Wildcard, int(100)),
        ],
    );
    let result = simplify_ground(&expr);
    assert_eq!(result, int(100), "should fall through to wildcard arm");
}

/// Match with binding fallback: `match Ok(3) { Err(e) => e, x => x }`
/// Should fall through to binding arm and substitute x = Ok(3).
#[test]
#[timeout(5000)]
fn simplify_ground_match_binding_fallback() {
    let expr = match_expr(
        logic_call("Ok", vec![int(3)]),
        vec![
            match_arm(
                ctor_pattern_with("Err", Pattern::Binding("e".to_string())),
                var("e"),
            ),
            match_arm(Pattern::Binding("x".to_string()), var("x")),
        ],
    );
    let result = simplify_ground(&expr);
    assert_eq!(
        result,
        logic_call("Ok", vec![int(3)]),
        "binding fallback should substitute x = Ok(3)"
    );
}

/// Alias patterns bind the whole constructor and still recurse into the
/// inner pattern: `whole @ Some(v)`.
#[test]
#[timeout(5000)]
fn simplify_ground_match_alias_constructor_binds_whole_and_inner() {
    let expr = match_expr(
        logic_call("Some", vec![int(9)]),
        vec![match_arm(
            Pattern::Alias {
                alias: "whole".to_string(),
                pattern: Box::new(ctor_pattern_with("Some", Pattern::Binding("v".to_string()))),
            },
            logic_call("Pair", vec![var("whole"), var("v")]),
        )],
    );
    let result = simplify_ground(&expr);
    assert_eq!(
        result,
        logic_call("Pair", vec![logic_call("Some", vec![int(9)]), int(9)])
    );
}

/// Alias catch-alls bind the entire constructor value.
#[test]
#[timeout(5000)]
fn simplify_ground_match_alias_wildcard_binds_whole_constructor() {
    let expr = match_expr(
        logic_call("Ok", vec![int(3)]),
        vec![match_arm(
            Pattern::Alias {
                alias: "whole".to_string(),
                pattern: Box::new(Pattern::Wildcard),
            },
            var("whole"),
        )],
    );
    let result = simplify_ground(&expr);
    assert_eq!(result, logic_call("Ok", vec![int(3)]));
}

/// Match with variable scrutinee should NOT reduce (not a constructor).
#[test]
#[timeout(5000)]
fn simplify_ground_match_variable_scrutinee_no_reduction() {
    let expr = match_expr(
        var("x"),
        vec![
            match_arm(ctor_pattern("None"), int(0)),
            match_arm(
                ctor_pattern_with("Some", Pattern::Binding("v".to_string())),
                var("v"),
            ),
        ],
    );
    let result = simplify_ground(&expr);
    // Should return the match expression unchanged (no reduction possible)
    assert!(
        matches!(result, PureExpr::Match { .. }),
        "variable scrutinee should not reduce, got: {result:?}"
    );
}

/// Match with literal pattern: `match Ok(42) { Ok(42) => true, _ => false }`
/// The inner pattern is a Literal(42) that should match exactly.
#[test]
#[timeout(5000)]
fn simplify_ground_match_literal_inner_pattern() {
    let expr = match_expr(
        logic_call("Ok", vec![int(42)]),
        vec![
            match_arm(
                ctor_pattern_with("Ok", Pattern::Literal(int(42))),
                PureExpr::Bool(true),
            ),
            match_arm(Pattern::Wildcard, PureExpr::Bool(false)),
        ],
    );
    let result = simplify_ground(&expr);
    assert_eq!(
        result,
        PureExpr::Bool(true),
        "literal 42 should match Ok(42)"
    );
}

/// Match with non-matching literal: `match Ok(99) { Ok(42) => true, _ => false }`
/// Should fall through to wildcard since 99 != 42.
#[test]
#[timeout(5000)]
fn simplify_ground_match_literal_mismatch_falls_through() {
    let expr = match_expr(
        logic_call("Ok", vec![int(99)]),
        vec![
            match_arm(
                ctor_pattern_with("Ok", Pattern::Literal(int(42))),
                PureExpr::Bool(true),
            ),
            match_arm(Pattern::Wildcard, PureExpr::Bool(false)),
        ],
    );
    let result = simplify_ground(&expr);
    assert_eq!(
        result,
        PureExpr::Bool(false),
        "literal 42 should not match Ok(99), falls to wildcard"
    );
}

/// Nested constructor pattern: `match Some(Ok(5)) { Some(Ok(v)) => v, _ => 0 }`
#[test]
#[timeout(5000)]
fn simplify_ground_match_nested_constructor_pattern() {
    let expr = match_expr(
        logic_call("Some", vec![logic_call("Ok", vec![int(5)])]),
        vec![
            match_arm(
                ctor_pattern_with(
                    "Some",
                    Pattern::Constructor {
                        name: "Ok".to_string(),
                        inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                    },
                ),
                var("v"),
            ),
            match_arm(Pattern::Wildcard, int(0)),
        ],
    );
    let result = simplify_ground(&expr);
    assert_eq!(result, int(5), "nested Some(Ok(5)) should bind v=5");
}

/// The try_reduce_match_constructor function directly: verify it returns
/// None for non-constructor scrutinee.
#[test]
fn try_reduce_match_constructor_returns_none_for_var() {
    use super::try_reduce_match_constructor;
    let arms = vec![match_arm(ctor_pattern("None"), int(0))];
    assert_eq!(
        try_reduce_match_constructor(&var("x"), &arms),
        None,
        "variable scrutinee should return None"
    );
}

/// Verify the Deref-stripping works through try_reduce_match_constructor.
#[test]
fn try_reduce_match_constructor_strips_deref() {
    use super::try_reduce_match_constructor;
    let scrutinee = PureExpr::Deref(Arc::new(logic_call("None", vec![])));
    let arms = vec![
        match_arm(
            ctor_pattern_with("Some", Pattern::Binding("v".to_string())),
            var("v"),
        ),
        match_arm(ctor_pattern("None"), int(77)),
    ];
    assert_eq!(
        try_reduce_match_constructor(&scrutinee, &arms),
        Some(int(77)),
        "Deref(None) should match None arm"
    );
}
