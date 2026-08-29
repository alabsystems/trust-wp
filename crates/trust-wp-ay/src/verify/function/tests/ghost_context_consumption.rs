// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// --- ghost_context consumption tests (#1581) ---

/// Ghost context facts should be asserted in the function verification path.
#[test]
#[timeout(30000)]
fn ghost_context_facts_asserted_in_function_verifier() {
    let ghost_facts = vec![eq(var("x"), PureExpr::Int(42))];
    let ensures = vec![eq(var("result"), PureExpr::Int(42))];
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .ghost_context(Some(&ghost_facts))
            .return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ghost context fact (x == 42) should make result == 42 verify: got {result:?}"
    );
}

/// Without ghost_context, the same postcondition should fail.
#[test]
#[timeout(30000)]
fn without_ghost_context_postcondition_fails() {
    let ensures = vec![eq(var("result"), PureExpr::Int(42))];
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "without ghost context, unconstrained x should fail result == 42: got {result:?}"
    );
}

/// Ghost context with None should be a no-op.
#[test]
#[timeout(30000)]
fn ghost_context_none_is_noop() {
    let ensures = vec![eq(var("result"), PureExpr::Int(42))];
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .ghost_context(None)
            .return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "ghost_context(None) should fail for unconstrained x: got {result:?}"
    );
}

/// Ghost mutation via arithmetic chain: ghost context provides
/// `g == x + 14` and `x == 7`, body returns `g`, postcondition says
/// `result == 21`. This exercises the pattern where ghost mutations
/// establish transitive equalities the solver must compose.
/// Uses Add (not Mul) to stay within QF_LIA — ay-dpll panics on NIA
/// sort mismatches (#1581).
#[test]
#[timeout(30000)]
fn ghost_mutation_transitive_equality_verifies() {
    let ghost_facts = vec![
        eq(
            var("g"),
            PureExpr::BinOp(
                Arc::new(var("x")),
                trust_wp_core::formula::BinOp::Add,
                Arc::new(PureExpr::Int(14)),
            ),
        ),
        eq(var("x"), PureExpr::Int(7)),
    ];

    let ensures = vec![eq(var("result"), PureExpr::Int(21))];
    let body = var("g");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .ghost_context(Some(&ghost_facts))
            .return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ghost transitive equality (g = x+14, x = 7 => g = 21) should verify: got {result:?}"
    );
}

/// Multiple ghost mutations compose: ghost context provides two facts
/// constraining different variables, body combines them.
#[test]
#[timeout(30000)]
fn ghost_multiple_mutations_compose() {
    let ghost_facts = vec![
        eq(var("a"), PureExpr::Int(10)),
        eq(var("b"), PureExpr::Int(20)),
    ];
    let body = PureExpr::BinOp(
        Arc::new(var("a")),
        trust_wp_core::formula::BinOp::Add,
        Arc::new(var("b")),
    );
    let ensures = vec![eq(var("result"), PureExpr::Int(30))];

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .ghost_context(Some(&ghost_facts))
            .return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "composing ghost facts a=10, b=20 with body a+b should verify result==30: got {result:?}"
    );
}

/// Ghost context with three-variable chain: ghost facts establish
/// `a == x + 1` and `b == a + 2`, with precondition `x >= 0`.
/// Body returns `b`, postcondition says `result > x`. The solver
/// must compose all three ghost equalities to conclude b > x.
/// Avoids `Implies` BinOp which triggers ay-dpll sort mismatch (#1581).
#[test]
#[timeout(30000)]
fn ghost_three_variable_chain_verifies() {
    let ghost_facts = vec![
        eq(
            var("a"),
            PureExpr::BinOp(
                Arc::new(var("x")),
                trust_wp_core::formula::BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            ),
        ),
        eq(
            var("b"),
            PureExpr::BinOp(
                Arc::new(var("a")),
                trust_wp_core::formula::BinOp::Add,
                Arc::new(PureExpr::Int(2)),
            ),
        ),
    ];

    let requires = vec![PureExpr::BinOp(
        Arc::new(var("x")),
        trust_wp_core::formula::BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(var("result")),
        trust_wp_core::formula::BinOp::Gt,
        Arc::new(var("x")),
    )];
    let body = var("b");

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .ghost_context(Some(&ghost_facts))
            .return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ghost three-variable chain (a=x+1, b=a+2, x>=0 => b>x) should verify: got {result:?}"
    );
}
