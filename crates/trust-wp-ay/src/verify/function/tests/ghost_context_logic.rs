// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// --- ghost_context + logic_fns interaction tests ---

/// Control test: ghost_context provides `double(x) == 42` and the logic
/// function `double(x) = x + x` is ALSO referenced in ensures. The filter
/// should retain the logic function, and verification should succeed.
#[test]
#[timeout(30000)]
fn ghost_context_with_logic_fn_in_ensures_verifies() {
    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    // ghost: double(x) == 42 (constrains x to 21)
    let ghost_facts = vec![eq(logic_fn_call("double", vec![var("x")]), int(42))];
    // ensures: result == double(x)  (references double — keeps it in filter)
    let ensures = vec![eq(var("result"), logic_fn_call("double", vec![var("x")]))];
    // body returns 42
    let body = int(42);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .ghost_context(Some(&ghost_facts))
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&double_fn))),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ghost(double(x)==42) + ensures(result==double(x)) with body=42 should verify: got {result:?}"
    );
}

/// Soundness probe: ghost_context provides `double(x) == 42` but the
/// logic function `double` is only referenced in ghost — NOT in
/// requires, ensures, or return_expr. If `filter_logic_functions_for_goal`
/// drops the function definition, ghost's `double(x)` becomes an
/// uninterpreted term and cannot constrain `x` to 21. The postcondition
/// `result == 21` with `body = x` would then fail because `x` is
/// unconstrained without the axiom `double(x) = x + x`.
///
/// If the filter correctly includes ghost_context references (via
/// context_exprs at function.rs:584), the axiom is asserted, ghost
/// constrains `x + x == 42` → `x == 21`, and `result == 21` verifies.
#[test]
#[timeout(30000)]
fn ghost_context_logic_fn_only_in_ghost_verifies() {
    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    // ghost: double(x) == 42  (ONLY mention of "double" in any expression)
    let ghost_facts = vec![eq(logic_fn_call("double", vec![var("x")]), int(42))];
    // ensures: result == 21  (does NOT reference "double")
    let ensures = vec![eq(var("result"), int(21))];
    // body returns x — NOT double(x), so filter cannot see "double" from body
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .ghost_context(Some(&ghost_facts))
            .return_expr(Some(&body))
            .logic_fns(Some(std::slice::from_ref(&double_fn))),
    )
    .expect("encoding should succeed");

    // This test REQUIRES the logic function axiom to pass:
    // - Ghost asserts: double(x) == 42
    // - Axiom asserts: double(x) = x + x
    // - Therefore: x + x == 42, i.e., x == 21
    // - Body is x, ensures is result == 21 → verified
    // Without the axiom, double(x) is uninterpreted and x is unconstrained.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ghost(double(x)==42) + axiom(double(x)=x+x) should derive x==21, \
         verifying result==21 with body=x. If this fails, \
         filter_logic_functions_for_goal may not scan ghost_context. Got: {result:?}"
    );
}

// --- ghost_context + multiple ensures interaction tests ---

/// Ghost context combined with multiple ensures clauses. Ghost provides
/// `x == 42` and `x > 0`, ensures checks both `result == 42` AND
/// `result > 0`. Each postcondition is independently verifiable only
/// because the ghost context constrains `x` — testing that ghost facts
/// persist across the postcondition negation loop.
#[test]
#[timeout(30000)]
fn ghost_context_satisfies_multiple_ensures_independently() {
    use trust_wp_core::formula::BinOp;

    let ghost_facts = vec![
        eq(var("x"), int(42)),
        PureExpr::BinOp(Arc::new(var("x")), BinOp::Gt, Arc::new(int(0))),
    ];
    let ensures = vec![
        eq(var("result"), int(42)),
        PureExpr::BinOp(Arc::new(var("result")), BinOp::Gt, Arc::new(int(0))),
    ];
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .ghost_context(Some(&ghost_facts))
            .return_expr(Some(&body)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "ghost(x==42, x>0) + body=x should satisfy both ensures \
         (result==42, result>0). Got: {result:?}"
    );
}
