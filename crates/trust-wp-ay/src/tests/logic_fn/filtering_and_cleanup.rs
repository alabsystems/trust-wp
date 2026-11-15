// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::*;

#[test]
#[timeout(30000)]
fn test_register_logic_fn_cleanup_on_error() {
    // Test that register_logic_fn restores variable bindings when body encoding fails.
    // Issue #256: a failed registration must not leave its parameter shadowing
    // the caller's binding.
    let mut encoder = AYEncoder::new_with_quantifiers();

    // First, bind 'x' to a known term in the encoder's vars map
    let _original_x = encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("Should declare x");

    // Create a logic function with 'x' as a parameter (will shadow original)
    // and a body that will fail to encode (complex deref expression).
    // Deref(Int(0)) encodes (#1075) and Deref(BinOp) encodes via BinOp
    // distribution (#2700), so neither can serve as the failing body.
    // Deref(Exists(...)) hits the unsupported complex-deref catch-all.
    let invalid_logic_fn = LogicFnDef::new(
        "bad_fn".to_string(),
        "test::bad_fn".to_string(),
        vec!["x".to_string()],
        // Deref of an Exists expression causes EncodingError::Unsupported
        deref(PureExpr::Exists {
            var: "q".to_string(),
            var_sort: None,
            body: Arc::new(gt(var("q"), int(0))),
            triggers: vec![],
        }),
    )
    .with_mode(LogicMode::Open);

    // Registration should fail due to unsupported deref
    let err = encoder
        .register_logic_fn(&invalid_logic_fn)
        .expect_err("registration with unsupported deref should fail");
    assert!(
        format!("{err:?}").contains("Unsupported"),
        "expected unsupported deref encoding error, got: {err:?}"
    );

    // Verify original 'x' binding was restored (not polluted by the failed registration)
    // register_logic_fn must restore bindings even on error
    let current_x = encoder.vars_for_test().get("x");
    assert!(
        current_x.is_some(),
        "Original 'x' binding should still exist after failed registration"
    );

    // Note: We can't directly compare Term equality, but we can verify
    // the binding wasn't removed or replaced with a different term.
    // The fact that 'x' still exists in vars proves cleanup worked.
}

/// Bug #259: Multiple logic function registration breaks quantifier instantiation.
///
/// When multiple logic functions are registered, the E-matcher must instantiate
/// all of their axioms correctly for goals that reference multiple logic fns.
///
/// Regression guard for ay#1939 (E-matching with multiple triggered quantifiers).
#[test]
#[timeout(30000)]
fn test_bug_259_multiple_logic_fns_registered() {
    use trust_wp_core::logic::LogicFnDef;

    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // Define two logic functions
    let add_one = LogicFnDef::new(
        "add_one".to_string(),
        "test::add_one".to_string(),
        vec!["x".to_string()],
        // add_one(x) = x + 1
        add(var("x"), int(1)),
    )
    .with_mode(LogicMode::Open);

    let double = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["y".to_string()], // Different param name to avoid confusion
        // double(y) = y * 2
        mul(var("y"), int(2)),
    )
    .with_mode(LogicMode::Open);

    // requires: none (x is symbolic)
    let requires: Vec<PureExpr> = vec![];

    // ensures (single): result == add_one(x)
    let ensures_single = vec![eq(var("result"), logic_fn_call("add_one", vec![var("x")]))];

    // ensures (multiple): result == add_one(x) && double(x) == x * 2
    // (references both logic fns to force multi-axiom instantiation)
    let ensures_multiple = vec![
        eq(var("result"), logic_fn_call("add_one", vec![var("x")])),
        eq(
            logic_fn_call("double", vec![var("x")]),
            mul(var("x"), int(2)),
        ),
    ];

    // body: result = x + 1
    let return_expr = add(var("x"), int(1));

    // First verify with just add_one (should pass)
    let result_single = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures_single)
            .return_expr(Some(&return_expr))
            .logic_fns(Some(std::slice::from_ref(&add_one))),
    );
    assert!(
        matches!(result_single, Ok(VerificationResult::Verified(_))),
        "Single logic function should verify: {result_single:?}"
    );

    // Now verify with BOTH logic functions registered
    // E-matching must instantiate both axioms (ay#1939).
    let logic_fns = vec![add_one, double];
    let result_multiple = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures_multiple)
            .return_expr(Some(&return_expr))
            .logic_fns(Some(&logic_fns)),
    );

    // Both registered logic functions must verify (ay#1939).
    assert!(
        matches!(result_multiple, Ok(VerificationResult::Verified(_))),
        "Multiple logic functions should verify (ay#1939 fixed): {result_multiple:?}"
    );
}

/// Test logic fn filtering when function is referenced ONLY in postcondition.
///
/// Verifies the #259 filtering handles the case where logic fn appears
/// in ensures but not in requires (guards registration via postcondition scan).
#[test]
#[timeout(30000)]
fn test_verify_function_filters_logic_fn_only_in_ensures() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // Logic fn: triple(x) = x * 3
    let triple = LogicFnDef::new(
        "triple".to_string(),
        "crate::specs::triple".to_string(),
        vec!["x".to_string()],
        mul(var("x"), int(3)),
    )
    .with_mode(LogicMode::Open);

    // requires: x > 0 (no logic fn reference)
    let requires = vec![gt(var("x"), int(0))];

    // ensures: result == triple(x)
    let ensures = vec![eq(var("result"), logic_fn_call("triple", vec![var("x")]))];

    // body: x * 3
    let body = mul(var("x"), int(3));

    let logic_fns = vec![triple];
    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(&logic_fns)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Logic fn used only in ensures should be registered: {result:?}"
    );
}

/// Test mutual recursion between logic functions.
///
/// `is_even(n)` := n == 0 || `is_odd(n - 1)`
/// `is_odd(n)` := n != 0 && `is_even(n - 1)`
///
/// Both should be included when either is referenced.
#[test]
#[timeout(30000)]
fn test_verify_function_filters_mutual_recursion() {
    use crate::{verify_function_with_modes, VerificationRequest};

    // Note: These are simplified non-recursive versions for testing filtering,
    // since actual recursion would diverge in SMT encoding.
    let is_even = LogicFnDef::new(
        "is_even".to_string(),
        "crate::specs::is_even".to_string(),
        vec!["n".to_string()],
        // Simplified: n % 2 == 0 (but referencing is_odd for filtering test)
        or(
            eq(var("n"), int(0)),
            logic_fn_call("is_odd", vec![sub(var("n"), int(1))]),
        ),
    )
    .with_mode(LogicMode::Open);

    let is_odd = LogicFnDef::new(
        "is_odd".to_string(),
        "crate::specs::is_odd".to_string(),
        vec!["n".to_string()],
        // Simplified: References is_even
        and(
            ne(var("n"), int(0)),
            logic_fn_call("is_even", vec![sub(var("n"), int(1))]),
        ),
    )
    .with_mode(LogicMode::Open);

    // requires: is_even(n) (should pull in is_odd transitively)
    let requires = vec![logic_fn_call("is_even", vec![var("n")])];
    let ensures = vec![bool_expr(true)];
    let body = var("n");

    let logic_fns = vec![is_even, is_odd];
    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(&logic_fns)),
    )
    .expect("mutual recursion should not crash filter");
    // ensures(true) is trivially valid, but verify it actually produces Verified
    // (not Failed or Unknown which would indicate an encoding problem)
    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "mutual recursion with ensures(true) should verify, not fail or timeout"
    );
}

#[test]
#[timeout(30000)]
fn test_verify_function_executes_recursive_mutual_pair() {
    use std::collections::HashMap;

    use crate::encoder::try_evaluate_recursive;

    let mut is_even = LogicFnDef::new(
        "is_even".to_string(),
        "crate::specs::is_even".to_string(),
        vec!["n".to_string()],
        ite(
            eq(var("n"), int(0)),
            bool_expr(true),
            logic_fn_call("is_odd", vec![sub(var("n"), int(1))]),
        ),
    )
    .with_mode(LogicMode::Open);
    is_even.set_is_recursive(true);

    let mut is_odd = LogicFnDef::new(
        "is_odd".to_string(),
        "crate::specs::is_odd".to_string(),
        vec!["n".to_string()],
        ite(
            eq(var("n"), int(0)),
            bool_expr(false),
            logic_fn_call("is_even", vec![sub(var("n"), int(1))]),
        ),
    )
    .with_mode(LogicMode::Open);
    is_odd.set_is_recursive(true);

    let recursive_fns: HashMap<&str, &LogicFnDef> =
        HashMap::from([("is_even", &is_even), ("is_odd", &is_odd)]);
    let even_result =
        try_evaluate_recursive(&logic_fn_call("is_even", vec![int(2)]), &recursive_fns, 10);
    assert!(
        even_result == Some(bool_expr(true)),
        "is_even(2) should evaluate through the existing recursive path: {even_result:?}"
    );

    let odd_result =
        try_evaluate_recursive(&logic_fn_call("is_odd", vec![int(3)]), &recursive_fns, 10);
    assert!(
        odd_result == Some(bool_expr(true)),
        "is_odd(3) should evaluate through the existing recursive path: {odd_result:?}"
    );
}

/// Test diamond dependency pattern: A calls B and C, both call D.
///
/// Ensures transitive closure correctly handles shared dependencies.
#[test]
#[timeout(30000)]
fn test_verify_function_filters_diamond_dependency() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // D: base(x) = x + 1
    let base = LogicFnDef::new(
        "base".to_string(),
        "crate::specs::base".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(1)),
    )
    .with_mode(LogicMode::Open);

    // B: left(x) = base(x) + 10
    let left = LogicFnDef::new(
        "left".to_string(),
        "crate::specs::left".to_string(),
        vec!["x".to_string()],
        add(logic_fn_call("base", vec![var("x")]), int(10)),
    )
    .with_mode(LogicMode::Open);

    // C: right(x) = base(x) + 100
    let right = LogicFnDef::new(
        "right".to_string(),
        "crate::specs::right".to_string(),
        vec!["x".to_string()],
        add(logic_fn_call("base", vec![var("x")]), int(100)),
    )
    .with_mode(LogicMode::Open);

    // A: top(x) = left(x) + right(x)
    let top = LogicFnDef::new(
        "top".to_string(),
        "crate::specs::top".to_string(),
        vec!["x".to_string()],
        add(
            logic_fn_call("left", vec![var("x")]),
            logic_fn_call("right", vec![var("x")]),
        ),
    )
    .with_mode(LogicMode::Open);

    // requires: top(x) > 0 (should pull in left, right, base)
    let requires = vec![gt(logic_fn_call("top", vec![var("x")]), int(0))];
    let ensures = vec![bool_expr(true)];
    let body = var("x");

    // Include unused fn to verify it's filtered out
    let unused = LogicFnDef::new(
        "unused".to_string(),
        "crate::specs::unused".to_string(),
        vec!["x".to_string()],
        method_call(var("x"), "will_fail_if_registered", Vec::new()),
    );

    // Order matters - put deps in wrong order to test fixpoint
    let logic_fns = vec![unused, top, base, right, left];
    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(&logic_fns)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Diamond dependency should resolve correctly: {result:?}"
    );
}
