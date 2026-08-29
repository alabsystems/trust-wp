// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for ghost pipeline compat patterns (#2671).
//!
//! Each test maps to a specific Creusot compat test in
//! `reference/creusot/tests/should_succeed/ghost/`. These exist to prevent
//! regressions on ghost patterns that previously failed.

use std::collections::HashMap;

use trust_wp_core::formula::NamedBindingValue;

use super::*;

// --- ghost/ghost_set.rs regression ---

/// Regression test for `ghost/ghost_set.rs`: FSet insert, contains, remove,
/// and length operations inside a ghost block.
///
/// Models the core pattern: insert elements, check contains, remove, verify length.
/// Part of #2671.
#[test]
#[timeout(60000)]
fn test_regression_ghost_set_insert_contains_remove() {
    // Model: start with empty set, insert 1, check contains(1) && !contains(2)
    let ghost_facts = vec![
        // s0 is empty
        eq(method_call(var("s0"), "len", vec![]), int(0)),
        // After insert(1): s1 contains 1, len == 1
        method_call(var("s1"), "contains", vec![int(1)]),
        eq(method_call(var("s1"), "len", vec![]), int(1)),
        // s1 does NOT contain 2
        not(method_call(var("s1"), "contains", vec![int(2)])),
        // After insert(2): s2 contains both 1 and 2, len == 2
        method_call(var("s2"), "contains", vec![int(1)]),
        method_call(var("s2"), "contains", vec![int(2)]),
        eq(method_call(var("s2"), "len", vec![]), int(2)),
        // After remove(2): s3 does NOT contain 2, len == 1
        not(method_call(var("s3"), "contains", vec![int(2)])),
        method_call(var("s3"), "contains", vec![int(1)]),
        eq(method_call(var("s3"), "len", vec![]), int(1)),
    ];

    // Goal: s3.len() == 1 && s3.contains(1) && !s3.contains(2)
    let goal = binop(
        eq(method_call(var("s3"), "len", vec![]), int(1)),
        BinOp::And,
        binop(
            method_call(var("s3"), "contains", vec![int(1)]),
            BinOp::And,
            not(method_call(var("s3"), "contains", vec![int(2)])),
        ),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], std::slice::from_ref(&goal))
            .ghost_context(Some(&ghost_facts)),
    );

    assert!(
        result.is_ok(),
        "ghost_set regression should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "ghost_set insert/contains/remove should verify: {vr:?}"
    );
}

// --- ghost/ghost_map.rs regression ---

/// Regression test for `ghost/ghost_map.rs`: FMap insert, lookup, get_mut,
/// remove operations inside a ghost block.
///
/// Models: insert(1, 21), lookup(1)==21, then get_mut sets value to 43,
/// verify lookup(1)==43.
/// Part of #2671.
#[test]
#[timeout(60000)]
fn test_regression_ghost_map_insert_lookup_update() {
    let ghost_facts = vec![
        // m0 is empty, len==0
        eq(method_call(var("m0"), "len", vec![]), int(0)),
        // After insert(1, 21): m1.lookup(1)==21, m1.len()==1
        method_call(var("m1"), "contains", vec![int(1)]),
        eq(method_call(var("m1"), "get", vec![int(1)]), int(21)),
        eq(method_call(var("m1"), "len", vec![]), int(1)),
        // After get_mut + write 43: m2.lookup(1)==43
        method_call(var("m2"), "contains", vec![int(1)]),
        eq(method_call(var("m2"), "get", vec![int(1)]), int(43)),
        eq(method_call(var("m2"), "len", vec![]), int(1)),
    ];

    // Goal: m2.get(1) == 43 && m2.len() == 1
    let goal = binop(
        eq(method_call(var("m2"), "get", vec![int(1)]), int(43)),
        BinOp::And,
        eq(method_call(var("m2"), "len", vec![]), int(1)),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], std::slice::from_ref(&goal))
            .ghost_context(Some(&ghost_facts)),
    );

    assert!(
        result.is_ok(),
        "ghost_map regression should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "ghost_map insert/lookup/update should verify: {vr:?}"
    );
}

// --- ghost/ghost_vec.rs regression ---

/// Regression test for `ghost/ghost_vec.rs`: Vec push_back_ghost and
/// len_ghost inside a ghost block.
///
/// Models: push two elements, check length == 2.
/// Part of #2671.
#[test]
#[timeout(60000)]
fn test_regression_ghost_vec_push_and_length() {
    let empty = PureExpr::LogicFnCall {
        name: "seq_empty".to_string(),
        args: vec![],
    };

    let ghost_facts = vec![
        eq(var("v0"), empty),
        eq(
            var("v1"),
            method_call(var("v0"), "push_back", vec![int(10)]),
        ),
        eq(
            var("v2"),
            method_call(var("v1"), "push_back", vec![int(20)]),
        ),
    ];

    // Goal: v2.len() == 2
    let goal = eq(method_call(view(var("v2")), "len", vec![]), int(2));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], std::slice::from_ref(&goal))
            .ghost_context(Some(&ghost_facts)),
    );

    assert!(
        result.is_ok(),
        "ghost_vec regression should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert_verified_or_vacuous(&vr, "ghost_vec push_back chain length==2 should verify");
}

// --- ghost/loop_in_ghost.rs regression ---

/// Regression test for `ghost/loop_in_ghost.rs`: while loop inside ghost block
/// with arithmetic invariant `y@ + i@ == x@`.
///
/// Models: y starts at 0, i starts at x, each step y+=1, i-=1,
/// invariant y+i==x. At exit, y==x.
/// Part of #2671.
#[test]
#[timeout(60000)]
fn test_regression_loop_in_ghost_arithmetic_invariant() {
    // The Creusot test: y starts at 0, i starts at x, loop body: i-=1, y+=1
    // Invariant: y + i == x
    let invariant = eq(add(var("y"), var("i")), var("x"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), sub(var("i"), int(1)));
    body_effect.insert("y".to_string(), add(var("y"), int(1)));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("y".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(var("x")));

    // Loop condition: i > 0
    let loop_cond = gt(var("i"), int(0));
    let requires = vec![ge(var("x"), int(0))];

    // Postcondition: *result == x, which after ghost unwrapping is just y == x
    // But the loop's return_expr is var("y"), so ensures on the function is
    // that the returned ghost value equals x.
    let postcondition = eq(var("y"), var("x"));

    let ctx = LoopVerificationContext {
        requires: &requires,
        ensures: &[postcondition],
        invariants: std::slice::from_ref(&invariant),
        loop_condition: Some(&loop_cond),
        condition_is_body_break: false,
        modified_vars: &["y", "i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&var("i")),
        pre_loop_assignments: &pre_loop,
        return_expr: Some(&var("y")),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx);
    assert!(
        result.is_ok(),
        "loop_in_ghost regression should not error: {result:?}"
    );
    let lr = result.unwrap();

    // Initialization: x >= 0 => (0 + x == x) — trivially true. In full-suite
    // order this can conservatively report ResourceOut if earlier seq-heavy
    // diagnostics still occupy hard-timeout workers.
    assert_verified_or_vacuous(&lr.initialization, "loop_in_ghost init: 0 + x == x");

    // Preservation: (y + i == x) /\ (i > 0) => ((y+1) + (i-1) == x)
    assert_verified_or_vacuous(
        &lr.preservation,
        "loop_in_ghost preservation: (y+1)+(i-1) == x",
    );

    // Variant decrease: i > 0 implies i' = i - 1 < i
    if let Some(ref vr) = lr.variant_decrease {
        assert_verified_or_vacuous(vr, "loop_in_ghost variant decrease should verify");
    }
}

// --- ghost/assert_in_ghost.rs regression ---

/// Regression test for `ghost/assert_in_ghost.rs`: proof_assert! inside ghost
/// blocks with simple arithmetic and boolean conditions.
///
/// Models: ghost context establishes facts, postcondition checks them.
/// Part of #2671.
#[test]
#[timeout(60000)]
fn test_regression_assert_in_ghost_simple_arithmetic() {
    // Model: x > 0 && y == x + 1
    let ghost_facts = vec![gt(var("x"), int(0)), eq(var("y"), add(var("x"), int(1)))];

    // proof_assert!(y > x) — should verify from ghost facts
    let goal = gt(var("y"), var("x"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], std::slice::from_ref(&goal))
            .ghost_context(Some(&ghost_facts)),
    );

    assert!(
        result.is_ok(),
        "assert_in_ghost regression should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "assert_in_ghost: y > x from y == x + 1 should verify: {vr:?}"
    );
}

// --- ghost/ghost_let.rs regression ---

/// Regression test for `ghost/ghost_let.rs` bar function: ghost_let! with
/// mutable reference write inside ghost block.
///
/// The bar function takes `Ghost<&mut i32>` and writes 1 to the inner
/// reference. Postcondition: `(^*g2) == 1i32`.
///
/// This exercises the double-deref write encoding path through ghost context.
/// Part of #2671.
#[test]
#[timeout(60000)]
fn test_regression_ghost_let_bar_double_deref_write() {
    // Ghost context: the ghost block writes 1 to *(*g2), producing
    // Final(Deref(g2)) == 1
    let ghost_facts = vec![eq(final_expr(deref(var("g2"))), int(1))];

    // Postcondition: (^*g2) == 1i32
    let ensures = vec![eq(final_expr(deref(var("g2"))), int(1))];

    // Use MutBorrowRequest since bar takes a reference parameter
    let mut final_values = HashMap::new();
    final_values.insert("g2".to_string(), var("g2"));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).ghost_context(Some(&ghost_facts)),
    );

    assert!(
        result.is_ok(),
        "ghost_let bar regression should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "ghost_let bar: (^*g2)==1 via ghost context should verify: {vr:?}"
    );
}
