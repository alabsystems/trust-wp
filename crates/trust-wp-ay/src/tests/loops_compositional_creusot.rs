// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compositional loop tests modeled on real Creusot compat suite patterns (#2085).
//!
//! These tests exercise the two-phase verification approach (loop induction +
//! function-level post-loop verification) against patterns from actual Creusot
//! `should_succeed` test functions and trust-wp fixture tests.
//!
//! Complements `loops_compositional.rs` which covers synthetic patterns and
//! mechanism tests. This module covers real-world patterns that the
//! compositional loop verification path needs to handle.

use std::collections::HashMap;

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::{super::*, helpers::*};

fn assert_failed_with_counterexample(result: &VerificationResult, context: &str) {
    match result {
        VerificationResult::Failed(cex) => assert!(
            !cex.values.is_empty(),
            "{context} should fail with a counterexample model; got empty counterexample"
        ),
        other => panic!("{context} should fail verification; got {other:?}"),
    }
}

fn assert_ok_failed_with_counterexample(
    result: &Result<VerificationResult, impl std::fmt::Debug>,
    context: &str,
) {
    match result {
        Ok(VerificationResult::Failed(cex)) => assert!(
            !cex.values.is_empty(),
            "{context} should fail with a counterexample model; got empty counterexample"
        ),
        Ok(other) => panic!("{context} should fail verification; got {other:?}"),
        Err(err) => panic!("{context} should encode successfully; got {err:?}"),
    }
}

/// Models `ghost/loop_in_ghost.rs::foo` from Creusot compat suite.
///
/// ```rust
/// #[ensures(*result == x)]
/// pub fn foo(x: u32) -> Ghost<u32> {
///     ghost! {
///         let mut y = 0; let mut i = x;
///         #[invariant(y@ + i@ == x@)]
///         while i > 0 { i -= 1; y += 1; }
///         y   // POST-LOOP
///     }
/// }
/// ```
///
/// Phase 1: Loop invariant `y + i == x` with body `i -= 1; y += 1`.
/// Phase 2: At loop exit: `y + i == x ∧ !(i > 0)` → `y + 0 == x` → `y == x`.
///          Postcondition: `result == x`, return_expr: `y` → verified.
#[test]
#[timeout(30000)]
fn test_creusot_ghost_loop_sum_invariant_verifies() {
    // Phase 1: Loop verification
    let inv = eq(add(var("y"), var("i")), var("x"));
    let cond = gt(var("i"), int(0));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), sub(var("i"), int(1)));
    body_effect.insert("y".to_string(), add(var("y"), int(1)));

    let invariants = [inv.clone()];
    let loop_result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("x"), int(0))],
        ensures: &[],
        invariants: &invariants,
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "y"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::from([
            ("y".to_string(), NamedBindingValue::untyped(int(0))),
            ("i".to_string(), NamedBindingValue::untyped(var("x"))),
        ]),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        loop_result.induction_passed(),
        "Loop induction (y + i == x) should pass: {loop_result:?}"
    );

    // Phase 2: Function-level path with loop-exit assumptions.
    // At exit: y + i == x ∧ !(i > 0) → since i is non-negative, i == 0 → y == x.
    let loop_exit_requires = vec![
        ge(var("x"), int(0)), // precondition
        inv,                  // invariant at exit
        not(cond),            // loop exited: !(i > 0)
        ge(var("i"), int(0)), // i is unsigned (u32)
    ];

    // Postcondition: result == x, return_expr: y
    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[eq(var("result"), var("x"))])
            .return_expr(Some(&var("y"))),
    );

    assert!(
        matches!(fn_result, Ok(VerificationResult::Verified(_))),
        "Ghost loop foo should verify: y == x at exit with return_expr y. Got: {fn_result:?}"
    );
}

/// Models `count_to_n_with_shadow` from fixture tests.
///
/// ```rust
/// #[ensures(result == n)]
/// #[invariant(i >= 0 && i <= n)]
/// #[invariant(j == i)]
/// fn count_to_n_with_shadow(n: i32) -> i32 {
///     let mut i = 0;
///     let mut j = 0;
///     while i < n {
///         i += 1;
///         j = i;
///     }
///     j // POST-LOOP: return shadow variable
/// }
/// ```
///
/// Phase 1: Two invariants: `i >= 0 ∧ i <= n` and `j == i`.
/// Phase 2: At exit: `i <= n ∧ !(i < n) ∧ j == i` → `i == n ∧ j == n`.
///          Postcondition: `result == n`, return_expr: `j` → verified.
#[test]
#[timeout(60000)]
fn test_creusot_shadow_variable_verifies() {
    // Phase 1: Loop verification with two invariants.
    let inv1 = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let inv2 = eq(var("j"), var("i"));
    let cond = lt(var("i"), var("n"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    body_effect.insert("j".to_string(), add(var("i"), int(1)));

    let invariants = [inv1.clone(), inv2.clone()];
    let loop_result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("n"), int(0))],
        ensures: &[],
        invariants: &invariants,
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "j"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::from([
            ("i".to_string(), NamedBindingValue::untyped(int(0))),
            ("j".to_string(), NamedBindingValue::untyped(int(0))),
        ]),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        loop_result.induction_passed(),
        "Shadow variable loop induction should pass: {loop_result:?}"
    );

    // Phase 2: Function-level path.
    // At exit: (i >= 0 ∧ i <= n) ∧ (j == i) ∧ !(i < n) → i == n ∧ j == n
    let loop_exit_requires = vec![
        ge(var("n"), int(0)), // precondition
        inv1,                 // invariant 1
        inv2,                 // invariant 2
        not(cond),            // loop exited
    ];

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[eq(var("result"), var("n"))])
            .return_expr(Some(&var("j"))),
    );

    assert!(
        matches!(fn_result, Ok(VerificationResult::Verified(_))),
        "Shadow variable should verify: j == n at exit. Got: {fn_result:?}"
    );
}

/// Soundness test: too-weak invariant should NOT allow postcondition to verify.
///
/// ```rust
/// #[ensures(result == n)]
/// #[invariant(i >= 0)] // too weak — doesn't establish i <= n
/// fn buggy_invariant(n: i32) -> i32 {
///     let mut i = 0;
///     while i < n {
///         i += 1;
///     }
///     i
/// }
/// ```
///
/// Phase 1: `i >= 0` is preserved correctly (init + preservation pass).
/// Phase 2: At exit: `i >= 0 ∧ !(i < n)` → `i >= n` but NOT `i == n`.
///          The solver finds a counterexample (e.g., i > n) → fails.
#[test]
#[timeout(30000)]
fn test_creusot_weak_invariant_soundly_fails() {
    // Phase 1: Too-weak invariant still passes induction.
    let inv = ge(var("i"), int(0));
    let cond = lt(var("i"), var("n"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let invariants = [inv.clone()];
    let loop_result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("n"), int(0))],
        ensures: &[],
        invariants: &invariants,
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::from([(
            "i".to_string(),
            NamedBindingValue::untyped(int(0)),
        )]),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        loop_result.induction_passed(),
        "Even a weak invariant should pass induction: {loop_result:?}"
    );

    // Phase 2: Function-level path should FAIL.
    // At exit: i >= 0 ∧ !(i < n) → i >= n, but not i == n.
    // Postcondition result == n with return_expr i requires i == n,
    // which is not provable from i >= n alone.
    let loop_exit_requires = vec![ge(var("n"), int(0)), inv, not(cond)];

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[eq(var("result"), var("n"))])
            .return_expr(Some(&var("i"))),
    );

    assert_ok_failed_with_counterexample(
        &fn_result,
        "weak invariant postcondition where i >= n but not i == n",
    );
}

/// Models `return_param_after_loop` from fixture tests — trivial post-loop
/// expression that doesn't depend on loop state.
///
/// ```rust
/// #[ensures(result == n)]
/// #[invariant(i >= 0 && i <= n)]
/// fn return_param_after_loop(n: i32) -> i32 {
///     let mut i = 0;
///     while i < n {
///         i += 1;
///     }
///     n // POST-LOOP: returns parameter, not loop variable
/// }
/// ```
///
/// Phase 2 should succeed trivially: return_expr is `n`, postcondition is
/// `result == n`, so the verification reduces to `n == n` regardless of
/// loop-exit state.
#[test]
#[timeout(30000)]
fn test_creusot_return_param_trivially_verifies() {
    // Phase 1: Standard counting loop.
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let cond = lt(var("i"), var("n"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let invariants = [inv.clone()];
    let loop_result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("n"), int(0))],
        ensures: &[],
        invariants: &invariants,
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::from([(
            "i".to_string(),
            NamedBindingValue::untyped(int(0)),
        )]),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        loop_result.induction_passed(),
        "Standard counting loop should pass induction: {loop_result:?}"
    );

    // Phase 2: Postcondition is trivially satisfied by return_expr.
    let loop_exit_requires = vec![ge(var("n"), int(0)), inv, not(cond)];

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[eq(var("result"), var("n"))])
            .return_expr(Some(&var("n"))),
    );

    assert!(
        matches!(fn_result, Ok(VerificationResult::Verified(_))),
        "Returning parameter directly should trivially verify. Got: {fn_result:?}"
    );
}

// ── Post-loop mutable borrow patterns (#2085) ──────────────────────────────
//
// These tests model the compositional path for functions where a mutable
// reference is modified AFTER a loop, and the postcondition depends on the
// post-loop value. The loop-local postcondition check (postcondition.rs)
// cannot handle these because it only sees loop-exit state. The driver's
// `filter_post_loop_borrow_resolution_vars` excludes post-loop-modified
// vars from loop-local resolution, and the function-level path handles them
// via `final_values` in `MutBorrowRequest`.

/// Models a function that writes `*x = n` after a counting loop, with
/// postcondition `^x == n`.
///
/// ```rust
/// #[requires(*x == 0)]
/// #[ensures(^x == n)]
/// #[invariant(*x == 0)]
/// fn set_after_loop(x: &mut i32, n: i32) {
///     let mut i = 0;
///     while i < n {
///         i += 1;
///         *x = 0; // loop body maintains *x == 0
///     }
///     *x = n; // POST-LOOP: overwrite with n
/// }
/// ```
///
/// Phase 1: Loop invariant `*x == 0` is preserved.
/// Phase 2 (mut_borrow path): With loop-exit assumptions + `final_values`
/// mapping `x → n`, verify postcondition `^x == n`.
#[test]
#[timeout(60000)]
fn test_compositional_post_loop_deref_write_mut_borrow_verifies() {
    // Phase 1: Loop invariant with deref body effect.
    let inv = eq(deref(var("x")), int(0));
    let cond = lt(var("i"), var("n"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut deref_body_effect = HashMap::new();
    deref_body_effect.insert("x".to_string(), int(0)); // *x = 0 in loop body

    let invariants = [inv.clone()];
    let loop_result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[eq(deref(var("x")), int(0)), ge(var("n"), int(1))],
        ensures: &[], // Postcondition deferred to function-level path
        invariants: &invariants,
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "x"], // x is in deref_body_effect, must be listed (#1884)
        body_effect: &body_effect,
        deref_body_effect: &deref_body_effect,
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::from([(
            "i".to_string(),
            NamedBindingValue::untyped(int(0)),
        )]),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        loop_result.induction_passed(),
        "Loop invariant *x == 0 should pass induction: {loop_result:?}"
    );

    // Phase 2: Function-level mut_borrow path with post-loop deref write.
    //
    // The driver constructs final_values from the full MIR analysis, which
    // includes post-loop effects. For *x = n after loop, final_values maps
    // x → Var("n"). The loop-exit assumptions are injected as requires.
    let loop_exit_requires = vec![
        eq(deref(var("x")), int(0)), // precondition
        ge(var("n"), int(1)),        // precondition
        inv,                         // loop invariant at exit
        not(cond),                   // loop exited
    ];

    // Postcondition: ^x == n (the final value of x equals n)
    let postcondition = eq(final_expr(var("x")), var("n"));

    // final_values from MIR analysis: x → n (the post-loop assignment *x = n)
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), var("n"));

    let fn_result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &loop_exit_requires,
        &[postcondition],
        &final_values,
    ))
    .expect("encoding should succeed");

    assert!(
        matches!(fn_result, VerificationResult::Verified(_)),
        "Post-loop deref write *x = n with postcondition ^x == n should verify. Got: {fn_result:?}"
    );
}

/// Negative control: without the post-loop assignment in `final_values`,
/// the postcondition should fail. This proves the `final_values` are
/// necessary for correctness.
#[test]
#[timeout(60000)]
fn test_compositional_post_loop_deref_write_fails_without_final_values() {
    let inv = eq(deref(var("x")), int(0));
    let cond = lt(var("i"), var("n"));

    let loop_exit_requires = vec![
        eq(deref(var("x")), int(0)),
        ge(var("n"), int(1)),
        inv,
        not(cond),
    ];

    // Postcondition: ^x == n
    let postcondition = eq(final_expr(var("x")), var("n"));

    // Wrong final_values: x → *x (the loop-exit value, not the post-loop value)
    // This simulates what would happen if the MIR analysis didn't capture
    // the post-loop assignment.
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));

    let fn_result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &loop_exit_requires,
        &[postcondition],
        &final_values,
    ))
    .expect("encoding should succeed");

    assert_failed_with_counterexample(
        &fn_result,
        "without post-loop assignment in final_values, ^x == n",
    );
}

/// Models post-loop deref write with loop-dependent value: `*x = i` after loop.
///
/// ```rust
/// #[requires(*x == 0)]
/// #[ensures(^x == n)]
/// #[invariant(i >= 0 && i <= n)]
/// fn set_to_counter(x: &mut i32, n: i32) {
///     let mut i = 0;
///     while i < n {
///         i += 1;
///     }
///     *x = i; // POST-LOOP: i == n at loop exit
/// }
/// ```
///
/// Phase 2 depends on BOTH loop-exit assumptions (i == n) AND final_values
/// (x → i). This tests that the compositional path correctly combines both.
#[test]
#[timeout(60000)]
fn test_compositional_post_loop_deref_write_uses_loop_exit_state() {
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let cond = lt(var("i"), var("n"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let invariants = [inv.clone()];
    let loop_result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("n"), int(0))],
        ensures: &[],
        invariants: &invariants,
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::from([(
            "i".to_string(),
            NamedBindingValue::untyped(int(0)),
        )]),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        loop_result.induction_passed(),
        "Counting loop induction should pass: {loop_result:?}"
    );

    // Phase 2: final_values maps x → i, and loop-exit gives i == n.
    // Combined: x_final == i ∧ i == n ⊢ ^x == n.
    let loop_exit_requires = vec![
        ge(var("n"), int(0)), // precondition
        inv,                  // i >= 0 && i <= n
        not(cond),            // !(i < n), so i >= n, combined with i <= n: i == n
    ];

    let postcondition = eq(final_expr(var("x")), var("n"));

    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), var("i")); // *x = i (post-loop)

    let fn_result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &loop_exit_requires,
        &[postcondition],
        &final_values,
    ))
    .expect("encoding should succeed");

    assert!(
        matches!(fn_result, VerificationResult::Verified(_)),
        "Post-loop *x = i with loop-exit i == n should verify ^x == n. Got: {fn_result:?}"
    );
}
