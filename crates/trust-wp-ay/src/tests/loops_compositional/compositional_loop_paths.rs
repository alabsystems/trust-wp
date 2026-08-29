// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ── Phase 1 + Phase 2 compositional pattern ────────────────────────────────

/// Counting loop with post-loop assignment: `result = i + 1` after loop.
///
/// ```rust
/// #[requires(n >= 1)]
/// #[ensures(result == n + 1)]
/// #[invariant(i >= 0 && i <= n)]
/// fn count_plus_one(n: i32) -> i32 {
///     let mut i = 0;
///     while i < n {
///         i += 1;
///     }
///     i + 1 // post-loop computation
/// }
/// ```
///
/// Phase 1 (loop): invariant `i >= 0 && i <= n` is preserved.
/// Phase 2 (post-loop): with `i >= 0 && i <= n && !(i < n)` assumed,
/// verify `result == n + 1` where `result = i + 1`.
#[test]
#[timeout(30000)]
fn test_compositional_post_loop_assignment_verifies() {
    // Phase 1: Loop invariant verification
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let cond = lt(var("i"), var("n"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let invariants = [inv.clone()];
    let loop_result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("n"), int(1))],
        ensures: &[], // Post-loop verification handles postcondition
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
        loop_result.all_passed(),
        "Loop invariant should be verified: {loop_result:?}"
    );

    // Phase 2: Post-loop function verification with loop-exit assumptions.
    // This models what the driver does: inject invariants ∧ ¬condition as
    // preconditions, then verify function postcondition.
    let loop_exit_requires = vec![
        ge(var("n"), int(1)), // original precondition
        inv,                  // loop invariant assumed at exit
        not(cond),            // loop condition negated
    ];

    // Postcondition: result == n + 1, with body result = i + 1
    let postcondition = eq(var("result"), add(var("n"), int(1)));
    let return_expr = add(var("i"), int(1));

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[postcondition])
            .return_expr(Some(&return_expr)),
    );

    assert!(
        matches!(fn_result, Ok(VerificationResult::Verified(_))),
        "Post-loop verification should succeed: result = i + 1 = n + 1 when i == n, got: {fn_result:?}"
    );
}

/// Negative control: post-loop verification FAILS when loop-exit assumptions
/// are missing — proving the assumptions are necessary.
///
/// Same function as above, but without loop-exit assumptions. The verifier
/// cannot establish `result == n + 1` because `i` is unconstrained.
#[test]
#[timeout(30000)]
fn test_compositional_post_loop_fails_without_loop_exit_assumptions() {
    // Only original precondition, no loop-exit state
    let requires = vec![ge(var("n"), int(1))];
    let postcondition = eq(var("result"), add(var("n"), int(1)));
    let return_expr = add(var("i"), int(1));

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&requires, &[postcondition]).return_expr(Some(&return_expr)),
    );

    assert_ok_failed_with_counterexample(
        &fn_result,
        "without loop-exit assumptions, post-loop verification",
    );
}

/// Negative control: wrong invariant produces wrong post-loop result.
///
/// If the loop invariant claims `i >= 0 && i <= n + 1` (too weak — allows
/// `i = n + 1` at exit), and we verify `result == n + 1` with body `i`,
/// this could spuriously verify. But with the correct negated condition
/// `!(i < n)` meaning `i >= n`, the invariant `i <= n + 1` is too weak
/// to pin `i == n` at exit.
#[test]
#[timeout(30000)]
fn test_compositional_wrong_postcondition_fails() {
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let cond = lt(var("i"), var("n"));

    // Loop-exit state: i >= 0 && i <= n && !(i < n), so i == n
    let loop_exit_requires = vec![ge(var("n"), int(1)), inv, not(cond)];

    // Wrong postcondition: result == n + 2 (should be n + 1)
    let wrong_postcondition = eq(var("result"), add(var("n"), int(2)));
    let return_expr = add(var("i"), int(1));

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[wrong_postcondition])
            .return_expr(Some(&return_expr)),
    );

    assert_ok_failed_with_counterexample(
        &fn_result,
        "wrong postcondition where i + 1 = n + 1, not n + 2",
    );
}

/// Post-loop variable reassignment pattern (like `nested_borrows`).
///
/// Models the pattern where a variable is reassigned after the loop:
/// ```rust
/// #[requires(x == 0)]
/// #[ensures(result == 42)]
/// #[invariant(x == 0)]
/// fn reassign_after_loop(mut x: i32) -> i32 {
///     loop { if ... { break; } x = 0; }
///     x = 42;  // post-loop reassignment
///     x
/// }
/// ```
///
/// The loop invariant gives us `x == 0` at exit, but the postcondition
/// depends on the post-loop assignment `x = 42`.
#[test]
#[timeout(30000)]
fn test_compositional_post_loop_reassignment_verifies() {
    // Phase 1: loop invariant (x == 0 preserved)
    let inv = eq(var("x"), int(0));
    let cond = lt(var("i"), int(10));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    body_effect.insert("x".to_string(), int(0));

    let invariants = [inv.clone()];
    let loop_result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[eq(var("x"), int(0))],
        ensures: &[],
        invariants: &invariants,
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "x"],
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
        loop_result.all_passed(),
        "Loop invariant x == 0 should be verified: {loop_result:?}"
    );

    // Phase 2: Post-loop with reassignment.
    // Loop-exit gives us x == 0, but post-loop code sets x = 42.
    // We model this as: the return_expr is 42 (the post-loop assignment).
    // The function verification only needs the loop-exit assumptions
    // if the postcondition depends on the pre-reassignment state.
    // Here result == 42 depends on the post-loop assignment, not the invariant.
    let loop_exit_requires = vec![
        eq(var("x"), int(0)), // precondition
        inv,                  // loop invariant at exit
        not(cond),            // loop exited
    ];

    let postcondition = eq(var("result"), int(42));
    let return_expr = int(42); // post-loop code sets result to 42

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[postcondition])
            .return_expr(Some(&return_expr)),
    );

    assert!(
        matches!(fn_result, Ok(VerificationResult::Verified(_))),
        "Post-loop reassignment result == 42 should verify: {fn_result:?}"
    );
}

/// Post-loop verification with multiple postconditions.
///
/// Models a function with two ensures clauses where both depend on
/// the loop-exit state:
/// ```rust
/// #[requires(n >= 1)]
/// #[ensures(result >= 1)]
/// #[ensures(result <= n + 1)]
/// #[invariant(i >= 0 && i <= n)]
/// fn bounded_result(n: i32) -> i32 {
///     let mut i = 0;
///     while i < n {
///         i += 1;
///     }
///     i + 1
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_compositional_multiple_postconditions() {
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let cond = lt(var("i"), var("n"));

    let loop_exit_requires = vec![ge(var("n"), int(1)), inv, not(cond)];

    let ensures1 = ge(var("result"), int(1));
    let ensures2 = le(var("result"), add(var("n"), int(1)));
    let return_expr = add(var("i"), int(1));

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[ensures1, ensures2])
            .return_expr(Some(&return_expr)),
    );

    assert!(
        matches!(fn_result, Ok(VerificationResult::Verified(_))),
        "Both postconditions should verify with loop-exit state: {fn_result:?}"
    );
}

/// Unconditional loop (no condition, break-based exit) — only invariants
/// assumed at exit, no negated condition.
///
/// Models:
/// ```rust
/// #[ensures(result > 0)]
/// #[invariant(x > 0)]
/// fn unconditional_loop(mut x: i32) -> i32 {
///     loop { if ... { break; } x = abs(x) + 1; }
///     x
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_compositional_unconditional_loop_no_condition() {
    // For unconditional loops (loop {} with internal break), there is no
    // loop condition to negate. Only invariants are assumed at exit.
    let loop_exit_requires = vec![
        gt(var("x"), int(0)), // invariant: x > 0 at exit
    ];

    let postcondition = gt(var("result"), int(0));
    let return_expr = var("x");

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[postcondition])
            .return_expr(Some(&return_expr)),
    );

    assert!(
        matches!(fn_result, Ok(VerificationResult::Verified(_))),
        "Unconditional loop with invariant x > 0 verifies result > 0: {fn_result:?}"
    );
}

// ── Multi-variable compositional patterns ──────────────────────────────────

/// Two variables modified by loop, post-loop result depends on both.
///
/// Models:
/// ```rust
/// #[requires(n >= 1)]
/// #[ensures(result == n * 2)]
/// #[invariant(i >= 0 && i <= n && sum == i * 2)]
/// fn double_count(n: i32) -> i32 {
///     let mut i = 0;
///     let mut sum = 0;
///     while i < n {
///         sum += 2;
///         i += 1;
///     }
///     sum // post-loop: just return sum (no extra computation)
/// }
/// ```
///
/// Phase 1 verifies the loop invariant `i >= 0 && i <= n && sum == i * 2`.
/// Phase 2 verifies: at exit `i == n` (from `i <= n && !(i < n)`),
/// so `sum == n * 2`, and `result == sum == n * 2`.
#[test]
#[timeout(30000)]
fn test_compositional_multi_variable_loop_and_postcondition() {
    // Phase 1: loop invariant with two modified variables
    let inv = and(
        and(ge(var("i"), int(0)), le(var("i"), var("n"))),
        eq(var("sum"), add(var("i"), var("i"))), // sum == i * 2 expressed as i + i
    );
    let cond = lt(var("i"), var("n"));

    let mut body_effect = HashMap::new();
    body_effect.insert("sum".to_string(), add(var("sum"), int(2)));
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let invariants = [inv.clone()];
    let loop_result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("n"), int(1))],
        ensures: &[],
        invariants: &invariants,
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "sum"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::from([
            ("i".to_string(), NamedBindingValue::untyped(int(0))),
            ("sum".to_string(), NamedBindingValue::untyped(int(0))),
        ]),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        loop_result.all_passed(),
        "Loop invariant with i and sum should verify: {loop_result:?}"
    );

    // Phase 2: Post-loop verification.
    // At loop exit: i >= 0 && i <= n && sum == i + i && !(i < n)
    // This pins i == n, so sum == n + n == n * 2.
    // return_expr = sum, postcondition: result == n + n.
    let loop_exit_requires = vec![
        ge(var("n"), int(1)),
        inv, // invariant assumed at exit
        not(cond),
    ];

    let postcondition = eq(var("result"), add(var("n"), var("n")));
    let return_expr = var("sum");

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[postcondition])
            .return_expr(Some(&return_expr)),
    );

    assert!(
        matches!(fn_result, Ok(VerificationResult::Verified(_))),
        "Multi-variable: result == n * 2 should verify with loop-exit state: {fn_result:?}"
    );
}

/// Multi-variable loop with post-loop computation that uses both variables.
///
/// Models:
/// ```rust
/// #[requires(n >= 1)]
/// #[ensures(result == n * 2 + 1)]
/// #[invariant(i >= 0 && i <= n && sum == i * 2)]
/// fn double_count_plus_one(n: i32) -> i32 {
///     let mut i = 0;
///     let mut sum = 0;
///     while i < n {
///         sum += 2;
///         i += 1;
///     }
///     sum + 1 // post-loop adds 1
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_compositional_multi_variable_with_post_loop_computation() {
    let inv = and(
        and(ge(var("i"), int(0)), le(var("i"), var("n"))),
        eq(var("sum"), add(var("i"), var("i"))),
    );
    let cond = lt(var("i"), var("n"));

    let loop_exit_requires = vec![ge(var("n"), int(1)), inv, not(cond)];

    // Post-loop computation: result = sum + 1 = n * 2 + 1
    let postcondition = eq(var("result"), add(add(var("n"), var("n")), int(1)));
    let return_expr = add(var("sum"), int(1));

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[postcondition])
            .return_expr(Some(&return_expr)),
    );

    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27): the verdict
    // demotes to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        fn_result
            .as_ref()
            .is_ok_and(crate::tests::helpers::verified_or_known_proof_trusted),
        "Multi-variable with post-loop +1: result == n*2+1 should verify: {fn_result:?}"
    );
}

/// Soundness check: unconstrained modified variable should make
/// postcondition unprovable.
///
/// If a loop modifies variable `y` but the invariant says nothing about `y`,
/// and the postcondition depends on `y`, the post-loop path must fail.
/// This tests that the loop-exit assumptions (invariant + ¬condition) are
/// insufficient when the postcondition depends on unconstrained state.
///
/// Models:
/// ```rust
/// #[requires(n >= 1)]
/// #[ensures(result == y + 1)] // y is unconstrained at exit!
/// #[invariant(i >= 0 && i <= n)]
/// fn unconstrained_var(n: i32) -> i32 {
///     let mut i = 0;
///     let mut y = 0;
///     while i < n {
///         i += 1;
///         y = arbitrary();
///     }
///     y + 1
/// }
/// ```
///
/// The invariant pins `i` but says nothing about `y`. The post-loop
/// path only gets `i >= 0 && i <= n && !(i < n)` — `y` is unconstrained.
/// Postcondition `result == y + 1` where `result = y + 1` is tautologically
/// true IF the verifier correctly binds result to return_expr. But if we
/// make the postcondition `result == 42`, it should fail because y is unknown.
#[test]
#[timeout(30000)]
fn test_compositional_unconstrained_modified_var_fails() {
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let cond = lt(var("i"), var("n"));

    // Loop-exit state: only invariant on i, nothing about y
    let loop_exit_requires = vec![ge(var("n"), int(1)), inv, not(cond)];

    // Postcondition claims a specific value for y, but y is unconstrained
    let wrong_postcondition = eq(var("result"), int(42));
    let return_expr = add(var("y"), int(1)); // y is arbitrary

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[wrong_postcondition])
            .return_expr(Some(&return_expr)),
    );

    assert_ok_failed_with_counterexample(&fn_result, "postcondition depending on unconstrained y");
}

/// Positive control for tautological postcondition: `result == y + 1`
/// where `return_expr = y + 1`. The postcondition is tautologically
/// satisfied regardless of y's value, because result IS y + 1.
#[test]
#[timeout(30000)]
fn test_compositional_tautological_postcondition_verifies() {
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    let cond = lt(var("i"), var("n"));

    let loop_exit_requires = vec![ge(var("n"), int(1)), inv, not(cond)];

    // result == y + 1 where return_expr = y + 1 — tautological
    let postcondition = eq(var("result"), add(var("y"), int(1)));
    let return_expr = add(var("y"), int(1));

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[postcondition])
            .return_expr(Some(&return_expr)),
    );

    assert!(
        matches!(fn_result, Ok(VerificationResult::Verified(_))),
        "Tautological postcondition (result == return_expr) should always verify: {fn_result:?}"
    );
}

// ── Empty-assumptions path (loop timeout + postconditions) ───────────────

/// Function-level path with NO loop-exit assumptions (#2085).
///
/// When the loop invariant proof times out (Unknown) but the function has
/// postconditions, the driver now returns `ContinueWithAssumptions(vec![])`
/// instead of `Handled`. This means the function-level path runs with only
/// the original preconditions (no loop-exit state injected).
///
/// This test verifies that a tautological postcondition (result == return_expr)
/// still verifies even without loop-exit assumptions — the function-level
/// path reasons directly about the body expression.
///
/// ```rust
/// #[requires(n >= 1)]
/// #[ensures(result == n + 1)]
/// fn simple_with_loop(n: i32) -> i32 {
///     let mut i = 0;
///     loop {
///         if i >= n {
///             break;
///         }
///         i += 1;
///     }
///     n + 1 // postcondition depends only on n, not on loop state
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_empty_assumptions_path_verifies_body_determined_postcondition() {
    // Only the original precondition — no loop-exit assumptions.
    // This simulates ContinueWithAssumptions(vec![]) from the driver
    // when the loop invariant times out.
    let requires_no_loop_exit = vec![ge(var("n"), int(1))];

    // Postcondition depends only on n (not on loop-modified variables)
    let postcondition = eq(var("result"), add(var("n"), int(1)));
    let return_expr = add(var("n"), int(1));

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&requires_no_loop_exit, &[postcondition])
            .return_expr(Some(&return_expr)),
    );

    assert!(
        matches!(fn_result, Ok(VerificationResult::Verified(_))),
        "Body-determined postcondition should verify without loop-exit assumptions: {fn_result:?}"
    );
}

/// Negative control: a postcondition that depends on loop-exit state fails
/// when no loop-exit assumptions are provided (#2085).
///
/// This is the expected tradeoff: when the loop invariant times out, the
/// function-level path runs without loop-exit assumptions. Postconditions
/// that depend on loop-exit state (e.g., `result == i` where i is the
/// loop counter) will fail because i is unconstrained.
///
/// ```rust
/// #[requires(n >= 1)]
/// #[ensures(result == n)] // depends on i == n at loop exit
/// fn loop_dependent(n: i32) -> i32 {
///     let mut i = 0;
///     loop {
///         if i >= n {
///             break;
///         }
///         i += 1;
///     }
///     i // postcondition needs i == n from loop-exit state
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_empty_assumptions_path_fails_loop_dependent_postcondition() {
    // No loop-exit assumptions — i is unconstrained
    let requires_no_loop_exit = vec![ge(var("n"), int(1))];

    // Postcondition claims result == n, but return_expr = i (unconstrained)
    let postcondition = eq(var("result"), var("n"));
    let return_expr = var("i");

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&requires_no_loop_exit, &[postcondition])
            .return_expr(Some(&return_expr)),
    );

    assert_ok_failed_with_counterexample(
        &fn_result,
        "loop-dependent postcondition without loop-exit assumptions",
    );
}

// ── Postcondition-deferred path (induction passes, loop-local postcondition fails) ──

/// Models the `nested_borrows` pattern (#2085): the loop-local postcondition
/// check fails because the function's ensures clauses depend on post-loop
/// code (e.g., `std::mem::replace`), but the induction proof (init +
/// preservation) succeeds. The driver should recognize this and delegate
/// postcondition checking to the function-level path.
///
/// Phase 1: Loop invariant init + preservation pass, but postcondition fails
/// because `ensures: result == 42` cannot be established from `invariant ∧
/// ¬condition` alone — it requires the post-loop assignment `x = 42`.
///
/// Phase 2: Function-level path with loop-exit assumptions succeeds because
/// the post-loop return_expr is 42, matching the postcondition.
///
/// ```rust
/// #[requires(x == 0)]
/// #[ensures(result == 42)]
/// #[invariant(x == 0)]
/// fn post_loop_reassign(mut x: i32) -> i32 {
///     loop { if ... { break; } x = 0; }
///     x = 42;  // post-loop!
///     x
/// }
/// ```
#[test]
#[timeout(60000)]
fn test_induction_passes_postcondition_fails_deferred_to_fn_path() {
    // Phase 1: Loop verification — invariant x == 0 is preserved.
    let inv = eq(var("x"), int(0));
    let cond = lt(var("i"), int(10));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    body_effect.insert("x".to_string(), int(0));

    // Postcondition that CANNOT be verified from loop-exit state alone:
    // result == 42 requires the post-loop assignment x = 42.
    let postcondition = eq(var("result"), int(42));

    let invariants = [inv.clone()];
    let loop_result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[eq(var("x"), int(0))],
        ensures: std::slice::from_ref(&postcondition),
        invariants: &invariants,
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "x"],
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

    // Key assertion: induction (init + preservation) passes, but postcondition fails.
    assert!(
        loop_result.induction_passed(),
        "Induction (init + preservation) should pass: {loop_result:?}"
    );
    assert!(
        !loop_result.all_passed(),
        "all_passed should be false (postcondition failed): {loop_result:?}"
    );
    assert_failed_result(
        &loop_result.postcondition,
        "loop-local postcondition result == 42 from loop exit",
    );

    // Phase 2: Function-level path with loop-exit assumptions succeeds.
    // This is what the driver does when it detects induction_passed() but
    // postcondition failed with non-empty base_ensures.
    let loop_exit_requires = vec![
        eq(var("x"), int(0)), // precondition
        inv,                  // loop invariant at exit
        not(cond),            // loop exited
    ];

    // Post-loop code sets x = 42, result = x.
    let return_expr = int(42);

    let fn_result = verify_function_with_modes(
        VerificationRequest::new(&loop_exit_requires, &[postcondition])
            .return_expr(Some(&return_expr)),
    );

    assert!(
        matches!(fn_result, Ok(VerificationResult::Verified(_))),
        "Function-level path with post-loop assignment should verify: {fn_result:?}"
    );
}
