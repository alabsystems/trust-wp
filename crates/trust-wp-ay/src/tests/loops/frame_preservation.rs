// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::*;

/// Regression for ghost/loop_in_ghost: postcondition needs `requires`.
///
/// Models `foo(x: u32) -> Ghost<u32>`:
///   requires: x >= 0 (unsigned nonneg)
///   invariant: y + i == x, i >= 0
///   loop: while i > 0 { i -= 1; y += 1; }
///   ensures: result == x (with ghost return rewrite: result = y)
///
/// Without asserting `requires` in the postcondition VC, the solver picks
/// x = -1, i = -1, y = 0, making the invariant hold but the postcondition
/// fail (y != x). (#1295)
///
/// Note: uses plain (non-View) expressions; View identity propagation is
/// a separate solver-level concern tested elsewhere.
#[test]
#[timeout(30000)]
fn test_ghost_loop_view_invariant_postcondition() {
    // Unsigned nonneg for parameter x (u32)
    let req_x = ge(var("x"), int(0));
    // Plain (non-view) invariant to test requires plumbing: y + i == x, i >= 0
    let inv_sum = eq(add(var("y"), var("i")), var("x"));
    let inv_nonneg = ge(var("i"), int(0));
    let ens = eq(var("y"), var("x"));
    let cond = gt(var("i"), int(0));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("y".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(var("x")));

    let mut body_effect = HashMap::new();
    body_effect.insert("y".to_string(), add(var("y"), int(1)));
    body_effect.insert("i".to_string(), sub(var("i"), int(1)));

    let modified: Vec<&str> = vec!["y", "i"];

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req_x],
        ensures: &[ens],
        invariants: &[inv_sum, inv_nonneg],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &modified,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: Some(&var("y")),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .expect("encoding should succeed");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "initialization should verify, got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify, got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify with requires constraining x >= 0, got {:?}",
        result.postcondition
    );
}

// Note: a View-based variant of the above test (using `y@` instead of `y`
// in invariants) times out in the ay solver due to View identity chain
// propagation cost. The real-world fix for ghost/loop_in_ghost is in the
// driver: is_trust_wp_ghost_def_path now recognizes creusot_std::Ghost
// re-exported through trust_wp_std, enabling the ghost return rewrite.
// See driver tests for that coverage. (#1572)

/// Test: Postcondition referencing `^y` (prophecy) for an unchanged mutable
/// reference parameter fails because `y_final` is unconstrained (#759 Phase 4).
///
/// Models:
/// ```rust
/// #[requires(*x == 0)]
/// #[ensures(*y == *y)] // trivially true, but uses y
/// fn foo(x: &mut i32, y: &mut i32) {
///     #[invariant(*x == 0)]
///     loop {
///         if i > 10 {
///             break;
///         }
///         i += 1;
///         *x = 0;
///     }
/// }
/// ```
///
/// The loop modifies `x` (via deref) but NOT `y`. The postcondition
/// `^y == ^y` should be trivially provable, but a postcondition like
/// `^y == 42` (where y starts at 42) requires borrow resolution for
/// unchanged parameters: `y_final == y_current`. Without this, `y_final`
/// is a free variable and the solver can assign any value.
///
/// This test demonstrates the gap that Phase 4 of #1816 / issue #759
/// would close: borrow resolution for unchanged mutable reference
/// parameters in loop postconditions.
#[test]
#[timeout(30000)]
fn test_postcondition_unchanged_mut_ref_borrow_resolution_gap() {
    // requires: *y == 42
    let requires = eq(deref(var("y")), int(42));

    // invariant: *x == 0
    let inv = eq(deref(var("x")), int(0));

    // ensures: ^y == 42
    // This postcondition says the final value of *y (when borrow resolves)
    // is 42. Since y is unchanged in the loop, ^y should equal *y which
    // equals 42 from the requires. But without y_final == y_current
    // borrow resolution, y_final is unconstrained.
    let ensures = eq(final_expr(var("y")), int(42));

    // loop condition: i < 10
    let cond = lt(var("i"), int(10));

    // body_effect: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // deref_body_effect: *x = 0
    let mut deref_body_effect = HashMap::new();
    deref_body_effect.insert("x".to_string(), int(0));

    // Only i and x are modified; y is unchanged
    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[requires],
        ensures: &[ensures],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "x"],
        body_effect: &body_effect,
        deref_body_effect: &deref_body_effect,
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // Phase 4 (#759): With borrow resolution for unchanged mut refs,
    // y_final == y_current is asserted, and requires(*y == 42) provides
    // y_current == 42, so the postcondition ^y == 42 is now provable.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Phase 4 borrow resolution should make postcondition provable \
         (y_final == y_current == 42). Got {:?}.",
        result.postcondition
    );
}

/// Phase 5 (#759): Frame preservation for unchanged locals via pre_loop_assignments.
///
/// Models:
/// ```rust
/// #[requires(n >= 0)]
/// #[ensures(result == n)]
/// fn count_to_n(n: i32) -> i32 {
///     let mut i = 0;
///     let bound = n; // pre_loop_assignment: bound = n
///     while i < bound {
///         i += 1;
///     }
///     i // return_expr = i
/// }
/// ```
///
/// The loop modifies `i` but not `bound`. With `pre_loop_assignments`
/// mapping `bound → Var("n")`, the postcondition frame mechanism asserts
/// `bound == n` for unmodified variables. Combined with the invariant
/// `i <= bound`, the postcondition `result == n` (where result is
/// substituted with `i`) becomes provable: at loop exit `!(i < bound)`
/// gives `i >= bound`, and invariant `i <= bound` gives `i <= bound`,
/// so `i == bound == n`.
///
/// This test directly exercises AC #4 of issue #759: "loop that modifies
/// only one variable still verifies invariants for others."
#[test]
#[timeout(30000)]
fn test_frame_preservation_unchanged_local_postcondition() {
    // requires: n >= 0
    let requires = ge(var("n"), int(0));

    // invariants: i >= 0 && i <= bound
    let inv_nonneg = ge(var("i"), int(0));
    let inv_bound = le(var("i"), var("bound"));

    // ensures: result == n
    // With return_expr = Some(Var("i")), this becomes i == n after substitution.
    let ensures = eq(var("result"), var("n"));

    // loop condition: i < bound
    let cond = lt(var("i"), var("bound"));

    // body_effect: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // pre_loop_assignments: i = 0, bound = n
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop.insert("bound".to_string(), NamedBindingValue::untyped(var("n")));

    // Only i is modified; bound is unchanged
    let return_expr = var("i");
    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[requires],
        ensures: &[ensures],
        invariants: &[inv_nonneg, inv_bound],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: Some(&return_expr),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // Initialization: requires(n >= 0) ∧ i == 0 ∧ bound == n => i >= 0 ∧ i <= bound
    // i == 0 >= 0 ✓, i == 0 <= bound == n >= 0 ✓
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Initialization should be provable. Got {:?}.",
        result.initialization
    );

    // Preservation: i >= 0 ∧ i <= bound ∧ i < bound => (i+1) >= 0 ∧ (i+1) <= bound
    // i >= 0 => i+1 >= 1 >= 0 ✓
    // i < bound => i+1 <= bound ✓
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "Preservation should be provable. Got {:?}.",
        result.preservation
    );

    // Postcondition: i >= 0 ∧ i <= bound ∧ !(i < bound) ∧ frame(bound == n)
    //   => result == n (where result = i)
    // Frame: bound == n (unchanged local preserved via pre_loop_assignments)
    // !(i < bound) => i >= bound, combined with i <= bound => i == bound == n ✓
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Postcondition should be provable with frame preservation: \
         bound == n from pre_loop_assignments makes i == bound == n. Got {:?}.",
        result.postcondition
    );
}

/// Phase 5 (#759): Frame preservation without explicit invariant for the
/// unchanged local — the postcondition frame alone suffices.
///
/// Models:
/// ```rust
/// #[requires(n > 0)]
/// #[ensures(result >= n)]
/// fn at_least_n(n: i32) -> i32 {
///     let mut sum = 0;
///     let target = n; // pre_loop_assignment: target = n
///     while sum < target {
///         sum += 1;
///     }
///     sum
/// }
/// ```
///
/// Unlike the previous test, there is no explicit invariant referencing `target`.
/// The postcondition `result >= n` relies on:
/// 1. Loop exit: `!(sum < target)` i.e. `sum >= target`
/// 2. Frame: `target == n` (unmodified local)
/// So `sum >= target == n`, proving `result >= n`.
#[test]
#[timeout(30000)]
fn test_frame_preservation_no_explicit_invariant_for_unchanged_local() {
    // requires: n > 0
    let requires = gt(var("n"), int(0));

    // No invariants — this test verifies the frame mechanism alone.
    // (In practice, infer_stable_loop_invariants at the driver level would
    // add `target == n` as an inferred invariant. Here we test the ay-level
    // frame that ensures postcondition correctness.)

    // ensures: result >= n (with return_expr = sum, becomes sum >= n)
    let ensures = ge(var("result"), var("n"));

    // loop condition: sum < target
    let cond = lt(var("sum"), var("target"));

    // body_effect: sum' = sum + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("sum".to_string(), add(var("sum"), int(1)));

    // pre_loop_assignments: sum = 0, target = n
    let mut pre_loop = HashMap::new();
    pre_loop.insert("sum".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop.insert("target".to_string(), NamedBindingValue::untyped(var("n")));

    let return_expr = var("sum");
    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[requires],
        ensures: &[ensures],
        invariants: &[],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["sum"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: Some(&return_expr),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // Initialization is trivially verified (no invariants to check).
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Initialization should be trivially verified (no invariants). Got {:?}.",
        result.initialization
    );

    // Preservation is trivially verified (no invariants to check).
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "Preservation should be trivially verified (no invariants). Got {:?}.",
        result.preservation
    );

    // Postcondition: !(sum < target) ∧ frame(target == n) => sum >= n
    // sum >= target == n ✓
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Postcondition should be provable: frame(target == n) + exit(sum >= target) \
         => sum >= n. Got {:?}.",
        result.postcondition
    );
}
