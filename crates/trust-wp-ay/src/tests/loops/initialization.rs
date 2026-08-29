// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::*;

/// Test: Simple counting loop
/// ```
/// #[requires(n >= 0)]
/// #[ensures(result == n)]
/// #[invariant(i >= 0 && i <= n)]
/// fn count_to(n: i32) -> i32 {
///     let mut i = 0;
///     while i < n {
///         i += 1;
///     }
///     i
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_loop_initialization_valid() {
    // requires: n >= 0
    let req = ge(var("n"), int(0));

    // invariant: i >= 0 && i <= n
    // For initialization, i = 0, so we check: 0 >= 0 && 0 <= n
    // Since n >= 0, this should hold
    let inv1 = ge(var("i"), int(0));
    let inv2 = le(var("i"), var("n"));
    let inv = and(inv1, inv2);

    // At loop entry, i = 0, so we substitute i = 0 in the precondition context
    // Actually, for initialization we need: requires => inv[i/0]
    // But verify_loop_invariant takes the invariant as-is and checks requires => inv
    // We need to set up the state properly...

    // For this test, we just verify the API works correctly
    // Full semantic test requires proper state setup

    let ens = bool_expr(true); // Trivial postcondition for this test

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &HashMap::new(),
        deref_body_effect: &HashMap::new(),
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

    // Initialization should fail because i is not constrained to 0 in precondition
    // This is expected - the invariant needs to be checked at the actual initial state
    // In practice, we'd need i = 0 to be added as a precondition or the invariant
    // would be established by the assignment statement
    assert!(
        matches!(result.initialization, VerificationResult::Failed(_)),
        "Without i=0 constraint, initialization should fail"
    );
}

/// Test: Pre-loop assignments fix initialization (#563)
///
/// Same setup as `test_loop_initialization_valid` (which fails because i is
/// unconstrained), but now we pass `pre_loop_assignments: {i: 0}` to simulate
/// `let mut i = 0;` before the loop. Initialization should succeed.
#[test]
#[timeout(30000)]
fn test_loop_initialization_with_pre_loop_assignment() {
    // requires: n >= 0
    let req = ge(var("n"), int(0));

    // invariant: i >= 0 && i <= n
    let inv1 = ge(var("i"), int(0));
    let inv2 = le(var("i"), var("n"));
    let inv = and(inv1, inv2);

    let ens = bool_expr(true);

    // Pre-loop assignment: i = 0 (simulates `let mut i = 0;`)
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &HashMap::new(),
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // With pre-loop assignment i=0: n >= 0 ∧ i == 0 => i >= 0 ∧ i <= n
    // This should now verify (0 >= 0 is true, 0 <= n is true when n >= 0)
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "With pre-loop i=0, initialization should verify: got {:?}",
        result.initialization
    );
}

#[test]
#[timeout(30000)]
fn test_loop_initialization_with_initial_value() {
    // Test with explicit initial value in preconditions
    // requires: n >= 0 && i == 0
    let req1 = ge(var("n"), int(0));
    let req2 = eq(var("i"), int(0));

    // invariant: i >= 0 && i <= n
    let inv1 = ge(var("i"), int(0));
    let inv2 = le(var("i"), var("n"));
    let inv = and(inv1, inv2);

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req1, req2],
        ensures: &[],
        invariants: &[inv],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &HashMap::new(),
        deref_body_effect: &HashMap::new(),
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

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "With i=0 in precondition, initialization should verify"
    );
}
