// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

/// Test: result binding in loop postcondition (#622)
///
/// Uses verify_loop_invariant with return_expr to verify ensures(result == n).
#[test]
#[timeout(30000)]
fn test_loop_postcondition_with_result_binding() {
    // invariant: i >= 0 && i <= n
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    // condition: i < n
    let cond = lt(var("i"), var("n"));

    // ensures: result == n
    let ens = eq(var("result"), var("n"));

    // return_expr: the function returns i after the loop
    let return_expr = var("i");

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &HashMap::new(),
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: Some(&return_expr),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Postcondition result==n should verify with return_expr binding: got {:?}",
        result.postcondition
    );
}

/// Test: without return_expr, result is unbound and postcondition fails (#622 regression guard)
#[test]
#[timeout(30000)]
fn test_loop_postcondition_result_unbound_fails() {
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    let cond = lt(var("i"), var("n"));

    // ensures: result == n (but result is NOT bound)
    let ens = eq(var("result"), var("n"));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
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

    // Without result binding, the postcondition should fail:
    // result is unconstrained, so the solver can set result != n.
    assert!(
        matches!(result.postcondition, VerificationResult::Failed(_)),
        "Postcondition result==n should FAIL without return_expr binding: got {:?}",
        result.postcondition
    );
}

/// Test: different return variable (sum) with result binding (#622)
///
/// The postcondition `result >= 0` requires non-trivial reasoning after
/// return_expr substitution (result → sum):
/// - The invariant does NOT directly state `sum >= 0`
/// - Instead, proving `sum >= 0` requires combining `sum == i` with `i >= 0`
///   via transitivity: sum == i ∧ i >= 0 → sum >= 0
///
/// This exercises return_expr substitution for a non-counter variable AND
/// verifies the solver can chain equalities with inequalities.
///
/// ```
/// #[requires(n >= 0)]
/// #[ensures(result >= 0)]
/// #[invariant(i >= 0 && i <= n && sum == i)]
/// fn accumulate(n: i32) -> i32 {
///     let mut i = 0;
///     let mut sum = 0;
///     while i < n {
///         i += 1;
///         sum += 1;
///     }
///     sum // return_expr = Var("sum")
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_loop_postcondition_sum_with_result() {
    // invariant: i >= 0 && i <= n && sum == i
    // Note: sum >= 0 is NOT a direct clause — the solver must derive it
    // from sum == i ∧ i >= 0.
    let inv = and(
        and(ge(var("i"), int(0)), le(var("i"), var("n"))),
        eq(var("sum"), var("i")),
    );

    // condition: i < n
    let cond = lt(var("i"), var("n"));

    // ensures: result >= 0 (requires sum == i ∧ i >= 0 → sum >= 0)
    let ens = ge(var("result"), int(0));

    // return_expr: the function returns sum (not i)
    let return_expr = var("sum");

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &HashMap::new(),
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: Some(&return_expr),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Postcondition result>=0 should verify via sum==i ∧ i>=0 with return_expr=sum: got {:?}",
        result.postcondition
    );
}

/// Regression test for #654: verify_loop_invariant with type_invariants parameter.
///
/// Type invariant: invariant(self) = self > 0
/// Loop: while i < n { i += 1; }
/// Requires: n > 0
/// Invariants: [n > 0, i >= 0 && i <= n]
/// Ensures: n.invariant()  (evaluates to n > 0 via the type invariant axiom)
///
/// With type invariant registered, postcondition should verify because
/// invariant(n) is defined as n > 0, and n > 0 is preserved as a loop invariant.
/// Without the axiom, invariant(n) is an unconstrained UF call and postcondition fails.
///
/// Note: n > 0 must be a loop invariant (not just a precondition) because the
/// postcondition check only has invariants + ¬condition, not preconditions.
#[test]
#[timeout(30000)]
fn test_loop_invariant_with_type_invariant_axiom() {
    // Type invariant: invariant(self) = self > 0
    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None, // Int
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: n > 0
    let req = gt(var("n"), int(0));

    // ensures: n.invariant()
    let ens = method_call(
        var("n"),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // invariant 1: n > 0 (preserved from precondition — n is not modified)
    let inv_n_pos = gt(var("n"), int(0));

    // invariant 2: i >= 0 && i <= n
    let inv_bounds = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    // loop condition: i < n
    let cond = lt(var("i"), var("n"));

    // body effect: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // WITH type invariant axiom: postcondition should verify
    let result_with = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: std::slice::from_ref(&ens),
        invariants: &[inv_n_pos.clone(), inv_bounds.clone()],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig {
            transition_facts: vec![],
            type_invariants: Some(&[inv_def]),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    assert!(
        matches!(result_with.postcondition, VerificationResult::Verified(_)),
        "With type invariant axiom, postcondition n.invariant() should verify: got {:?}",
        result_with.postcondition
    );

    // WITHOUT type invariant axiom: postcondition should NOT verify
    let result_without = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[ens],
        invariants: &[inv_n_pos, inv_bounds],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
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
        matches!(result_without.postcondition, VerificationResult::Failed(_)),
        "Without type invariant axiom, postcondition should produce Failed (invariant() is \
         uninterpreted UF, solver finds counterexample): got {:?}",
        result_without.postcondition
    );
}
