// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_loop_preservation() {
    // Test: inv && cond => inv'
    // invariant: i >= 0 && i <= n
    // condition: i < n
    // body: i = i + 1
    //
    // Check: (i >= 0 && i <= n) && (i < n) => ((i+1) >= 0 && (i+1) <= n)

    let inv1 = ge(var("i"), int(0));
    let inv2 = le(var("i"), var("n"));

    let cond = lt(var("i"), var("n"));

    // Body effect: i' = i + 1
    let i_plus_1 = add(var("i"), int(1));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), i_plus_1);

    let result = verify_preservation(
        &[inv1, inv2],
        Some(&cond),
        &["i"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Loop preservation should verify (QF_LIA decidable): got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_loop_postcondition() {
    // Test: inv && ¬cond => ensures
    // invariant: i >= 0 && i <= n
    // condition: i < n
    // ensures: i == n (result of counting loop)
    //
    // When loop exits: ¬(i < n) => i >= n
    // Combined with inv (i <= n): i >= n && i <= n => i == n ✓

    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    // Loop condition: i < n
    let cond = lt(var("i"), var("n"));

    // Postcondition: i == n
    let ens = eq(var("i"), var("n"));

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

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Postcondition i==n should verify when loop exits"
    );
}

#[test]
#[timeout(30000)]
fn test_loop_full_verification() {
    // Full loop verification for counting loop.
    let req1 = ge(var("n"), int(0));
    let req2 = eq(var("i"), int(0));

    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    let cond = lt(var("i"), var("n"));

    let ens = eq(var("i"), var("n"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req1, req2],
        ensures: &[ens],
        invariants: &[inv],
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
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Full loop initialization should verify: got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "Full loop preservation should verify (native lt/gt): got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Full loop postcondition should verify: got {:?}",
        result.postcondition
    );
}

#[test]
#[timeout(30000)]
fn test_loop_wrong_invariant_auto_strengthened() {
    // User invariant: only i >= 0 (missing i <= n).
    // Auto-invariant synthesis from condition `i < n` adds `i <= n`.
    // Combined with `!(i < n)` at loop exit, we get `i == n`, so the
    // postcondition now verifies.

    let req1 = ge(var("n"), int(0));
    let req2 = eq(var("i"), int(0));

    let ens = eq(var("i"), var("n"));

    // Incomplete user invariant — auto-invariant closes the gap.
    let inv = ge(var("i"), int(0));

    let cond = lt(var("i"), var("n"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req1, req2],
        ensures: &[ens],
        invariants: &[inv],
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

    // Auto-invariant synthesis adds `i <= n`, postcondition now verifies.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Auto-invariant should strengthen incomplete user invariant: got {:?}",
        result.postcondition
    );
}
