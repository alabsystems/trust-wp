// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// --- Variant Lt-inside-Implies coverage tests ---
//
// These tests exercise variant checks under Implies-shaped conditions that
// include strict inequalities.

/// Test: variant nonneg with Lt inside Implies condition.
///
/// invariant: `i >= 0 && i <= n`
/// condition: `(i >= 0) ==> (i < n)`
/// variant: `n - i`
///
/// The variant `n - i >= 0` is guaranteed by invariant `i <= n`.
#[test]
#[timeout(30000)]
fn test_variant_nonneg_lt_inside_implies() {
    let inv1 = ge(var("i"), int(0));
    let inv2 = le(var("i"), var("n"));

    // condition: (i >= 0) ==> (i < n)
    let cond = implies(ge(var("i"), int(0)), lt(var("i"), var("n")));

    // variant: n - i
    let variant = sub(var("n"), var("i"));

    // Body effect: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // Preconditions for initialization
    let req_n = ge(var("n"), int(0));
    let req_i = eq(var("i"), int(0));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req_n, req_i],
        ensures: &[],
        invariants: &[inv1, inv2],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&variant),
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // Variant nonneg should be checked and proven.
    assert!(
        result.variant_nonneg.is_some(),
        "Variant nonneg check should be performed"
    );
    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Verified(_))),
        "Variant n-i should verify non-negative when i <= n: got {:?}",
        result.variant_nonneg
    );
}

/// Test: variant decrease with Lt inside Implies condition.
///
/// invariant: `i >= 0 && i <= n`
/// condition: `(i >= 0) ==> (i < n)`
/// variant: `n - i`
/// body: `i' = i + 1`
///
/// Variant decrease: `(n - (i+1)) < (n - i)` simplifies to `-1 < 0` which is true.
#[test]
#[timeout(30000)]
fn test_variant_decrease_lt_inside_implies() {
    let inv1 = ge(var("i"), int(0));
    let inv2 = le(var("i"), var("n"));

    // condition: (i >= 0) ==> (i < n)
    let cond = implies(ge(var("i"), int(0)), lt(var("i"), var("n")));

    // variant: n - i
    let variant = sub(var("n"), var("i"));

    // Body effect: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // Preconditions for initialization
    let req_n = ge(var("n"), int(0));
    let req_i = eq(var("i"), int(0));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req_n, req_i],
        ensures: &[],
        invariants: &[inv1, inv2],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&variant),
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // Variant decrease should be checked and proven.
    assert!(
        result.variant_decrease.is_some(),
        "Variant decrease check should be performed"
    );
    assert!(
        matches!(
            result.variant_decrease,
            Some(VerificationResult::Verified(_))
        ),
        "Variant n-i should verify decrease when i'=i+1: got {:?}",
        result.variant_decrease
    );
}

/// Test: variant nonneg correctly rejects bad variant with Implies condition.
///
/// invariant: `i <= n`
/// condition: `(i >= 0) ==> (i < n)`
/// variant: `i` (wrong — NOT non-negative when i < 0)
///
/// Counterexample: `i = -1, n = 0`. The condition is vacuously true
/// (antecedent false). Variant `i = -1 >= 0` is false.
///
/// This verifies primary nonneg check correctness with an Implies-shaped
/// condition.
#[test]
#[timeout(30000)]
fn test_variant_nonneg_rejects_bad_variant_with_implies_condition() {
    let inv = le(var("i"), var("n"));

    // condition: (i >= 0) ==> (i < n)
    let cond = implies(ge(var("i"), int(0)), lt(var("i"), var("n")));

    // variant: i (wrong — not non-negative for i < 0)
    let variant = var("i");

    // Body effect: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // Preconditions — just i = 0 to make init work
    let req_i = eq(var("i"), int(0));
    let req_n = ge(var("n"), int(0));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req_i, req_n],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&variant),
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // Variant nonneg should detect failure: i can be negative (invariant
    // only says i <= n, not i >= 0). The result should never be Verified
    // since the variant IS negative for some states.
    // Accept Failed or Unknown (Unknown is conservative-correct).
    assert!(
        result.variant_nonneg.is_some(),
        "Variant nonneg check should be performed"
    );
    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Failed(_))),
        "Variant 'i' should be Failed with counterexample (i=-1, n=0), got {:?}",
        result.variant_nonneg
    );
}
