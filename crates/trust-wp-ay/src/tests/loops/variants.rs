// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::{results_and_counterexamples::dummy_cex, *};

// Tests for variant verification (Part of #80 - termination checking)

#[test]
#[timeout(30000)]
fn test_loop_variant_nonneg_nonfailing_without_fallback() {
    // Test: variant n - i is non-negative when invariant holds and loop continues
    // invariant: i >= 0 && i <= n
    // condition: i < n
    // variant: n - i
    //
    // Check: (i >= 0 && i <= n) && (i < n) => (n - i >= 0)
    // This should verify since i <= n and i < n implies n - i >= 0

    let req1 = ge(var("n"), int(0));
    let req2 = eq(var("i"), int(0));

    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    let cond = lt(var("i"), var("n"));

    // Variant: n - i (decreases each iteration)
    let variant = sub(var("n"), var("i"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req1, req2],
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

    assert!(
        result.variant_nonneg.is_some(),
        "Variant non-negative check should be performed"
    );
    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Verified(_))),
        "Variant non-negative should verify (native lt/gt): got {:?}",
        result.variant_nonneg
    );
}

#[test]
#[timeout(30000)]
fn test_loop_variant_decrease_verifies() {
    // Test: variant n - i decreases when body sets i = i + 1
    // variant: n - i
    // variant': n - (i + 1)
    //
    // Check: n - (i + 1) < n - i  =>  -1 < 0 which is TRUE

    let req1 = ge(var("n"), int(0));
    let req2 = eq(var("i"), int(0));

    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    let cond = lt(var("i"), var("n"));

    // Variant: n - i (decreases each iteration)
    let variant = sub(var("n"), var("i"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req1, req2],
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

    assert!(
        result.variant_decrease.is_some(),
        "Variant decrease check should be performed"
    );
    assert!(
        matches!(
            result.variant_decrease,
            Some(VerificationResult::Verified(_))
        ),
        "Variant should strictly decrease: got {:?}",
        result.variant_decrease
    );
}

#[test]
#[timeout(30000)]
fn test_loop_variant_contradictory_invariants_demote_to_vacuous_unknown() {
    // Contradictory invariants make the shared base UNSAT. Both variant
    // obligations must demote to Unknown(vacuous) rather than returning the
    // old vacuous Verified result.
    let inv = and(gt(var("i"), int(0)), lt(var("i"), int(0)));
    let cond = eq(var("i"), var("i"));
    let bad_variant = neg(int(1));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&bad_variant),
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Unknown(_))),
        "Contradictory invariants should demote variant_nonneg to Unknown(vacuous), got {:?}",
        result.variant_nonneg
    );
    if let Some(VerificationResult::Unknown(reason)) = &result.variant_nonneg {
        let msg = format!("{reason:?}");
        assert!(
            msg.contains("vacuous"),
            "Variant nonneg Unknown reason should mention vacuity, got: {msg}"
        );
    }

    assert!(
        matches!(
            result.variant_decrease,
            Some(VerificationResult::Unknown(_))
        ),
        "Contradictory invariants should demote variant_decrease to Unknown(vacuous), got {:?}",
        result.variant_decrease
    );
    if let Some(VerificationResult::Unknown(reason)) = &result.variant_decrease {
        let msg = format!("{reason:?}");
        assert!(
            msg.contains("vacuous"),
            "Variant decrease Unknown reason should mention vacuity, got: {msg}"
        );
    }
}

#[test]
#[timeout(30000)]
fn test_loop_variant_full_termination() {
    // Full termination proof with all variant conditions
    // This proves the counting loop terminates.

    let req1 = ge(var("n"), int(0));
    let req2 = eq(var("i"), int(0));

    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    let cond = lt(var("i"), var("n"));

    let ens = eq(var("i"), var("n"));

    // Variant: n - i
    let variant = sub(var("n"), var("i"));

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
        variant: Some(&variant),
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // All loop checks should now return Verified with native lt/gt handling.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Initialization should verify: got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "Preservation should verify (native lt/gt): got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Postcondition should verify: got {:?}",
        result.postcondition
    );
    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Verified(_))),
        "Variant nonneg should verify (native lt/gt): got {:?}",
        result.variant_nonneg
    );
    assert!(
        matches!(
            result.variant_decrease,
            Some(VerificationResult::Verified(_))
        ),
        "Variant decrease should verify: got {:?}",
        result.variant_decrease
    );
}

#[test]
#[timeout(30000)]
fn test_loop_variant_all_verified_with_variants() {
    // Test that all_verified checks variant conditions
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Verified(None)),
        variant_decrease: Some(VerificationResult::Verified(None)),
    };
    assert!(
        result.all_verified(),
        "all verified with variants should pass: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_loop_variant_all_verified_fails_on_nonneg() {
    // Test that all_verified fails when variant_nonneg fails
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Failed(dummy_cex())),
        variant_decrease: Some(VerificationResult::Verified(None)),
    };
    assert!(
        !result.all_verified(),
        "failed variant_nonneg should cause all_verified=false: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_loop_variant_all_verified_fails_on_decrease() {
    // Test that all_verified fails when variant_decrease fails
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: Some(VerificationResult::Verified(None)),
        variant_decrease: Some(VerificationResult::Failed(dummy_cex())),
    };
    assert!(
        !result.all_verified(),
        "failed variant_decrease should cause all_verified=false: {result:?}"
    );
}
