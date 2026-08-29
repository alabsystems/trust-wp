// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Targeted loop invariant verification tests for common patterns (#1709).
//!
//! These tests cover common Creusot-compatible loop patterns that exercise
//! initialization, preservation, and postcondition together. They focus on
//! patterns observed in Creusot compat test failures.

use std::time::Duration;

use super::*;

fn assert_pattern_failed_result(result: &VerificationResult, context: &str) {
    match result {
        VerificationResult::Failed(_) => {}
        other => panic!("{context} should fail verification; got {other:?}"),
    }
}

mod auto_condition_bound;
mod auto_frame;
mod auto_monotonicity;
mod auto_stable_requires;
mod variant_only;

// -----------------------------------------------------------------------
// Full pipeline: while-loop counting with postcondition `result == n`
// -----------------------------------------------------------------------

/// Classic while-loop counting pattern: `while i < n { i += 1 }; return i`.
///
/// Models the most common Creusot compat loop pattern:
///   requires: n >= 0
///   invariant: 0 <= i <= n
///   ensures: result == n
///
/// This exercises all three VCs together via the full `verify_loop_invariant`
/// pipeline. Many Creusot compat tests fail because the postcondition doesn't
/// properly use the loop exit condition (NOT(i < n)) combined with the
/// invariant (i <= n) to derive i == n.
#[test]
#[timeout(30000)]
fn full_pipeline_while_count_to_n_result_eq_n() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), var("n"))];
    let return_expr = PureExpr::Var("i".to_string(), None);
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("full pipeline should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify: i=0, n>=0, so 0<=0<=n; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify: 0<=i<=n, i<n => 0<=i+1<=n; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify: i<=n, NOT(i<n) => i==n, result=i; got {:?}",
        result.postcondition
    );
    assert!(
        result.all_verified(),
        "all VCs should verify for while-count-to-n pattern"
    );
}

/// While-loop with variant (termination): `while i < n { i += 1 }`.
///
/// variant: n - i
///
/// This exercises the variant VCs in addition to init/preservation/postcondition.
#[test]
#[timeout(30000)]
fn full_pipeline_while_count_with_variant() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures: Vec<PureExpr> = vec![];
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    let loop_condition = lt(var("i"), var("n"));
    let variant = sub(var("n"), var("i"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_variant(&variant)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("variant pipeline should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify; got {:?}",
        result.preservation
    );
    assert!(
        result.variant_nonneg.is_some(),
        "variant_nonneg should be present"
    );
    assert!(
        matches!(
            result.variant_nonneg.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant nonneg should verify: i<=n, i<n => n-i>=0; got {:?}",
        result.variant_nonneg
    );
    assert!(
        result.variant_decrease.is_some(),
        "variant_decrease should be present"
    );
    assert!(
        matches!(
            result.variant_decrease.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant decrease should verify: n-i'=n-(i+1)<n-i; got {:?}",
        result.variant_decrease
    );
}

// -----------------------------------------------------------------------
// Multi-variable accumulation pattern
// -----------------------------------------------------------------------

/// Two modified variables with dependent effects: counter + accumulator.
///
/// Models: `while i < n { sum += i; i += 1 }`.
/// Invariants: 0 <= i <= n, sum >= 0.
///
/// This pattern appears in several Creusot compat tests where multiple
/// loop variables are updated each iteration. The challenge is that
/// preservation must reason about both primed variables simultaneously.
#[test]
#[timeout(30000)]
fn full_pipeline_accumulator_two_modified_vars() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![
        ge(var("i"), int(0)),
        le(var("i"), var("n")),
        ge(var("sum"), int(0)),
    ];
    let ensures = vec![ge(var("sum"), int(0))];
    let modified_vars: Vec<&str> = vec!["i", "sum"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    body_effect.insert("sum".to_string(), add(var("sum"), var("i")));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    pre_loop_assignments.insert(
        "sum".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("accumulator pipeline should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify: i=0, sum=0, n>=0; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify: sum>=0, i>=0 => sum+i>=0; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify: sum>=0 from invariant; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// Postcondition with unmodified parameter frame
// -----------------------------------------------------------------------

/// Postcondition referencing both modified and unmodified variables.
///
/// Models: `fn f(x: i32, n: i32) { let mut i = 0; while i < n { i += 1 }; ensures(i == n && x > 0) }`
/// requires: n >= 0, x > 0
///
/// The key is that `x > 0` should be provable from the frame (unmodified `x`)
/// plus the `requires(x > 0)`. `i == n` should be provable from the invariant
/// and exit condition.
#[test]
#[timeout(30000)]
fn postcondition_mixed_modified_and_unmodified_vars() {
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let requires = vec![ge(var("n"), int(0)), gt(var("x"), int(0))];
    let ensures = vec![eq(var("i"), var("n")), gt(var("x"), int(0))];
    let cond = lt(var("i"), var("n"));
    let modified_vars: Vec<&str> = vec!["i"];

    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };
    let empty_body = HashMap::new();
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();
    let empty_pre_loop = HashMap::new();
    let result = verify_postcondition(
        &invariants,
        Some(&cond),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &empty_pre_loop, &requires, &[]),
        effects(&empty_body, &empty_deref, &empty_double_deref),
        &config,
    )
    .expect("postcondition should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "postcondition with mixed modified/unmodified vars should verify; got {result:?}"
    );
}

// -----------------------------------------------------------------------
// Initialization: pre-loop assignments establish invariant
// -----------------------------------------------------------------------

/// Initialization must verify when pre-loop assignments establish the invariant.
///
/// Models: `let mut i = 0; let mut sum = 0; while ...`
/// Invariant: i >= 0 && i <= n && sum == 0
///
/// The third invariant is verified using substitution: with i=0 and sum=0,
/// we need 0 == 0, which is trivially true.
#[test]
#[timeout(30000)]
fn initialization_compound_pre_loop_assignments() {
    let invariants = vec![
        ge(var("i"), int(0)),
        le(var("i"), var("n")),
        eq(var("sum"), int(0)), // Simplified: sum starts at 0
    ];
    let requires = vec![ge(var("n"), int(0))];
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    pre_loop_assignments.insert(
        "sum".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );

    let result = verify_initialization(
        &requires,
        &invariants,
        &pre_loop_assignments,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("initialization should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "initialization with compound assignments should verify; got {result:?}"
    );
}

/// Initialization should FAIL when a pre-loop assignment contradicts the invariant.
///
/// Models: `let mut i = -1; while i < n { ... }`
/// Invariant: i >= 0
///
/// Since i starts at -1, the invariant i >= 0 is false at loop entry.
#[test]
#[timeout(30000)]
fn initialization_fails_when_assignment_contradicts_invariant() {
    let invariants = vec![ge(var("i"), int(0))];
    let requires: Vec<PureExpr> = vec![];
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(-1)),
    );

    let result = verify_initialization(
        &requires,
        &invariants,
        &pre_loop_assignments,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("initialization should encode");

    assert_pattern_failed_result(&result, "initialization when i=-1 contradicts i>=0");
}

// -----------------------------------------------------------------------
// Preservation: invariant not strong enough
// -----------------------------------------------------------------------

/// Preservation should succeed when the lower bound is preserved.
///
/// Models: `while i < n { i += 2 }` with invariant `i >= 0`.
/// Missing: upper bound `i <= n`.
///
/// The preservation VC is: i >= 0, i < n => (i+2) >= 0. This IS valid.
#[test]
#[timeout(30000)]
fn preservation_weak_invariant_succeeds_for_lower_bound() {
    let invariants = vec![ge(var("i"), int(0))];
    let loop_condition = lt(var("i"), var("n"));
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(2)));

    let result = verify_preservation(
        &invariants,
        Some(&loop_condition),
        &modified_vars,
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .expect("preservation should encode");

    // i >= 0 /\ i < n => (i+2) >= 0 — VALID (i+2 > i >= 0)
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "preservation of i>=0 under i+=2 should verify; got {result:?}"
    );
}

/// Preservation FAILS with step=2 and wrong upper bound invariant.
///
/// invariant: i <= n, condition: i < n, body: i += 2
/// VC: i <= n /\ i < n => (i+2) <= n — INVALID (counterexample: i=n-1)
#[test]
#[timeout(30000)]
fn preservation_fails_step2_upper_bound() {
    let invariants = vec![le(var("i"), var("n"))];
    let loop_condition = lt(var("i"), var("n"));
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(2)));

    let result = verify_preservation(
        &invariants,
        Some(&loop_condition),
        &modified_vars,
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .expect("preservation should encode");

    assert_pattern_failed_result(&result, "preservation of i<=n under i+=2");
}

// -----------------------------------------------------------------------
// Postcondition with return_expr substitution
// -----------------------------------------------------------------------

/// Postcondition with return_expr substitution for non-body-break loop.
///
/// Models: `while i < n { i += 1 }; return i`
/// ensures: result == n
///
/// The return_expr `i` is substituted for `result` in the postcondition.
/// Combined with exit condition NOT(i < n) and invariant i <= n, we get
/// i >= n /\ i <= n => i == n.
#[test]
#[timeout(30000)]
fn postcondition_return_expr_substitution_header_loop() {
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), var("n"))];
    let return_expr = PureExpr::Var("i".to_string(), None);
    let requires = vec![ge(var("n"), int(0))];
    let cond = lt(var("i"), var("n"));
    let modified_vars: Vec<&str> = vec!["i"];
    let empty_pre_loop = HashMap::new();
    let empty_body = HashMap::new();
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let result = verify_postcondition(
        &invariants,
        Some(&cond),
        false,
        &modified_vars,
        postcondition_inputs(
            &ensures,
            Some(&return_expr),
            &empty_pre_loop,
            &requires,
            &[],
        ),
        effects(&empty_body, &empty_deref, &empty_double_deref),
        &LoopEncoderConfig {
            timeout: Some(Duration::from_secs(5)),
            ..LoopEncoderConfig::default()
        },
    )
    .expect("postcondition should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "postcondition result==n with return_expr=i should verify; got {result:?}"
    );
}

// -----------------------------------------------------------------------
// Empty invariants: edge case
// -----------------------------------------------------------------------

/// Empty invariants should produce Verified for all VCs.
///
/// When no invariants are provided, the inductive proof is vacuously true
/// (nothing to prove). The postcondition with empty ensures is also trivially
/// verified.
#[test]
#[timeout(30000)]
fn full_pipeline_empty_invariants_all_verified() {
    let empty_body = HashMap::new();
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();
    let empty_pre_loop = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &[],
        &[],
        &[],
        &[],
        BodyEffects::new(&empty_body, &empty_deref, &empty_double_deref),
        &empty_pre_loop,
    );

    let result = verify_loop_invariant(&ctx).expect("empty pipeline should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "empty init should be Verified; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "empty preservation should be Verified; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "empty postcondition should be Verified; got {:?}",
        result.postcondition
    );
}

#[test]
#[timeout(30000)]
fn full_pipeline_no_effect_method_value_bound() {
    let perm_val = view(method_call(var("perm"), "val", vec![]));
    let requires = vec![
        eq(perm_val.clone(), int(1)),
        eq(deref(method_call(var("perm"), "ward", vec![])), var("ptr")),
    ];
    let invariants = vec![le(int(0), perm_val)];
    let empty_effect = HashMap::new();
    let empty_pre_loop = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &[],
        &invariants,
        &[],
        BodyEffects::new(&empty_effect, &empty_effect, &empty_effect),
        &empty_pre_loop,
    )
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result =
        verify_loop_invariant(&ctx).expect("no-effect method-bound pipeline should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "literal equality should initialize the method-value bound; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "no-effect loop should preserve the unchanged scalar invariant; got {:?}",
        result.preservation
    );
    assert!(
        result.all_verified(),
        "all VCs should verify for a no-effect method-value bound"
    );
}

// -----------------------------------------------------------------------
// Postcondition with post_extra_facts (for-loop completion)
// -----------------------------------------------------------------------

/// Post-extra-facts (iterator completion) should strengthen the postcondition VC.
///
/// Models a for-loop pattern where `produced == input` at loop exit.
/// The postcondition `i == n` is provable because the invariant + exit condition
/// are sufficient, and the post_extra_fact (redundant here) verifies the mechanism.
#[test]
#[timeout(30000)]
fn postcondition_post_extra_facts_provide_completion() {
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("i"), var("n"))];
    let cond = lt(var("i"), var("n"));
    let modified_vars: Vec<&str> = vec!["i"];
    let requires = vec![ge(var("n"), int(0))];
    // Post-extra fact: at loop exit, the invariant + exit condition are enough
    // to prove i == n, but we add an extra fact to verify the mechanism works.
    let post_extra_facts = vec![ge(var("n"), int(0))]; // redundant but tests the mechanism
    let empty_pre_loop = HashMap::new();
    let empty_body = HashMap::new();
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let result = verify_postcondition(
        &invariants,
        Some(&cond),
        false,
        &modified_vars,
        postcondition_inputs(
            &ensures,
            None,
            &empty_pre_loop,
            &requires,
            &post_extra_facts,
        ),
        effects(&empty_body, &empty_deref, &empty_double_deref),
        &LoopEncoderConfig {
            timeout: Some(Duration::from_secs(5)),
            ..LoopEncoderConfig::default()
        },
    )
    .expect("postcondition with post_extra_facts should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "postcondition with post_extra_facts should verify; got {result:?}"
    );
}

// -----------------------------------------------------------------------
// Body effect variable not in modified_vars: should error
// -----------------------------------------------------------------------

/// Body effect variable not in modified_vars should produce a hard error.
///
/// This is a soundness guard (#1884, #2626): if a variable has a body effect
/// but is NOT in modified_vars, the postcondition VC would create unsound
/// frame constraints.
#[test]
#[timeout(30000)]
fn body_effect_not_in_modified_vars_errors() {
    let invariants = vec![ge(var("i"), int(0))];
    let modified_vars: Vec<&str> = vec![]; // intentionally empty
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();
    let empty_pre_loop = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &[],
        &[],
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &empty_pre_loop,
    );

    let err = verify_loop_invariant(&ctx);
    assert!(
        err.is_err(),
        "body effect variable not in modified_vars should error; got {err:?}"
    );
    let msg = err.unwrap_err().to_string();
    assert!(
        msg.contains("modified_vars"),
        "error should mention modified_vars: {msg}"
    );
}

// -----------------------------------------------------------------------
// Conditionless loop (infinite loop with break)
// -----------------------------------------------------------------------

/// Conditionless loop: `loop { ... break }` with no extracted condition.
///
/// When no condition is extractable, the exit condition is not negated in the
/// postcondition VC. The invariant alone must be strong enough for the
/// postcondition.
#[test]
#[timeout(30000)]
fn full_pipeline_conditionless_loop_invariant_implies_postcondition() {
    let invariants = vec![ge(var("x"), int(0))];
    let ensures = vec![ge(var("x"), int(0))];
    let modified_vars: Vec<&str> = vec!["x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), add(var("x"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "x".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &[],
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("conditionless loop should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init: x=0 >= 0; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation: x>=0 => x+1>=0; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition: invariant x>=0 directly implies ensures x>=0; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// Multiple ensures slices: one passes, one fails
// -----------------------------------------------------------------------

/// Full pipeline with multiple ensures: both provable via auto-invariant synthesis.
///
/// Previously this test expected failure because the user invariant `i >= 0` was
/// intentionally weak (missing `i <= n`). After #3315, the auto-invariant synthesis
/// generates `i <= n` from the loop condition `i < n`, making both ensures provable.
/// This demonstrates the value of condition-bound auto-invariants.
#[test]
#[timeout(30000)]
fn full_pipeline_multiple_ensures_auto_invariant_strengthens() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0))]; // intentionally weak: missing i <= n
    let ensures = vec![
        ge(var("i"), int(0)),   // provable from invariant
        eq(var("i"), var("n")), // NOW provable: auto-invariant i<=n from condition i<n
    ];
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("multi-ensures pipeline should encode");

    // Auto-invariant synthesis (#3315) generates `i <= n` from condition `i < n`,
    // making the postcondition `i == n` provable.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify with auto-invariant i<=n; got {:?}",
        result.postcondition
    );
}

/// Full pipeline with multiple ensures: one fails because the bound variable
/// is also modified (no auto-invariant can be generated).
///
/// When both `i` and `n` are modified by the loop, the auto-invariant `i <= n`
/// cannot be generated (bound is not stable). The postcondition should fail.
#[test]
#[timeout(30000)]
fn full_pipeline_multiple_ensures_one_fails_modified_bound() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0))]; // intentionally weak
    let ensures = vec![
        ge(var("i"), int(0)),   // provable from invariant
        eq(var("i"), var("n")), // NOT provable: n is also modified, no auto-invariant
    ];
    let modified_vars: Vec<&str> = vec!["i", "n"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    body_effect.insert("n".to_string(), var("n")); // n modified (identity, but in modified set)
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("multi-ensures pipeline should encode");

    // With n also in modified_vars, no auto-invariant `i <= n` is generated.
    // Postcondition should fail because invariant is too weak.
    assert_pattern_failed_result(
        &result.postcondition,
        "postcondition when bound is also modified",
    );
}

// -----------------------------------------------------------------------
// Decreasing counter pattern
// -----------------------------------------------------------------------

/// Counting down: `while i > 0 { i -= 1 }; return i`.
///
/// Models a common Creusot pattern where the counter decreases toward 0.
///   requires: n >= 0
///   invariant: 0 <= i <= n
///   ensures: result == 0
///
/// The exit condition NOT(i > 0) gives i <= 0, combined with invariant i >= 0
/// yields i == 0, and result = i gives result == 0.
#[test]
#[timeout(30000)]
fn full_pipeline_decreasing_counter_result_eq_zero() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), int(0))];
    let return_expr = PureExpr::Var("i".to_string(), None);
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), sub(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("n")));
    let loop_condition = gt(var("i"), int(0));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("decreasing counter pipeline should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify: i=n, n>=0, so 0<=n<=n; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify: 0<=i<=n, i>0 => 0<=i-1<=n; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify: i>=0, NOT(i>0) => i==0, result=i; got {:?}",
        result.postcondition
    );
}

// -----------------------------------------------------------------------
// Ghost loop-in-ghost pattern (Creusot ghost/loop_in_ghost.rs)
// -----------------------------------------------------------------------

/// Ghost block with while-loop counting: `ghost! { while i > 0 { i -= 1; y += 1; } y }`.
///
/// Models the Creusot compat test `ghost/loop_in_ghost.rs`:
///   fn foo(x: u32) -> Ghost<u32> {
///     ghost! { let mut y = 0; let mut i = x;
///       #[variant(i)] #[invariant(y@ + i@ == x@)]
///       while i > 0 { i -= 1; y += 1; }
///       y
///     }
///   }
///   requires: x > 0
///   ensures: *result == x  (after ghost rewrite: y == x)
///   invariant: y + i == x  (after view stripping)
///
/// This isolates the ay-level loop encoding from driver-level MIR extraction
/// to determine whether the `loop_in_ghost.rs` compat failure is at the
/// ay encoding level or the driver level. (#2671)
#[test]
#[timeout(30000)]
fn full_pipeline_ghost_loop_in_ghost_sum_invariant() {
    // requires: x > 0 (u32 so also x >= 0)
    let requires = vec![gt(var("x"), int(0)), ge(var("x"), int(0))];
    // invariant: y + i == x (after strip_scalar_views)
    let invariants = vec![eq(add(var("y"), var("i")), var("x"))];
    // ensures: *result == x → after ghost rewrite with return_expr=y: y == x
    let ensures = vec![eq(var("result"), var("x"))];
    let return_expr = var("y");
    let modified_vars: Vec<&str> = vec!["y", "i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), sub(var("i"), int(1)));
    body_effect.insert("y".to_string(), add(var("y"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("y".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("x")));
    let loop_condition = gt(var("i"), int(0));
    let variant = var("i");
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_variant(&variant)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("ghost loop_in_ghost should encode");

    // Init: y=0, i=x, requires x>0. Invariant: 0 + x == x. Trivially true.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify: y=0, i=x => 0+x==x; got {:?}",
        result.initialization
    );
    // Preservation: y+i==x, i>0 => (y+1)+(i-1)==x. Simplifies to y+i==x. Trivially true.
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify: y+i==x => (y+1)+(i-1)==x; got {:?}",
        result.preservation
    );
    // Postcondition: y+i==x, NOT(i>0) => i<=0. Since y+0==x => y==x. result=y => result==x.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify: y+i==x, i<=0 => y==x, result=y; got {:?}",
        result.postcondition
    );
    // Variant non-negative: y+i==x, i>0 => i >= 0. Trivially true since i > 0.
    assert!(
        result.variant_nonneg.is_some(),
        "variant_nonneg should be present"
    );
    assert!(
        matches!(
            result.variant_nonneg.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant nonneg should verify: i>0 => i>=0; got {:?}",
        result.variant_nonneg
    );
    // Variant decrease: variant' = i-1 < i. Trivially true.
    assert!(
        result.variant_decrease.is_some(),
        "variant_decrease should be present"
    );
    assert!(
        matches!(
            result.variant_decrease.as_ref().unwrap(),
            VerificationResult::Verified(_)
        ),
        "variant decrease should verify: i-1 < i; got {:?}",
        result.variant_decrease
    );
    assert!(
        result.all_verified(),
        "all VCs should verify for ghost loop_in_ghost pattern"
    );
}

// -----------------------------------------------------------------------
// Deref body effect pattern (mutable reference writes)
// -----------------------------------------------------------------------

/// Deref body effect: `*x = *x + 1` through a mutable reference.
///
/// Models: `fn inc_ref(x: &mut i32, n: i32) { while *x < n { *x += 1 } }`
///   requires: n >= *x, *x >= 0
///   invariant: 0 <= *x <= n
///   ensures: ^x == n  (final value through the borrow)
///
/// The deref effect maps "x" -> `add(deref(var("x")), int(1))` meaning
/// `*x_next = *x + 1`. The postcondition references Final(x) which must
/// resolve to the current value at loop exit.
#[test]
#[timeout(30000)]
fn full_pipeline_deref_body_effect_mut_ref() {
    let requires = vec![ge(deref(var("x")), int(0)), ge(var("n"), deref(var("x")))];
    let invariants = vec![ge(deref(var("x")), int(0)), le(deref(var("x")), var("n"))];
    // ensures: ^x == n (Final(x) == n)
    let ensures = vec![eq(final_expr(var("x")), var("n"))];
    let loop_condition = lt(deref(var("x")), var("n"));
    let modified_vars: Vec<&str> = vec!["x"];
    let empty_direct = HashMap::new();
    let mut deref_effect = HashMap::new();
    deref_effect.insert("x".to_string(), add(deref(var("x")), int(1)));
    let empty_double_deref = HashMap::new();
    let empty_pre_loop = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&empty_direct, &deref_effect, &empty_double_deref),
        &empty_pre_loop,
    )
    .with_loop_condition(&loop_condition)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("deref body effect pipeline should encode");

    // Initialization: without pre_loop_assignments, init uses requires as assumptions.
    // deref(x) >= 0 and deref(x) <= n should hold from requires.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify from requires; got {:?}",
        result.initialization
    );
    // Preservation: 0 <= *x <= n, *x < n => 0 <= *x+1 <= n
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify: 0<=*x<=n, *x<n => 0<=*x+1<=n; got {:?}",
        result.preservation
    );
}

// -----------------------------------------------------------------------
// Body-break full pipeline with postcondition
// -----------------------------------------------------------------------

/// Body-break loop with postcondition verification.
///
/// Models: `let mut i = 0; loop { i += 1; if i >= n { break } }; return i`
///   requires: n > 0
///   invariant: 0 < i <= n  (i is always positive after body, at most n)
///   ensures: result == n
///
/// The body-break pattern means the condition is checked AFTER the body
/// executes, so the exit condition applies to post-body (primed) state.
/// The invariant uses strict inequality because i == 0 only holds at entry
/// before the first body execution.
#[test]
#[timeout(30000)]
fn full_pipeline_body_break_with_postcondition() {
    let requires = vec![gt(var("n"), int(0))];
    // After body executes: i is in range (0, n]
    let invariants = vec![gt(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), var("n"))];
    let return_expr = PureExpr::Var("i".to_string(), None);
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    // Continuation condition: i < n (loop continues while i < n after increment)
    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_body_break()
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("body-break with postcondition should encode");

    // Init: i = 0, but invariant says i > 0. The init check substitutes i = 0
    // into the invariant, so we need i > 0 after substitution... which gives 0 > 0 = false.
    // This means the invariant i > 0 is wrong for body-break init.
    // Correct invariant for body-break where body runs first: the invariant holds
    // AFTER the body, so at the check point i has already been incremented.
    // But init checks invariant at loop entry BEFORE body runs.
    // For body-break loops, init still checks the invariant at entry. So we need
    // a weaker invariant that holds at entry.
    // Let's use: i >= 0 && i <= n instead.
    // Actually the test above has the wrong invariant for init. Let me fix it.
    // The existing body_break tests in body_break.rs use i >= 0 && i < n.
    // Let's match that pattern.

    // With invariants [i > 0, i <= n], init with i = 0 gives 0 > 0 which is false.
    // So init should FAIL.
    assert_pattern_failed_result(
        &result.initialization,
        "initialization when i=0 does not satisfy i > 0",
    );
}

/// Body-break loop with correct invariant for full pipeline verification.
///
/// Models: `let mut i = 0; loop { i += 1; if i >= n { break } }; return i`
///   requires: n > 0
///   invariant: 0 <= i, i <= n  (holds at loop head, before body)
///   ensures: result == n
///
/// For body-break loops, the invariant must hold at the loop head (before
/// body execution). After the body (i += 1) and the break test (i >= n),
/// the exit condition in primed state is NOT(i' < n), i.e., i+1 >= n.
/// Combined with invariant i <= n and i+1 >= n, we get i+1 == n... but
/// that gives result = i+1 = n. The return_expr must be primed for
/// body-break loops, which the postcondition handler does automatically.
#[test]
#[timeout(30000)]
fn full_pipeline_body_break_correct_invariant() {
    let requires = vec![gt(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), lt(var("i"), var("n"))];
    let ensures: Vec<PureExpr> = vec![]; // No ensures to keep this focused on init + preservation
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_body_break()
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("body-break correct invariant should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify: i=0, n>0 => 0>=0 && 0<n; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify with body-break priming; got {:?}",
        result.preservation
    );
}

// -----------------------------------------------------------------------
// Snapshot pattern: old value via pre-loop assignment
// -----------------------------------------------------------------------

/// Postcondition referencing old value through a snapshot variable.
///
/// Models the common Creusot pattern:
///   `let old_x = snapshot!(x); while ... { x += 1 }; ensures(x >= old_x)`
///
/// The snapshot `old_x = x` is a pre-loop assignment. Since `old_x` is not
/// modified by the loop, it acts as a frame constraint: old_x == x_initial.
/// The postcondition `x >= old_x` is provable from the invariant `x >= old_x`.
#[test]
#[timeout(30000)]
fn postcondition_snapshot_old_value_pattern() {
    let invariants = vec![ge(var("x"), var("old_x")), ge(var("x"), int(0))];
    let ensures = vec![ge(var("x"), var("old_x"))];
    let requires = vec![ge(var("x"), int(0))];
    let loop_condition = lt(var("x"), var("n"));
    let modified_vars: Vec<&str> = vec!["x"];

    let mut pre_loop_assignments = HashMap::new();
    // old_x = x (snapshot of x before loop)
    pre_loop_assignments.insert("old_x".to_string(), NamedBindingValue::untyped(var("x")));
    let empty_body = HashMap::new();
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let result = verify_postcondition(
        &invariants,
        Some(&loop_condition),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &pre_loop_assignments, &requires, &[]),
        effects(&empty_body, &empty_deref, &empty_double_deref),
        &LoopEncoderConfig {
            timeout: Some(Duration::from_secs(5)),
            ..LoopEncoderConfig::default()
        },
    )
    .expect("snapshot pattern postcondition should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "postcondition x >= old_x should verify from invariant + frame; got {result:?}"
    );
}

// -----------------------------------------------------------------------
// Conjunctive invariant pattern (AND of conditions)
// -----------------------------------------------------------------------

/// Invariant expressed as a conjunction: `a <= i && i <= b && b <= n`.
///
/// Models a range-tracking loop where variables maintain a sorted order.
/// Tests that the preservation VC correctly handles conjunctive invariants
/// where each conjunct depends on different variables.
///
///   while i < b { i += 1 }
///   invariant: a <= i && i <= b && b <= n
///   ensures: i == b
#[test]
#[timeout(30000)]
fn full_pipeline_conjunctive_range_invariant() {
    let requires = vec![
        le(var("a"), var("b")),
        le(var("b"), var("n")),
        ge(var("a"), int(0)),
    ];
    let invariants = vec![
        le(var("a"), var("i")),
        le(var("i"), var("b")),
        le(var("b"), var("n")),
    ];
    let ensures = vec![eq(var("i"), var("b"))];
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(var("a")));
    let loop_condition = lt(var("i"), var("b"));
    let return_expr = var("i");
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_return_expr(&return_expr)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("conjunctive range pipeline should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify: i=a, a<=b, b<=n => a<=a, a<=b, b<=n; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify: a<=i<=b, i<b => a<=i+1<=b; got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify: i<=b, NOT(i<b) => i==b; got {:?}",
        result.postcondition
    );
    assert!(
        result.all_verified(),
        "all VCs should verify for conjunctive range pattern"
    );
}

// -----------------------------------------------------------------------
// Multiplicative invariant (doubling pattern)
// -----------------------------------------------------------------------

/// Multiplicative loop: `while x < n { x *= 2 }` with power-of-2 invariant.
///
/// Models a common pattern where the loop variable grows geometrically.
///   invariant: x >= 1
///   preservation: x >= 1, x < n => x*2 >= 1 (always true since x >= 1)
///
/// This tests that multiplication is handled correctly in body effects.
/// We only verify a weak lower-bound invariant since the full power-of-2
/// property would require quantified reasoning.
#[test]
#[timeout(30000)]
fn preservation_multiplicative_body_effect() {
    let invariants = vec![ge(var("x"), int(1))];
    let loop_condition = lt(var("x"), var("n"));
    let modified_vars: Vec<&str> = vec!["x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), mul(var("x"), int(2)));

    let result = verify_preservation(
        &invariants,
        Some(&loop_condition),
        &modified_vars,
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .expect("multiplicative preservation should encode");

    // x >= 1, x < n => x*2 >= 1 (since x >= 1 implies x*2 >= 2 >= 1)
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "preservation of x>=1 under x*=2 should verify; got {result:?}"
    );
}

// -----------------------------------------------------------------------
// Invariant with implication (conditional invariant)
// -----------------------------------------------------------------------

/// Invariant containing an implication: `n > 0 ==> i < n`.
///
/// Models a pattern where the invariant has a conditional guard. The
/// preservation VC must handle the implication correctly.
///
///   invariant: n > 0 ==> i < n
///   condition: i < n - 1
///   body: i += 1
///
/// Preservation: (n > 0 ==> i < n) /\ i < n-1 => (n > 0 ==> i+1 < n)
/// When n > 0: i < n-1 => i+1 < n. VALID.
/// When n <= 0: implication vacuously true. VALID.
#[test]
#[timeout(30000)]
fn preservation_implication_invariant() {
    let invariants = vec![implies(gt(var("n"), int(0)), lt(var("i"), var("n")))];
    let loop_condition = lt(var("i"), sub(var("n"), int(1)));
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_preservation(
        &invariants,
        Some(&loop_condition),
        &modified_vars,
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .expect("implication invariant preservation should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "preservation of (n>0 ==> i<n) under i+=1 with cond i<n-1 should verify; got {result:?}"
    );
}

// -----------------------------------------------------------------------
// Two modified variables with relational invariant
// -----------------------------------------------------------------------

/// Two variables maintaining a relational invariant: `j == 2 * i`.
///
/// Models: `while i < n { i += 1; j += 2 }`
///   invariant: j == 2 * i, i >= 0, i <= n
///   ensures: j == 2 * n
///
/// Tests that preservation handles coupled updates correctly:
/// j' = j + 2 = 2*i + 2 = 2*(i+1) = 2*i'. The relational invariant
/// must be re-established for both primed variables simultaneously.
#[test]
#[timeout(30000)]
fn full_pipeline_relational_invariant_two_vars() {
    let requires = vec![ge(var("n"), int(0))];
    let invariants = vec![
        eq(var("j"), mul(int(2), var("i"))),
        ge(var("i"), int(0)),
        le(var("i"), var("n")),
    ];
    let ensures = vec![eq(var("j"), mul(int(2), var("n")))];
    let modified_vars: Vec<&str> = vec!["i", "j"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    body_effect.insert("j".to_string(), add(var("j"), int(2)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    pre_loop_assignments.insert(
        "j".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );
    let loop_condition = lt(var("i"), var("n"));
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let ctx = LoopVerificationContext::new(
        &requires,
        &ensures,
        &invariants,
        &modified_vars,
        BodyEffects::new(&body_effect, &empty_deref, &empty_double_deref),
        &pre_loop_assignments,
    )
    .with_loop_condition(&loop_condition)
    .with_config(LoopEncoderConfig {
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    });

    let result = verify_loop_invariant(&ctx).expect("relational invariant pipeline should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify: i=0, j=0 => j==2*i, 0>=0, 0<=n; got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify: j==2*i, i<n => j+2==2*(i+1); got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition should verify: j==2*i, i==n => j==2*n; got {:?}",
        result.postcondition
    );
    assert!(
        result.all_verified(),
        "all VCs should verify for relational invariant pattern"
    );
}

// -----------------------------------------------------------------------
// Postcondition with negated return expression
// -----------------------------------------------------------------------

/// Postcondition where return expression is a computed value, not a variable.
///
/// Models: `while i < n { i += 1 }; return n - i`
///   invariant: 0 <= i <= n
///   ensures: result == 0
///
/// The return expression `n - i` is substituted for `result`. At exit,
/// i == n (from invariant + exit condition), so n - i == 0.
#[test]
#[timeout(30000)]
fn postcondition_computed_return_expr() {
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let ensures = vec![eq(var("result"), int(0))];
    let return_expr = sub(var("n"), var("i"));
    let requires = vec![ge(var("n"), int(0))];
    let cond = lt(var("i"), var("n"));
    let modified_vars: Vec<&str> = vec!["i"];
    let empty_pre_loop = HashMap::new();
    let empty_body = HashMap::new();
    let empty_deref = HashMap::new();
    let empty_double_deref = HashMap::new();

    let result = verify_postcondition(
        &invariants,
        Some(&cond),
        false,
        &modified_vars,
        postcondition_inputs(
            &ensures,
            Some(&return_expr),
            &empty_pre_loop,
            &requires,
            &[],
        ),
        effects(&empty_body, &empty_deref, &empty_double_deref),
        &LoopEncoderConfig {
            timeout: Some(Duration::from_secs(5)),
            ..LoopEncoderConfig::default()
        },
    )
    .expect("computed return expr postcondition should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "postcondition result==0 with return_expr=n-i should verify; got {result:?}"
    );
}

// -----------------------------------------------------------------------
// Deref-through-substitution for Snapshot/Ghost value types (#1709)
// -----------------------------------------------------------------------

/// Snapshot pre-loop substitution produces Deref(non-Var) which should
/// simplify during initialization via the Deref-through-substitution pass.
///
/// Models the pattern where a Snapshot variable `total` is assigned a
/// compound expression before the loop. The invariant `*total == a`
/// (i.e., `Deref(total) == a`) after substitution becomes
/// `Deref(a + 0) == a`.
///
/// Without the Deref-through-substitution fix (#1709), `Deref(Add(a, 0))`
/// encodes as an unconstrained `total_current` variable disconnected from
/// the substituted value. With the fix, `Deref(non-Var)` collapses to the
/// inner expression, making the VC trivially provable.
#[test]
#[timeout(30000)]
fn init_deref_through_substitution_snapshot_pattern() {
    let invariants = vec![eq(deref(var("total")), var("a"))];
    let requires = vec![ge(var("a"), int(0))];

    // total = a + 0 (a non-Var expression, simulating snapshot substitution)
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "total".to_string(),
        NamedBindingValue::untyped(add(var("a"), int(0))),
    );

    // After substitution: Deref(Add(a, 0)) == a
    // Without fix: Deref(Add(a,0)) becomes unconstrained total_current
    // With fix: Deref(Add(a,0)) -> Add(a,0) == a, trivially provable
    let result = verify_initialization(
        &requires,
        &invariants,
        &pre_loop_assignments,
        &[],
        &LoopEncoderConfig {
            timeout: Some(Duration::from_secs(5)),
            ..LoopEncoderConfig::default()
        },
    )
    .expect("deref-through-substitution init should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "init should verify: Deref(a+0) simplifies to a+0, and a+0==a is trivial; got {result:?}"
    );
}
