// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Body-break `condition_is_body_break` algorithm audit tests (#1385, #1386).
//!
//! These tests exercise the `condition_is_body_break: true` path through
//! `verify_loop_invariant`, which was previously untested at the ay
//! verification level. The body-break pattern models `loop { body; if cond
//! { break } }` where the exit condition is checked AFTER the body.
//!
//! Key insight: for body-break loops, preservation must apply the continuation
//! condition to **primed** (post-body) variables. The step=2 tests demonstrate
//! this distinction is meaningful — the same invariant verifies with body-break
//! priming but fails without it.

use std::collections::HashMap;

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::{super::*, helpers::*};

/// Basic body-break init + preservation: `loop { i += 1; if i >= n { break } }`
///
/// Invariant: i < n (strict), condition (continuation): i < n, body effect: i' = i + 1.
/// With body-break priming: `(i+1) < n ∧ i < n => (i+1) < n` → VALID.
///
/// Uses `i < n` (strict) because `i == n` is unreachable at loop head: the
/// break fires when post-body `i` reaches `n`. (#1385)
/// Postcondition priming is tested separately in loops::tests. (#1385)
// ADJUDICATED LOAD FLAKE (#133 mass unit adjudication, 2026-08-27): passes 3/3
// solo at this pin; when it fails in-suite it is queued behind the global
// 8-permit `encoder::test_solver_limiter` cap, which ntest counts as wall-clock.
// Same class and same root cause as
// `tests::basic::boolean_models_and_diagnostics::test_counterexample_contains_meaningful_bindings`,
// where the mechanism is written up in full. Budget deliberately unchanged.
#[test]
#[timeout(30000)]
fn body_break_basic_loop_verifies() {
    let requires = vec![gt(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), lt(var("i"), var("n"))];
    let ensures = vec![ge(var("result"), var("n"))];
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let ctx = LoopVerificationContext {
        requires: &requires,
        ensures: &ensures,
        invariants: &invariants,
        loop_condition: Some(&lt(var("i"), var("n"))),
        condition_is_body_break: true,
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: Some(&return_expr),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).expect("body-break loop should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "initialization should verify, got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify with body-break priming, got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition result >= n should verify at body-break exit, got {:?}",
        result.postcondition
    );
}

/// Body-break with step=2: primed vs unprimed distinction matters.
///
/// `loop { i += 2; if i >= n { break } }`
/// Invariant: i <= n, condition: i < n, body effect: i' = i + 2.
///
/// With body-break priming: `(i+2) < n ∧ i <= n => (i+2) <= n` → VALID.
/// Without priming (header): `i < n ∧ i <= n => (i+2) <= n` → INVALID
///   (counterexample: i = n-1).
///
/// This test proves the priming distinction is meaningful.
#[test]
#[timeout(30000)]
fn body_break_step2_preservation_verifies() {
    let requires = vec![ge(var("n"), int(2))];
    let invariants = vec![and(ge(var("i"), int(0)), le(var("i"), var("n")))];
    let ensures = vec![ge(var("result"), var("n"))];
    let loop_condition = lt(var("i"), var("n"));
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(2)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let ctx = LoopVerificationContext {
        requires: &requires,
        ensures: &ensures,
        invariants: &invariants,
        loop_condition: Some(&loop_condition),
        condition_is_body_break: true,
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: Some(&return_expr),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).expect("body-break step=2 loop should encode");

    // With body-break priming: (i+2) < n ∧ i <= n => (i+2) <= n → VALID
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "body-break step=2 preservation should verify with primed condition, got {:?}",
        result.preservation
    );
}

/// Contrast: same loop as step=2 but with `condition_is_body_break: false`
/// (header condition) should FAIL preservation.
///
/// Header condition: `i < n ∧ i <= n => (i+2) <= n` → INVALID
/// Counterexample: i = n-1, n >= 2 → i < n ∧ i <= n → (n+1) <= n → FALSE
#[test]
#[timeout(30000)]
fn header_condition_step2_preservation_fails() {
    let requires = vec![ge(var("n"), int(2))];
    let invariants = vec![and(ge(var("i"), int(0)), le(var("i"), var("n")))];
    let ensures = vec![ge(var("result"), var("n"))];
    let loop_condition = lt(var("i"), var("n"));
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(2)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let ctx = LoopVerificationContext {
        requires: &requires,
        ensures: &ensures,
        invariants: &invariants,
        loop_condition: Some(&loop_condition),
        condition_is_body_break: false, // header condition (NOT body-break)
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: Some(&return_expr),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).expect("header-condition step=2 should encode");

    // Header condition: i < n ∧ i <= n => (i+2) <= n → INVALID
    assert!(
        matches!(result.preservation, VerificationResult::Failed(_)),
        "header-condition step=2 preservation should FAIL (unprimed condition too weak), got {:?}",
        result.preservation
    );
}

/// Body-break with variant: `n - i` decreases on each iteration.
///
/// Regression test for #1385 after primed-condition propagation was wired
/// through both variant checks. For step=1 this should remain VERIFIED.
///
/// Uses `i < n` (strict) invariant and no postcondition to avoid solver
/// timeout on the body-break return expression VC. (#1385)
#[test]
#[timeout(30000)]
fn body_break_variant_step1_verifies() {
    let requires = vec![gt(var("n"), int(0))];
    let invariants = vec![ge(var("i"), int(0)), lt(var("i"), var("n"))];
    let loop_condition = lt(var("i"), var("n"));
    let variant = sub(var("n"), var("i"));
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let ctx = LoopVerificationContext {
        requires: &requires,
        ensures: &[],
        invariants: &invariants,
        loop_condition: Some(&loop_condition),
        condition_is_body_break: true,
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&variant),
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).expect("body-break loop with variant should encode");

    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Verified(_))),
        "variant nonneg should verify, got {:?}",
        result.variant_nonneg
    );
    assert!(
        matches!(
            result.variant_decrease,
            Some(VerificationResult::Verified(_))
        ),
        "variant decrease should verify, got {:?}",
        result.variant_decrease
    );
}

/// No-condition path: `condition_is_body_break` is irrelevant when there is
/// no loop condition to prime.
#[test]
#[timeout(30000)]
fn no_condition_path_verifies() {
    let requires = vec![ge(var("x"), int(0))];
    let invariants = vec![ge(var("x"), int(0))];
    let ensures = vec![ge(var("x"), int(0))];
    let modified_vars: Vec<&str> = vec!["x"];
    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), add(var("x"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("x".to_string(), NamedBindingValue::untyped(int(0)));

    let ctx = LoopVerificationContext {
        requires: &requires,
        ensures: &ensures,
        invariants: &invariants,
        loop_condition: None,          // no condition
        condition_is_body_break: true, // irrelevant without condition
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).expect("conditionless body-break should encode");

    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation with no condition should verify regardless of body-break flag, got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition x >= 0 should verify on no-condition path, got {:?}",
        result.postcondition
    );
}

/// Models the `y` function from `inferred_invariants.rs`:
/// ```rust
/// fn y(v: &mut Vec<i32>) {
///     let _old_v_len = v.len();
///     let mut i: usize = 0;
///     loop {
///         if i < v.len() {
///             v[i] = 0;
///         }
///         i += 1;
///         if i > 10 {
///             break;
///         }
///     }
/// }
/// ```
/// Invariant: `i@ <= 10` (the only invariant the verifier can check without
/// Seq encoding for `v@.len()`).
///
/// After the opaque-condition conservative merge fix (#1295), body extraction
/// captures `i' = i + 1` despite the opaque `if i < v.len()` branch.
/// Body-break condition: `NOT(i > 10)` = `i <= 10`.
///
/// With body-break priming:
/// - Assume: `i <= 10`
/// - Body: `i' = i + 1`
/// - Continuation: `NOT(i' > 10)` → `i' <= 10` → `i + 1 <= 10`
/// - Prove: `i' <= 10` — directly from continuation assumption. ✓
#[test]
#[timeout(30000)]
fn body_break_inferred_invariants_y_verifies() {
    let invariants = vec![le(var("i"), int(10))];
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let condition = not(gt(var("i"), int(10)));

    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &invariants,
        loop_condition: Some(&condition),
        condition_is_body_break: true,
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).expect("inferred_invariants/y loop should encode");

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "init should verify (i=0, 0<=10), got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "preservation should verify with body effect i'=i+1 and body-break, got {:?}",
        result.preservation
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "postcondition (no ensures) should verify, got {:?}",
        result.postcondition
    );
}

/// Body-break with deref_body_effect: `loop { *x = 0; i += 1; if i >= n { break } }`
///
/// Invariant: `*x == 0`, condition (continuation): `i < n`, body effects:
/// `i' = i + 1` (direct), `*x = 0` (deref). With body-break priming, the
/// continuation condition is applied to post-body (primed) state, so the
/// deref effect must constrain `x_prime_current = 0` before the primed
/// condition is evaluated.
///
/// Covers gap: "No test with body-break + deref_body_effect combination" (#1386).
#[test]
#[timeout(30000)]
fn body_break_deref_body_effect_verifies() {
    let inv = eq(deref(var("x")), int(0));
    let loop_condition = lt(var("i"), var("n"));
    let modified_vars: Vec<&str> = vec!["i", "x"];

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut deref_body_effect = HashMap::new();
    deref_body_effect.insert("x".to_string(), int(0));

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let ctx = LoopVerificationContext {
        requires: &[gt(var("n"), int(0))],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&loop_condition),
        condition_is_body_break: true,
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &deref_body_effect,
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).expect("body-break + deref effect should encode");

    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "body-break + deref_body_effect preservation should verify, got {:?}",
        result.preservation
    );
}

/// Body-break with double_deref_body_effect: `loop { **x = 0; i += 1; if i >= n { break } }`
///
/// Invariant: `**x == 0`, body effects: `i' = i + 1` (direct), `**x = 0`
/// (double-deref). With body-break priming, the continuation is applied to
/// primed state, requiring `x_prime_current_current = 0` to be constrained
/// before the primed condition check.
///
/// Covers gap: "No test with body-break + double_deref_body_effect" (#1386).
#[test]
#[timeout(30000)]
fn body_break_double_deref_body_effect_verifies() {
    let inv = eq(deref(deref(var("x"))), int(0));
    let loop_condition = lt(var("i"), var("n"));
    let modified_vars: Vec<&str> = vec!["i", "x"];

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut double_deref_body_effect = HashMap::new();
    double_deref_body_effect.insert("x".to_string(), int(0));

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let ctx = LoopVerificationContext {
        requires: &[gt(var("n"), int(0))],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&loop_condition),
        condition_is_body_break: true,
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &double_deref_body_effect,
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result =
        verify_loop_invariant(&ctx).expect("body-break + double-deref effect should encode");

    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "body-break + double_deref_body_effect preservation should verify, got {:?}",
        result.preservation
    );
}

/// Body-break postcondition with step=2 detects overshoot that the unprimed
/// model would miss — demonstrates the #1385 fix.
///
/// `loop { i += 2; if i >= n { break } }`, return i.
/// ensures: `result == n`
///
/// With body-break priming (correct):
///   return = i_prime = i+2, exit: NOT((i+2) < n) → i+2 >= n.
///   From invariant i <= n: return = i+2 ∈ [n, n+2].
///   Postcondition `i+2 == n` fails — counterexample: i = n-1, i+2 = n+1.
///   CORRECTLY REJECTED.
///
/// Without priming (old bug #1385 path):
///   return = i, exit: NOT(i < n) → i >= n. With invariant i <= n → i = n.
///   Postcondition `i == n` trivially holds. UNSOUNDLY VERIFIED.
///
/// Covers gap: "No test exposes the postcondition gap (#1385)" (#1386).
#[test]
#[timeout(30000)]
fn body_break_step2_postcondition_rejects_exact_match() {
    let requires = vec![ge(var("n"), int(2))];
    let invariants = vec![and(ge(var("i"), int(0)), le(var("i"), var("n")))];
    let ensures = vec![eq(var("result"), var("n"))];
    let loop_condition = lt(var("i"), var("n"));
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(2)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let ctx = LoopVerificationContext {
        requires: &requires,
        ensures: &ensures,
        invariants: &invariants,
        loop_condition: Some(&loop_condition),
        condition_is_body_break: true,
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: Some(&return_expr),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result =
        verify_loop_invariant(&ctx).expect("body-break step=2 postcondition should encode");

    // Body-break priming correctly detects that return=i+2 can overshoot n.
    assert!(
        matches!(result.postcondition, VerificationResult::Failed(_)),
        "body-break step=2 postcondition `result == n` should FAIL \
         (return can be n+1 or n+2 with step=2), got {:?}",
        result.postcondition
    );
}

/// Contrast: same loop as step=2 postcondition test, but with header condition
/// (condition_is_body_break=false). The unprimed model pins i=n exactly,
/// making `result == n` trivially true — which is UNSOUND for the actual
/// body-break semantics.
///
/// This test documents the behavior the #1385 fix prevents.
#[test]
#[timeout(30000)]
fn header_condition_step2_postcondition_unsoundly_verifies() {
    let requires = vec![ge(var("n"), int(2))];
    let invariants = vec![and(ge(var("i"), int(0)), le(var("i"), var("n")))];
    let ensures = vec![eq(var("result"), var("n"))];
    let loop_condition = lt(var("i"), var("n"));
    let return_expr = var("i");
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(2)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let ctx = LoopVerificationContext {
        requires: &requires,
        ensures: &ensures,
        invariants: &invariants,
        loop_condition: Some(&loop_condition),
        condition_is_body_break: false, // header condition — NOT body-break
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: Some(&return_expr),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result =
        verify_loop_invariant(&ctx).expect("header-condition step=2 postcondition should encode");

    // Without body-break priming: exit NOT(i<n) → i>=n, invariant i<=n → i=n.
    // Return = i = n, so `result == n` trivially holds.
    // This would be UNSOUND for an actual body-break loop (see contrast test above).
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "header-condition step=2 postcondition `result == n` should VERIFY \
         (unprimed model pins i=n exactly), got {:?}",
        result.postcondition
    );
}

/// Body-break with variant where step=2 demonstrates that variant decrease
/// verifies correctly with primed condition. The variant `n - i` decreases
/// by 2 on each iteration, and the primed continuation condition `(i+2) < n`
/// ensures the variant is well-defined (non-negative after stepping).
///
/// Covers gap: "No test with body-break + variant where primed vs unprimed
/// matters" (#1386).
#[test]
#[timeout(30000)]
fn body_break_variant_step2_verifies() {
    let requires = vec![ge(var("n"), int(4))];
    let invariants = vec![ge(var("i"), int(0)), le(var("i"), var("n"))];
    let loop_condition = lt(var("i"), var("n"));
    let variant = sub(var("n"), var("i"));
    let modified_vars: Vec<&str> = vec!["i"];
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(2)));
    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let ctx = LoopVerificationContext {
        requires: &requires,
        ensures: &[],
        invariants: &invariants,
        loop_condition: Some(&loop_condition),
        condition_is_body_break: true,
        modified_vars: &modified_vars,
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&variant),
        pre_loop_assignments: &pre_loop_assignments,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result =
        verify_loop_invariant(&ctx).expect("body-break step=2 loop with variant should encode");

    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Verified(_))),
        "variant nonneg should verify (n-i >= 0 under primed condition), got {:?}",
        result.variant_nonneg
    );
    assert!(
        matches!(
            result.variant_decrease,
            Some(VerificationResult::Verified(_))
        ),
        "variant decrease should verify (n-(i+2) < n-i always), got {:?}",
        result.variant_decrease
    );
}
