// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

/// Test: Deref body effect constrains primed dereference value (#1295)
///
/// Models the `nested_loops` pattern from `inferred_invariants.rs`:
/// ```rust
/// fn nested_loops(x: &mut i32) {
///     let mut i = 0;
///     #[invariant(*x == 0i32)]
///     while i < 10 {
///         *x = 0;
///         i += 1;
///     }
/// }
/// ```
///
/// Without deref body effects, `x` is in modified_vars but has no body_effect,
/// so `x_prime` is havoced. `Deref(Var("x_prime"))` → `x_prime_current` is then
/// unconstrained, causing preservation to fail.
///
/// With deref body effects, `x_prime_current = 0` is asserted, and preservation
/// succeeds because `Deref(Var("x_prime")) == 0` holds.
#[test]
#[timeout(30000)]
fn test_preservation_deref_body_effect_nested_loops() {
    // invariant: *x == 0
    let inv = eq(deref(var("x")), int(0));

    // loop condition: i < 10
    let cond = lt(var("i"), int(10));

    // body_effect: i' = i + 1 (direct assignment)
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // deref_body_effect: *x = 0 (deref assignment)
    let mut deref_body_effect = HashMap::new();
    deref_body_effect.insert("x".to_string(), int(0));

    // modified_vars includes both i and x
    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
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

    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "Deref body effect should make preservation succeed: got {:?}",
        result.preservation
    );
}

/// Test: Without deref body effect, deref invariant preservation fails (#1295)
///
/// Same as above but without the deref_body_effect. This verifies that the
/// havoc behavior (variable modified but no effect known) correctly fails
/// preservation, confirming the fix is necessary.
#[test]
#[timeout(30000)]
fn test_preservation_deref_havoc_fails_without_deref_body_effect() {
    // invariant: *x == 0
    let inv = eq(deref(var("x")), int(0));

    // loop condition: i < 10
    let cond = lt(var("i"), int(10));

    // body_effect: i' = i + 1 (direct assignment only — no deref effect for x)
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // x is modified but has no body_effect or deref_body_effect → havoc
    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "x"],
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
        matches!(result.preservation, VerificationResult::Failed(_)),
        "Without deref body effect, preservation should fail: got {:?}",
        result.preservation
    );
}

/// Test: Seq-typed havoced variable gets correct sort in `propagate_bool_and_predeclare` (#1319).
///
/// Models:
/// ```
/// let mut s: Vec<i32> = ...;
/// #[invariant(s@.len() >= 0)]
/// while cond {
///     // s is modified but body effect is unknown (havoced)
/// }
/// ```
///
/// The variable `s` is in `modified_vars` but NOT in `body_effect` (havoced).
/// `propagate_bool_and_predeclare` must not cause a sort conflict when later
/// encoding `s@.len()` in the invariant. Before #1319, the havoc branch
/// hardcoded `Sort::Int` without consulting sort hints or prior declarations.
#[test]
#[timeout(30000)]
fn test_loop_preservation_seq_havoced_var_no_sort_conflict() {
    // invariant: s@.len() >= 0  (view(var("s")).len() >= 0)
    let inv = ge(method_call(view(var("s")), "len", vec![]), int(0));

    // condition: i < 10
    let cond = lt(var("i"), int(10));

    // body effect: i' = i + 1 (but NO effect for s — s is havoced)
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // Both "i" and "s" are modified — s has no body effect (havoced)
    let result = verify_preservation(
        &[inv],
        Some(&cond),
        &["i", "s"],
        &body_effect,
        &LoopEncoderConfig::default(),
    );

    // Must not error with sort conflict. The invariant uses view(s).len()
    // which requires s_view as Seq, while s itself is Int. Havoced s declared
    // as Int is correct — the view encoding handles the Seq indirection.
    assert!(
        result.is_ok(),
        "Seq-typed havoced variable should not cause sort conflict (#1319): {result:?}"
    );
}

/// Test: Double-deref body effect enables preservation (#1295, #1389)
///
/// Models `x: &mut &mut i32` with `**x = 0` each iteration:
/// ```
/// #[invariant(**x == 0)]
/// while i < 10 {
///     **x = 0;
///     i += 1;
/// }
/// ```
///
/// Without double_deref_body_effect, `x` is havoced and `x_prime` is
/// unconstrained, making `**x_prime == 0` unprovable. With the effect,
/// `build_prime_substitutions` constrains `x_prime_current_current = 0`,
/// and `Deref(Deref(Var("x_prime")))` resolves to that value.
#[test]
#[timeout(30000)]
fn test_preservation_double_deref_body_effect_verifies() {
    // invariant: **x == 0
    let inv = eq(deref(deref(var("x"))), int(0));

    // loop condition: i < 10
    let cond = lt(var("i"), int(10));

    // body_effect: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // double_deref_body_effect: **x = 0
    let mut double_deref_body_effect = HashMap::new();
    double_deref_body_effect.insert("x".to_string(), int(0));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "x"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &double_deref_body_effect,
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
        matches!(result.preservation, VerificationResult::Verified(_)),
        "Double-deref body effect should make preservation succeed (#1389): got {:?}",
        result.preservation
    );
}

/// Negative test: Without double-deref body effect, double-deref invariant
/// preservation fails. This confirms the encoding branch at
/// `build_prime_substitutions` (verify/loops.rs:757) is necessary.
#[test]
#[timeout(30000)]
fn test_preservation_double_deref_havoc_fails_without_effect() {
    // invariant: **x == 0
    let inv = eq(deref(deref(var("x"))), int(0));

    // loop condition: i < 10
    let cond = lt(var("i"), int(10));

    // body_effect: i' = i + 1 (no double-deref effect for x → havoced)
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "x"],
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
        matches!(result.preservation, VerificationResult::Failed(_)),
        "Without double-deref body effect, preservation should fail (#1389): got {:?}",
        result.preservation
    );
}

/// Test: Double-deref body effect with non-constant expression (#1389)
///
/// Models `**x = i` (the effect depends on the loop variable):
/// ```
/// #[invariant(**x == i)]
/// while i < 10 {
///     **x = i;
///     // i does NOT change here — so **x_prime == i_prime is **x_prime == i
///     // But i is incremented elsewhere, so this is intentionally subtle.
/// }
/// ```
///
/// Here we test that the encoder correctly wires `x_prime_current_current = i`
/// (the unprimed value) rather than a constant.
#[test]
#[timeout(30000)]
fn test_preservation_double_deref_nonconstant_effect() {
    // invariant: **x == i
    let inv = eq(deref(deref(var("x"))), var("i"));

    // loop condition: i < 10
    let cond = lt(var("i"), int(10));

    // body_effect: i' = i (no change — this is a simplified model)
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), var("i"));

    // double_deref_body_effect: **x = i
    let mut double_deref_body_effect = HashMap::new();
    double_deref_body_effect.insert("x".to_string(), var("i"));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[inv],
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "x"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &double_deref_body_effect,
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
        matches!(result.preservation, VerificationResult::Verified(_)),
        "Double-deref with non-constant effect (var(i)) should verify (#1389): got {:?}",
        result.preservation
    );
}
