// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::*;

/// Test: modified_vars entry without body_effect is havoced, not silently skipped (#740).
///
/// Before the fix, `build_prime_substitutions` silently skipped variables in
/// `modified_vars` that had no `body_effect` entry. The primed invariant then
/// referenced the original (unprimed) variable, making preservation trivially
/// true — a soundness bug (false accept).
///
/// After the fix, missing body_effect entries produce unconstrained (havoced)
/// prime variables. The solver must prove the invariant holds for ANY value,
/// which correctly fails for bounded invariants.
#[test]
#[timeout(30000)]
fn test_preservation_havoc_modified_var_without_body_effect() {
    // invariant: x >= 0 && x <= 10
    let inv1 = ge(var("x"), int(0));
    let inv2 = le(var("x"), int(10));

    // x is modified but we don't know the effect — havoc it
    let body_effect = HashMap::new();

    let result = verify_preservation(
        &[inv1, inv2],
        None, // No loop condition needed
        &["x"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    // Must FAIL: havoced x_prime is unconstrained, so x_prime >= 0 && x_prime <= 10
    // does NOT hold for all possible values (e.g., x_prime = -1).
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Modified var without body_effect must be havoced, not silently skipped: got {result:?}"
    );
}

/// Positive counterpart: when a modified var has an explicit body effect, the
/// preservation check should use that effect instead of havocing the variable.
#[test]
#[timeout(30000)]
fn test_preservation_modified_var_with_body_effect_verifies() {
    let inv1 = ge(var("x"), int(0));
    let inv2 = le(var("x"), int(10));

    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), var("x"));

    let result = verify_preservation(
        &[inv1, inv2],
        None,
        &["x"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Explicit body_effect x' = x should preserve the bounded invariant; got {result:?}"
    );
}

/// Test: variant decrease also havocs modified vars without body_effect (#740).
///
/// Same principle as preservation: the variant decrease check must use
/// unconstrained prime variables for modified vars missing from body_effect.
#[test]
#[timeout(30000)]
fn test_variant_decrease_havoc_modified_var_without_body_effect() {
    // invariant: x >= 0
    let inv = ge(var("x"), int(0));

    // condition: x > 0
    let cond = gt(var("x"), int(0));

    // variant: x (should decrease each iteration)
    let variant = var("x");

    // x is modified but body_effect is empty — havoc it
    let body_effect = HashMap::new();

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&inv),
        ensures: &[bool_expr(true)],
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["x"],
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

    // Variant decrease must FAIL: havoced x_prime is unconstrained,
    // so x_prime < x is not guaranteed.
    assert!(
        result
            .variant_decrease
            .as_ref()
            .is_some_and(|vd| matches!(vd, VerificationResult::Failed(_))),
        "Variant decrease with havoced var must fail: got {:?}",
        result.variant_decrease
    );

    // Preservation must also FAIL: havoced x_prime is unconstrained,
    // so x_prime >= 0 is not guaranteed for all values.
    assert!(
        matches!(result.preservation, VerificationResult::Failed(_)),
        "Preservation with havoced var must also fail: got {:?}",
        result.preservation
    );
}

/// Positive counterpart: a decreasing body effect should prove both the
/// variant and the preserved invariant on the same loop shape.
#[test]
#[timeout(30000)]
fn test_variant_decrease_with_body_effect_verifies() {
    let inv = ge(var("x"), int(0));
    let cond = gt(var("x"), int(0));
    let variant = var("x");

    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), sub(var("x"), int(1)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&inv),
        ensures: &[bool_expr(true)],
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["x"],
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
        result
            .variant_decrease
            .as_ref()
            .is_some_and(|vd| matches!(vd, VerificationResult::Verified(_))),
        "Variant decrease should verify when x' = x - 1 under x > 0; got {:?}",
        result.variant_decrease
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "Preservation should verify when x' = x - 1 keeps x' >= 0 under x > 0; got {:?}",
        result.preservation
    );
}

/// Regression for #751: bare Bool variable as loop condition not in invariants.
///
/// When the loop condition is a Bool variable (`running`) that does not appear
/// in invariants, `setup_loop_encoder` must register formula-level sort hints
/// for the condition. Without this, `running` gets default Int sort and the
/// condition encoding fails or produces false rejects.
///
/// ```text
/// invariant: i >= 0
/// condition: running       (Bool var, NOT mentioned in invariants)
/// body: i' = i + 1, running' = i + 1 < 10
/// ```
#[test]
#[timeout(30000)]
fn test_loop_preservation_bool_condition_not_in_invariant() {
    // invariant: i >= 0 (does NOT mention `running`)
    let inv = ge(var("i"), int(0));

    // condition: running (bare Bool variable)
    let cond = var("running");

    // body effect: i' = i + 1, running' = (i + 1) < 10
    let i_plus_1 = add(var("i"), int(1));
    let running_next = lt(i_plus_1.clone(), int(10));
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), i_plus_1);
    body_effect.insert("running".to_string(), running_next);

    let result = verify_preservation(
        &[inv],
        Some(&cond),
        &["i", "running"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    // i >= 0 ∧ running ⊨ (i+1) >= 0 — should verify (i+1 >= 0 when i >= 0)
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Preservation with Bool condition not in invariant should verify: got {result:?}"
    );
}

/// Regression for #751: Bool condition in postcondition VC (verify_postcondition path).
///
/// Postcondition: `i >= 0` after loop exits with `!running`.
/// The `running` Bool variable is only in the condition, not invariants or ensures.
/// `verify_postcondition` must register formula-level sort hints for `loop_condition`
/// so that `running` is correctly declared as Bool.
///
/// Uses `verify_loop_invariant` (public API) to exercise the internal
/// `verify_postcondition` code path.
#[test]
#[timeout(30000)]
fn test_loop_postcondition_bool_condition_not_in_invariant() {
    // requires: i >= 0
    let req = ge(var("i"), int(0));

    // invariant: i >= 0
    let inv = ge(var("i"), int(0));

    // ensures: i >= 0 (trivially follows from invariant when loop exits)
    let ens = ge(var("i"), int(0));

    // condition: running (bare Bool variable, NOT in invariants or ensures)
    let cond = var("running");

    // pre-loop: i = 0
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
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
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // Postcondition: inv ∧ ¬running ⊨ i >= 0 — should verify
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Postcondition with Bool condition not in invariant should verify: got {:?}",
        result.postcondition
    );
}

/// Test: Bool body effect LogicFnCall gets correct sort via `propagate_bool_and_predeclare` (#849).
///
/// Models:
/// ```
/// #[logic]
/// fn check_condition() -> bool { ... }
///
/// let mut done = false;
/// #[invariant(done == false || done == true)]
/// while !done {
///     done = check_condition();
/// }
/// ```
///
/// body effect: done' = check_condition() (LogicFnCall)
///
/// Before #849, `propagate_bool_and_predeclare` only propagated Bool for
/// simple Var effects (via `extract_base_var_name`), which returns None for
/// LogicFnCall. The fix adds explicit LogicFnCall handling: when a Bool
/// modified var has a LogicFnCall effect, the fn's SMT name is marked Bool.
/// Without the fix, the logic fn defaults to Int, causing sort mismatch.
#[test]
#[timeout(30000)]
fn test_loop_preservation_bool_body_effect_logic_fn_sort_hint() {
    // invariant: done == false || done == true
    let inv = or(
        eq(var("done"), bool_expr(false)),
        eq(var("done"), bool_expr(true)),
    );

    // condition: done == false
    let cond = eq(var("done"), bool_expr(false));

    // body effect: done' = check_condition() (LogicFnCall, not Var — triggers #849)
    let mut body_effect = HashMap::new();
    body_effect.insert("done".to_string(), logic_fn_call("check_condition", vec![]));

    let result = verify_preservation(
        &[inv],
        Some(&cond),
        &["done"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    // With correct sort hints from propagate_bool_and_predeclare (#849),
    // check_condition is declared as Bool → done' = check_condition() preserves
    // the Bool invariant. Without the fix, check_condition defaults to Int.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Bool body effect LogicFnCall should get correct sort hint via \
         propagate_bool_and_predeclare (#849): got {result:?}"
    );
}
