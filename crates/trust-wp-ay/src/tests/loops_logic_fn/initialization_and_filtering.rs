// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::*;

// =============================================================================
// Logic function axiom tests (#739)
// =============================================================================

/// Regression test for #739: loop initialization with logic function axiom.
///
/// Tests that logic function axioms are correctly registered during
/// initialization, so that `double(0) = 0 + 0 = 0` is available in the VC.
///
/// Models:
/// ```rust
/// #[logic(open)]
/// fn double(x: Int) -> Int {
///     x + x
/// }
///
/// #[requires(n >= 0)]
/// fn sum_double(n: i32) -> i32 {
///     let mut acc = 0;
///     let mut i = 0;
///     #[invariant(acc == double(i))]
///     while i < n {
///         acc += 2;
///         i += 1;
///     }
///     acc
/// }
/// ```
///
/// Initialization check: precondition ∧ pre-loop assignments ⟹ invariant
/// With axiom: acc=0, i=0, double(0)=0+0=0, so acc==double(i) ⟹ 0==0 ✓
/// Without axiom: double(0) is uninterpreted, 0==double(0) is not provable ✗
///
/// NOTE: Preservation/postcondition tests are deferred pending ay#2830 fix
/// for QF_LIA equality-chain reasoning through addition.
#[test]
#[timeout(30000)]
fn test_loop_initialization_with_logic_fn_axiom() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // Logic function: double(x) = x + x (Open mode to emit defining axiom)
    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    // requires: n >= 0
    let req = ge(var("n"), int(0));

    // invariant: acc == double(i)
    let inv = eq(var("acc"), logic_fn_call("double", vec![var("i")]));

    // pre-loop assignments: i = 0, acc = 0
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop.insert("acc".to_string(), NamedBindingValue::untyped(int(0)));

    // WITH logic function: initialization should verify
    // (double(0) = 0+0 = 0, acc = 0, so acc == double(i) holds)
    let result_with = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: &[],
        invariants: std::slice::from_ref(&inv),
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
        config: LoopEncoderConfig {
            transition_facts: vec![],
            logic_fns: Some(std::slice::from_ref(&double_fn)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    assert!(
        matches!(result_with.initialization, VerificationResult::Verified(_)),
        "With logic fn axiom, initialization should verify: got {:?}",
        result_with.initialization
    );

    // WITHOUT logic function: initialization should fail
    // (double(0) is uninterpreted, 0 == double(0) is not provable)
    let result_without = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
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
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // double(0) is uninterpreted without the axiom, so ay should find a
    // counterexample with double(0) != 0.
    assert!(
        matches!(result_without.initialization, VerificationResult::Failed(_)),
        "Without logic fn axiom, initialization should fail — \
         double(0) is uninterpreted, got {:?}",
        result_without.initialization
    );
}

/// Regression: logic function in pre_loop_assignments is not scanned by filter.
///
/// When a logic function appears ONLY in pre_loop_assignments (not in invariants,
/// requires, ensures, body_effect, condition, or variant), the current
/// `filter_logic_fns_for_loop_with_modes` omits it from the filtered set.
/// This causes the function to be treated as uninterpreted during initialization,
/// producing a false reject (completeness bug).
///
/// ```text
/// #[logic(open)]
/// fn make_zero() -> Int { 0 }
///
/// let mut acc = make_zero();    // pre_loop_assignment: acc = make_zero()
/// #[invariant(acc >= 0)]        // invariant does NOT mention make_zero
/// while ... { ... }
/// ```
///
/// Expected: initialization verifies (make_zero() = 0, so acc = 0 >= 0).
/// Actual (bug): initialization fails because make_zero is filtered out
/// and treated as uninterpreted (solver can set make_zero() = -1).
#[test]
#[timeout(30000)]
fn test_logic_fn_in_pre_loop_assignments_only_is_filtered_out() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // Logic function: make_zero() = 0 (Open mode)
    let make_zero_fn = LogicFnDef::new(
        "make_zero".to_string(),
        "test::make_zero".to_string(),
        vec![], // no parameters
        int(0),
    )
    .with_mode(LogicMode::Open);

    // invariant: acc >= 0  (does NOT reference make_zero)
    let inv = ge(var("acc"), int(0));

    // pre-loop assignment: acc = make_zero()
    let mut pre_loop = HashMap::new();
    pre_loop.insert(
        "acc".to_string(),
        NamedBindingValue::untyped(logic_fn_call("make_zero", vec![])),
    );

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: std::slice::from_ref(&inv),
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
        config: LoopEncoderConfig {
            transition_facts: vec![],
            logic_fns: Some(std::slice::from_ref(&make_zero_fn)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    // Fixed (#769): filter_logic_fns_for_loop_with_modes now scans
    // pre_loop_assignments, so make_zero is included and its axiom
    // is registered. Initialization should verify: make_zero() = 0,
    // so acc = 0 >= 0 holds.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Logic fn in pre_loop_assignments should be included in filter. \
         Expected Verified, got {:?}",
        result.initialization
    );
}

/// Length mismatch between mode_overrides and logic_fns is silently dropped
/// (#2316, #2700). The overrides are computed from the full logic_fn_defs set,
/// but logic_fns may be a filtered subset. Rather than returning an encoding
/// error, the overrides are dropped so filter_logic_functions_for_goal falls
/// back to default mode scoping.
#[test]
#[timeout(30000)]
fn test_verify_loop_invariant_mode_override_length_mismatch_drops_overrides_silently() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let logic_fns = vec![
        LogicFnDef::new("f".to_string(), "test::f".to_string(), vec![], int(1))
            .with_mode(LogicMode::Open),
        LogicFnDef::new("g".to_string(), "test::g".to_string(), vec![], int(2))
            .with_mode(LogicMode::Open),
    ];
    let mode_overrides = [LogicMode::Open];
    let body_effect = HashMap::new();
    let pre_loop = HashMap::new();

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig {
            transition_facts: vec![],
            logic_fns: Some(&logic_fns),
            mode_overrides: Some(&mode_overrides),
            ..LoopEncoderConfig::default()
        },
    });
    // Should NOT error — overrides are dropped, verification proceeds
    assert!(
        result.is_ok(),
        "mode_overrides mismatch should be silently dropped, not error: {result:?}"
    );
}
