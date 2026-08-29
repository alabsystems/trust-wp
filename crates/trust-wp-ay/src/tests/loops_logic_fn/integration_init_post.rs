// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::*;

// ── Loop + logic function integration tests (#739) ────────────────
//
// These tests verify that logic function axioms, tuple axioms, and
// Option/Result axioms are properly registered during loop verification,
// covering the soundness gap fixed by #739.

/// Integration: two interacting logic functions in a loop invariant.
///
/// ```text
/// #[logic] fn double(x) = x + x        (Open)
/// #[logic] fn half_sum(a, b) = a + b    (Open)
///
/// requires: n >= 0
/// invariant: acc == double(i) && acc == half_sum(i, i)
/// condition: i < n
/// body: i' = i + 1, acc' = acc + 2
/// pre-loop: i = 0, acc = 0
/// ```
///
/// Both axioms must be registered for initialization to verify:
/// - double(0) = 0 + 0 = 0
/// - half_sum(0, 0) = 0 + 0 = 0
/// - acc = 0, so both equalities hold
#[test]
#[timeout(60000)]
fn test_loop_initialization_two_interacting_logic_fns() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // double(x) = x + x
    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    // half_sum(a, b) = a + b
    let half_sum_fn = LogicFnDef::new(
        "half_sum".to_string(),
        "test::half_sum".to_string(),
        vec!["a".to_string(), "b".to_string()],
        add(var("a"), var("b")),
    )
    .with_mode(LogicMode::Open);

    let logic_fns = vec![double_fn, half_sum_fn];

    // requires: n >= 0
    let req = ge(var("n"), int(0));

    // invariant: acc == double(i) && acc == half_sum(i, i)
    let inv = and(
        eq(var("acc"), logic_fn_call("double", vec![var("i")])),
        eq(
            var("acc"),
            logic_fn_call("half_sum", vec![var("i"), var("i")]),
        ),
    );

    // pre-loop: i = 0, acc = 0
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop.insert("acc".to_string(), NamedBindingValue::untyped(int(0)));

    // With both logic functions
    let result = verify_loop_invariant_positional(&LoopVerificationContext {
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
            logic_fns: Some(&logic_fns),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Two-logic-fn initialization should verify (double(0)=0, half_sum(0,0)=0): got {:?}",
        result.initialization
    );

    // Without logic functions: should NOT verify (both are uninterpreted)
    let result_no_fns = verify_loop_invariant_positional(&LoopVerificationContext {
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
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // double(0) and half_sum(0, 0) are uninterpreted without the axioms, so ay
    // should find a counterexample.
    assert!(
        matches!(&result_no_fns.initialization, VerificationResult::Failed(_)),
        "Without logic fn axioms, initialization must fail: got {:?}",
        result_no_fns.initialization
    );
}

/// Integration: postcondition check with logic function in ensures clause.
///
/// Tests that logic function axioms are registered during postcondition
/// verification (#739). The ensures clause references `double(0)` which
/// requires the axiom to be available in the postcondition VC.
///
/// ```text
/// #[logic] fn double(x) = x + x    (Open)
///
/// requires: n >= 0
/// ensures:  result >= 0 && double(0) == 0
/// invariant: i >= 0 && i <= n
/// condition: i < n
/// body: i' = i + 1
/// pre-loop: i = 0
/// return: i
/// ```
///
/// The postcondition `double(0) == 0` requires the axiom (double(0) = 0+0 = 0).
/// Without the axiom, double(0) is uninterpreted and 0 == double(0) is unprovable.
#[test]
#[timeout(60000)]
fn test_loop_postcondition_with_logic_fn_axiom() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // double(x) = x + x
    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    // requires: n >= 0
    let req = ge(var("n"), int(0));

    // ensures: result >= 0 && double(0) == 0
    let ens = and(
        ge(var("result"), int(0)),
        eq(logic_fn_call("double", vec![int(0)]), int(0)),
    );

    // invariant: i >= 0 && i <= n
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    // condition: i < n
    let cond = lt(var("i"), var("n"));

    // body: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // pre-loop: i = 0
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    // return: i
    let return_expr = var("i");

    // With logic fn: all phases should verify
    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: std::slice::from_ref(&ens),
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: Some(&return_expr),
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
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Initialization should verify: got {:?}",
        result.initialization
    );

    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "Preservation should verify: got {:?}",
        result.preservation
    );

    // Key assertion: postcondition requires double axiom
    // inv ∧ ¬cond ⟹ i >= 0 ∧ double(0) == 0
    // With axiom: double(0) = 0+0 = 0. ✓
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Postcondition with logic fn axiom should verify: got {:?}",
        result.postcondition
    );

    // Without logic fn: postcondition should NOT verify
    // double(0) is uninterpreted, double(0) == 0 is unprovable
    let result_no_fn = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: std::slice::from_ref(&ens),
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: Some(&return_expr),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // double(0) is uninterpreted without the axiom, so ay should find a
    // counterexample.
    assert!(
        matches!(&result_no_fn.postcondition, VerificationResult::Failed(_)),
        "Without logic fn axiom, postcondition must fail: got {:?}",
        result_no_fn.postcondition
    );
}

/// Integration: loop with tuple invariant and logic function combined.
///
/// ```text
/// #[logic] fn pair_sum(p) = get_0(p) + get_1(p)    (Open)
///
/// requires: (none)
/// invariant: pair_sum(state) == get_0(state) + get_1(state)
/// pre-loop: state = tuple2(0, 0)
/// ```
///
/// Requires BOTH logic function axioms AND tuple axioms (#739).
/// The invariant is a tautology given the axiom definition, but without
/// the pair_sum axiom it becomes unprovable (pair_sum is uninterpreted).
#[test]
#[timeout(60000)]
fn test_loop_initialization_logic_fn_with_tuple_axioms() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // pair_sum(p) = get_0(p) + get_1(p)
    let pair_sum_fn = LogicFnDef::new(
        "pair_sum".to_string(),
        "test::pair_sum".to_string(),
        vec!["p".to_string()],
        add(
            logic_fn_call("__trust_wp_tuple_get_0", vec![var("p")]),
            logic_fn_call("__trust_wp_tuple_get_1", vec![var("p")]),
        ),
    )
    .with_mode(LogicMode::Open);

    // invariant: pair_sum(state) == get_0(state) + get_1(state)
    // Tautology given axiom definition, unprovable when pair_sum is uninterpreted.
    let inv = eq(
        logic_fn_call("pair_sum", vec![var("state")]),
        add(
            logic_fn_call("__trust_wp_tuple_get_0", vec![var("state")]),
            logic_fn_call("__trust_wp_tuple_get_1", vec![var("state")]),
        ),
    );

    // pre-loop: state = tuple2(0, 0)
    let mut pre_loop = HashMap::new();
    pre_loop.insert(
        "state".to_string(),
        NamedBindingValue::untyped(logic_fn_call("__trust_wp_tuple2", vec![int(0), int(0)])),
    );

    // With pair_sum axiom: initialization should verify
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
            logic_fns: Some(std::slice::from_ref(&pair_sum_fn)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    // pair_sum(tuple2(0,0)) = get_0(tuple2(0,0)) + get_1(tuple2(0,0))
    // Via axiom: LHS = RHS (tautology). ✓
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "With pair_sum axiom, initialization should verify: got {:?}",
        result.initialization
    );

    // Without pair_sum axiom: initialization should NOT verify
    let result_no_fn = verify_loop_invariant_positional(&LoopVerificationContext {
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
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        matches!(result_no_fn.initialization, VerificationResult::Failed(_)),
        "Without pair_sum axiom, initialization must fail with counterexample: got {:?}",
        result_no_fn.initialization
    );
}
