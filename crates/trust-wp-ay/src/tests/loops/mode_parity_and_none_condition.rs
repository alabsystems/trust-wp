// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{sync::Arc, time::Duration};

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::*;

/// Regression test: verify_loop_invariant (context-based) produces identical
/// results to verify_loop_invariant_positional for a counting loop with mode
/// overrides (#791, #923).
///
/// Exercises the context-based entry point with all fields populated,
/// including logic_fns + mode_overrides + pre-loop assignments + body effects.
#[test]
#[timeout(30000)]
fn test_loop_ctx_parity_with_mode_overrides() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // requires: n >= 0
    let req = ge(var("n"), int(0));
    // ensures: result == n
    let ens = eq(var("result"), var("n"));
    // invariant: i >= 0 && i <= n
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));
    // loop_condition: i < n
    let cond = lt(var("i"), var("n"));
    // body_effect: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    let modified_vars: Vec<&str> = vec!["i"];
    // pre-loop: i = 0
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    // return_expr: i
    let return_expr = var("i");

    // Logic fn (unused by this loop, but tests the filtering path)
    let unused_fn = LogicFnDef::new(
        "helper".to_string(),
        "test::helper".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Default);
    let logic_fns = vec![unused_fn];
    let modes = vec![LogicMode::Default];

    let requires = [req];
    let ensures = [ens];
    let invariants = [inv];

    // Call via positional API
    let result_positional = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &requires,
        ensures: &ensures,
        invariants: &invariants,
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &modified_vars,
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
            logic_fns: Some(&logic_fns),
            mode_overrides: Some(&modes),
            timeout: Some(Duration::from_secs(3)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    // Call via context API
    let ctx = LoopVerificationContext {
        requires: &requires,
        ensures: &ensures,
        invariants: &invariants,
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &modified_vars,
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
            type_invariants: None,
            logic_fns: Some(&logic_fns),
            mode_overrides: Some(&modes),
            type_constants: None,
            track: None,
            timeout: Some(Duration::from_secs(3)),
            adt_decls: None,
            adt_field_ranges: None,
            loop_element_borrow_vars: vec![],
            bridge_facts: vec![],
        },
    };
    let result_ctx = verify_loop_invariant(&ctx).unwrap();

    // Both should produce identical verification outcomes
    assert_eq!(
        std::mem::discriminant(&result_positional.initialization),
        std::mem::discriminant(&result_ctx.initialization),
        "initialization mismatch: positional={:?} ctx={:?}",
        result_positional.initialization,
        result_ctx.initialization
    );
    assert_eq!(
        std::mem::discriminant(&result_positional.preservation),
        std::mem::discriminant(&result_ctx.preservation),
        "preservation mismatch: positional={:?} ctx={:?}",
        result_positional.preservation,
        result_ctx.preservation
    );
    assert_eq!(
        std::mem::discriminant(&result_positional.postcondition),
        std::mem::discriminant(&result_ctx.postcondition),
        "postcondition mismatch: positional={:?} ctx={:?}",
        result_positional.postcondition,
        result_ctx.postcondition
    );
    assert_eq!(
        result_positional.all_verified(),
        result_ctx.all_verified(),
        "all_verified mismatch"
    );
}

// ── None-condition loop tests (unconditional `loop { }`) (#864) ───────────
//
// Rust `loop { ... }` has no while-condition. The loop exits only via `break`.
// In our encoding, this means `loop_condition = None`. The postcondition check
// should work without asserting a negated guard, and preservation should not
// assume a guard is true.

/// Postcondition verification with `loop_condition = None` (unconditional loop).
///
/// Models:
/// ```text
/// #[requires(true)]
/// #[ensures(result == 42)]
/// fn answer() -> i32 {
///     let mut x = 0;
///     loop {
///         x += 1;
///         if x == 42 { break; }
///     }
///     x
/// }
/// ```
///
/// Invariant: x >= 0
/// No loop condition (unconditional loop).
/// Postcondition: result == 42, with return_expr = x.
///
/// Without a guard, the postcondition check is:
///   invariant(x) ∧ (result = x) ⊢ result == 42
///
/// Since x is unconstrained (only x >= 0), this should FAIL — the invariant
/// alone doesn't guarantee x == 42.
#[test]
#[timeout(30000)]
fn test_postcondition_none_condition_unconditional_loop() {
    let inv = ge(var("x"), int(0));
    let ens = eq(var("result"), int(42));
    let return_expr = var("x");

    let pre_loop = {
        let mut m = HashMap::new();
        m.insert("x".to_string(), NamedBindingValue::untyped(int(0)));
        m
    };

    let body_effect = {
        let mut m = HashMap::new();
        m.insert("x".to_string(), add(var("x"), int(1)));
        m
    };

    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &[ens],
        invariants: &[inv],
        loop_condition: None, // unconditional loop
        condition_is_body_break: false,
        modified_vars: &["x"],
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
    };

    let result = verify_loop_invariant(&ctx).unwrap();

    // Initialization should pass: x = 0 => x >= 0
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Initialization should pass (x=0 => x>=0): got {:?}",
        result.initialization
    );

    // Postcondition should FAIL: invariant (x >= 0) does not imply x == 42
    assert!(
        matches!(result.postcondition, VerificationResult::Failed(_)),
        "Without loop condition, postcondition (x>=0 => x==42) should fail: got {:?}",
        result.postcondition
    );
}

/// Postcondition succeeds with None condition when invariant is strong enough.
///
/// Models a loop where the invariant directly establishes the postcondition:
/// ```text
/// loop { break; } // trivial loop
/// ```
///
/// Invariant: x == 42
/// Ensures: result == 42, return_expr = x
/// No condition.
///
/// Should verify because invariant directly implies postcondition.
#[test]
#[timeout(30000)]
fn test_postcondition_none_condition_strong_invariant_verified() {
    let inv = eq(var("x"), int(42));
    let ens = eq(var("result"), int(42));
    let return_expr = var("x");

    let pre_loop = {
        let mut m = HashMap::new();
        m.insert("x".to_string(), NamedBindingValue::untyped(int(42)));
        m
    };

    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &[ens],
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
        return_expr: Some(&return_expr),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).unwrap();

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Initialization should pass (x=42 => x==42): got {:?}",
        result.initialization
    );

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Postcondition should pass (x==42 => result==42): got {:?}",
        result.postcondition
    );

    assert!(
        result.all_verified(),
        "All phases should verify for trivial unconditional loop: got {:?}",
        result
    );
}

/// Preservation with `loop_condition = None`.
///
/// Without a guard, preservation checks:
///   invariant(x) ⊢ invariant(x')
/// where x' = body_effect(x).
///
/// Invariant: x >= 0
/// Body effect: x' = x + 1
/// No condition.
///
/// Should VERIFY because x >= 0 ∧ x' = x + 1 => x' >= 0.
#[test]
#[timeout(30000)]
fn test_preservation_none_condition_verified() {
    let inv = ge(var("x"), int(0));

    let body_effect = {
        let mut m = HashMap::new();
        m.insert("x".to_string(), add(var("x"), int(1)));
        m
    };

    let pre_loop = {
        let mut m = HashMap::new();
        m.insert("x".to_string(), NamedBindingValue::untyped(int(0)));
        m
    };

    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[inv],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &["x"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).unwrap();

    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "Preservation (x>=0 ∧ x'=x+1 => x'>=0) should verify without condition: got {:?}",
        result.preservation
    );
}

/// Preservation with `loop_condition = None` should FAIL for non-inductive invariant.
///
/// Invariant: x >= 0 ∧ x <= 10
/// Body effect: x' = x + 1
/// No condition.
///
/// Fails because x = 10 ∧ x' = 11 violates x' <= 10.
/// With a condition (x < 10), preservation would succeed. Without it, the
/// invariant must hold for ALL iterations, including x = 10.
#[test]
#[timeout(30000)]
fn test_preservation_none_condition_fails_without_guard() {
    let inv = and(ge(var("x"), int(0)), le(var("x"), int(10)));

    let body_effect = {
        let mut m = HashMap::new();
        m.insert("x".to_string(), add(var("x"), int(1)));
        m
    };

    let pre_loop = {
        let mut m = HashMap::new();
        m.insert("x".to_string(), NamedBindingValue::untyped(int(0)));
        m
    };

    let ctx = LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[inv],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &["x"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    };

    let result = verify_loop_invariant(&ctx).unwrap();

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Initialization (x=0 => 0>=0 ∧ 0<=10) should pass: got {:?}",
        result.initialization
    );

    assert!(
        matches!(result.preservation, VerificationResult::Failed(_)),
        "Preservation should fail without guard (x=10, x'=11 violates x'<=10): got {:?}",
        result.preservation
    );
}

/// Demonstrates that loop postcondition verification uses `assert_negated_conjunction`
/// instead of `encode_and_assert_negated_postconditions` for existential postconditions.
///
/// When a loop's `ensures` clause contains an existential quantifier (e.g.,
/// `exists<a:Bool> a`), function verification goes through the De Morgan slow
/// path (`NOT(exists x. P(x))` → `forall x. NOT P(x)`), but loop postcondition
/// verification applies ay-level NOT directly. For Bool-sorted quantifiers this
/// is equivalent (both are expanded to case splits), but for Int-sorted existentials
/// the ay-level negation hits E-matching limitations (#970).
///
/// This test verifies that the Bool-sorted case works correctly through the loop path,
/// documenting the architectural gap for Int-sorted existential loop postconditions (#1080).
///
/// Re: #970 (existential negation), #1080 (loops.rs De Morgan gap)
#[test]
#[timeout(30000)]
fn loop_postcondition_with_existential_ensures_verifies_bool_sorted() {
    use crate::ExprSort;

    // Loop: invariant = true, no condition (immediate exit),
    // ensures = exists<a:Bool> a (trivially true: a=true satisfies it).
    let ensures = PureExpr::Exists {
        var: "a".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(PureExpr::Var("a".to_string(), None)),
        triggers: vec![],
    };

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[ensures],
        invariants: &[bool_expr(true)],
        loop_condition: None,
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
    .expect("existential postcondition should encode without error");

    // Bool-sorted existentials are case-split, so this works even without
    // the De Morgan rewrite. Int-sorted existentials would need the De Morgan
    // path that function.rs uses but loops.rs currently lacks (#1080).
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "trivially-true existential loop postcondition should verify: got {:?}",
        result.postcondition
    );
}
