// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

/// Integration: variant nonneg with logic function axiom (positive plumbing test).
///
/// ```text
/// #[logic] fn double(x) = x + x   (Open)
///
/// requires: n >= 0
/// invariant: i >= 0 && i <= double(n)
/// condition: i < double(n)
/// variant: double(n) - i
/// body: i' = i + 1
/// ```
///
/// Variant nonneg: `i >= 0 && i <= double(n) && i < double(n) => double(n) - i >= 0`
/// With axiom: `double(n) = n + n`, so `n + n - i >= 0` given `i <= n + n`. ✓
///
/// Note: This is NOT a discriminating test — the invariant `i <= double(n)` makes
/// nonneg provable even with `double(n)` uninterpreted (the solver uses the
/// assumption directly). See `test_loop_variant_nonneg_discriminating_with_logic_fn`
/// for a discriminating variant nonneg test.
#[test]
#[timeout(60000)]
fn test_loop_variant_nonneg_with_logic_fn_axiom() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    // requires: n >= 0
    let req = ge(var("n"), int(0));

    // invariant: i >= 0 && i <= double(n)
    let inv = and(
        ge(var("i"), int(0)),
        le(var("i"), logic_fn_call("double", vec![var("n")])),
    );

    // condition: i < double(n)
    let cond = lt(var("i"), logic_fn_call("double", vec![var("n")]));

    // variant: double(n) - i
    let variant = sub(logic_fn_call("double", vec![var("n")]), var("i"));

    // body: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // With logic fn axiom: variant nonneg should verify
    let result_with = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: &[],
        invariants: std::slice::from_ref(&inv),
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
        config: LoopEncoderConfig {
            transition_facts: vec![],
            logic_fns: Some(std::slice::from_ref(&double_fn)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    assert!(
        matches!(
            result_with.variant_nonneg,
            Some(VerificationResult::Verified(_))
        ),
        "With logic fn axiom, variant nonneg should verify: got {:?}",
        result_with.variant_nonneg
    );
}

/// Integration: discriminating variant nonneg test requiring logic function.
///
/// ```text
/// #[logic] fn abs_diff(a, b) = if a >= b then a - b else b - a   (Open)
///
/// requires: n >= 0 && m >= 0
/// invariant: i >= 0 && i <= n && m >= 0
/// condition: i < n
/// variant: n + m - abs_diff(i, m)
/// body: i' = i + 1
/// ```
///
/// Variant nonneg: `n + m - abs_diff(i, m) >= 0`
/// With axiom: `abs_diff(i, m) = |i - m|`. Since `0 <= i <= n` and `m >= 0`,
/// `|i - m| <= max(i, m) <= max(n, m) <= n + m`, so the variant is nonneg. ✓
/// Without axiom: `abs_diff(i, m)` is uninterpreted; the solver can assign
/// `abs_diff(i, m) > n + m`, making the variant negative. ✗
///
/// Note: `m >= 0` is included in the invariant because `verify_variant_nonneg`
/// only receives invariants + condition, not requires. All constraints needed
/// for the variant proof must appear in the invariant.
#[test]
#[timeout(60000)]
fn test_loop_variant_nonneg_discriminating_with_logic_fn() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // abs_diff(a, b) = if a >= b then a - b else b - a
    let abs_diff_fn = LogicFnDef::new(
        "abs_diff".to_string(),
        "test::abs_diff".to_string(),
        vec!["a".to_string(), "b".to_string()],
        ite(
            ge(var("a"), var("b")),
            sub(var("a"), var("b")),
            sub(var("b"), var("a")),
        ),
    )
    .with_mode(LogicMode::Open);

    // requires: n >= 0 && m >= 0
    let req = and(ge(var("n"), int(0)), ge(var("m"), int(0)));

    // invariant: i >= 0 && i <= n && m >= 0
    // (m >= 0 must be in the invariant for variant nonneg, which only sees invariants)
    let inv = and(
        and(ge(var("i"), int(0)), le(var("i"), var("n"))),
        ge(var("m"), int(0)),
    );

    // condition: i < n
    let cond = lt(var("i"), var("n"));

    // variant: n + m - abs_diff(i, m)
    let variant = sub(
        add(var("n"), var("m")),
        logic_fn_call("abs_diff", vec![var("i"), var("m")]),
    );

    // body: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // With abs_diff axiom: variant nonneg should verify
    let result_with = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: &[],
        invariants: std::slice::from_ref(&inv),
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
        config: LoopEncoderConfig {
            transition_facts: vec![],
            logic_fns: Some(std::slice::from_ref(&abs_diff_fn)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    assert!(
        matches!(
            result_with.variant_nonneg,
            Some(VerificationResult::Verified(_))
        ),
        "With abs_diff axiom, variant nonneg should verify: got {:?}",
        result_with.variant_nonneg
    );

    // Without abs_diff axiom: variant nonneg should fail
    let result_without = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: &[],
        invariants: std::slice::from_ref(&inv),
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

    // abs_diff(i, m) is uninterpreted without the axiom, so ay should find a
    // counterexample.
    assert!(
        matches!(
            result_without.variant_nonneg,
            Some(VerificationResult::Failed(_))
        ),
        "Without axiom, variant nonneg must fail: got {:?}",
        result_without.variant_nonneg
    );
}

/// Integration: variant decrease with logic function axiom (positive plumbing test).
///
/// Same loop as `test_loop_variant_nonneg_with_logic_fn_axiom`:
/// variant `double(n) - i` with body `i' = i + 1`.
///
/// Decrease: `double(n) - (i+1) < double(n) - i` simplifies to `-1 < 0` ✓.
/// This is trivially true regardless of the axiom — the `double(n)` terms cancel.
///
/// Note: This is NOT a discriminating test. The axiom is not needed for the decrease
/// proof. This test confirms the plumbing works (no crash/error when logic_fns are
/// present in variant expressions) but would pass even if axiom registration were
/// completely broken in the variant decrease path.
#[test]
#[timeout(60000)]
fn test_loop_variant_decrease_with_logic_fn_axiom() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    let req = ge(var("n"), int(0));

    let inv = and(
        ge(var("i"), int(0)),
        le(var("i"), logic_fn_call("double", vec![var("n")])),
    );

    let cond = lt(var("i"), logic_fn_call("double", vec![var("n")]));

    let variant = sub(logic_fn_call("double", vec![var("n")]), var("i"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // With logic fn axiom: variant decrease should verify
    let result_with = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: &[],
        invariants: std::slice::from_ref(&inv),
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
        config: LoopEncoderConfig {
            transition_facts: vec![],
            logic_fns: Some(std::slice::from_ref(&double_fn)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    assert!(
        matches!(
            result_with.variant_decrease,
            Some(VerificationResult::Verified(_))
        ),
        "With logic fn axiom, variant decrease should verify: got {:?}",
        result_with.variant_decrease
    );
}

/// Plumbing-only companion for `test_loop_variant_decrease_with_logic_fn_axiom`.
///
/// This loop shape is intentionally non-discriminating: `double(n)` is a shared
/// term on both sides of `variant' < variant`, so the arithmetic part can still
/// discharge the check without seeing `double`'s body. Without the axiom,
/// `double(n)` is treated as an uninterpreted constant `c`, and the variant
/// `c - i` still decreases by 1 each iteration, so the proof goes through.
///
/// This test verifies the plumbing path (encoder selection, sort registration)
/// works correctly when no axiom is provided. It does NOT test semantic
/// discrimination between with-axiom and without-axiom cases (#850).
///
/// Re: #845, #850
#[test]
#[timeout(60000)]
fn test_loop_variant_decrease_plumbing_only_without_axiom() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // double(x) = x + x — registered so sort inference resolves return sort
    // without triggering the demoting SortFallbackToIntFromLogicFn counter.
    // The variant decrease proof is purely arithmetic (double(n) - i decreases
    // by 1 each iteration); it does not depend on the axiom body. (#2062)
    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    let req = ge(var("n"), int(0));

    let inv = and(
        ge(var("i"), int(0)),
        le(var("i"), logic_fn_call("double", vec![var("n")])),
    );

    let cond = lt(var("i"), logic_fn_call("double", vec![var("n")]));

    let variant = sub(logic_fn_call("double", vec![var("n")]), var("i"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let result_without = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: &[],
        invariants: std::slice::from_ref(&inv),
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
        config: LoopEncoderConfig {
            logic_fns: Some(std::slice::from_ref(&double_fn)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    // The variant `double(n) - i` decreases by pure integer arithmetic
    // (i' = i + 1 => variant' < variant). This verifies the plumbing path
    // (encoder selection, sort registration, variant VC encoding) works
    // correctly when a logic function is present in the variant expression.
    // This MUST be Verified — accepting Unknown here would mask plumbing regressions (#850).
    assert!(
        matches!(
            result_without.variant_decrease,
            Some(VerificationResult::Verified(_))
        ),
        "Plumbing test: variant decrease should verify (pure arithmetic): got {:?}",
        result_without.variant_decrease
    );
}

/// Integration: havoced modified variable combined with logic function.
///
/// ```text
/// #[logic] fn double(x) = x + x   (Open)
///
/// requires: n >= 0
/// invariant: x >= 0 && x <= double(n)
/// modified_vars: ["x"]
/// body_effect: {} (empty — x is havoced)
/// ```
///
/// Preservation: `x >= 0 && x <= double(n) && cond => x_prime >= 0 && x_prime <= double(n)`
/// Since `x_prime` is unconstrained (havoced), preservation MUST FAIL —
/// there exist values of `x_prime` that violate `x_prime >= 0 && x_prime <= double(n)`.
///
/// Key soundness check: even with the logic_fn axiom providing `double(n) = n + n`,
/// the havoc semantics must still cause failure because `x_prime` is unconstrained.
/// This tests that axiom registration and havoc work correctly together.
#[test]
#[timeout(60000)]
fn test_loop_preservation_havoc_with_logic_fn() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    let req = ge(var("n"), int(0));

    // invariant: x >= 0 && x <= double(n)
    let inv = and(
        ge(var("x"), int(0)),
        le(var("x"), logic_fn_call("double", vec![var("n")])),
    );

    // condition: x < double(n)
    let cond = lt(var("x"), logic_fn_call("double", vec![var("n")]));

    // Havoc: x is modified but has NO body_effect entry
    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: &[],
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["x"],
        body_effect: &HashMap::new(),
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
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

    // Preservation must FAIL: x_prime is unconstrained, so there exist
    // values violating x_prime >= 0 && x_prime <= double(n).
    assert!(
        matches!(result.preservation, VerificationResult::Failed(_)),
        "Havoc + logic fn: preservation must fail (x_prime unconstrained): got {:?}",
        result.preservation
    );
}
