// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::*;

// =============================================================================
// Sub-result isolation tests (#855)
//
// These tests verify that individual LoopVerificationResult fields are
// independently meaningful — not masked by `all_verified()`.
// =============================================================================

/// Isolation test: initialization passes with logic fn, preservation fails without body effect.
///
/// ```text
/// #[logic(open)] fn ident(x) = x
///
/// invariant: acc == ident(i) && i >= 0
/// pre-loop: i = 0, acc = 0
/// condition: i < n
/// body: i' = i + 1  (but acc has no body_effect → havoced)
/// ```
///
/// Initialization: acc=0, i=0, ident(0)=0, acc==ident(i) ⟹ 0==0 ✓
/// Preservation: acc' is havoced (no body_effect for acc), so acc'==ident(i') is not provable ✗
///
/// This proves `verify_initialization` passes independently while preservation fails,
/// ruling out sub-result masking (#855 AC1).
///
/// Part of #855
#[test]
#[timeout(30000)]
fn test_initialization_passes_preservation_fails_logic_fn_isolation() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // ident(x) = x — simplest possible logic function for isolation test
    let ident_fn = LogicFnDef::new(
        "ident".to_string(),
        "test::ident".to_string(),
        vec!["x".to_string()],
        var("x"),
    )
    .with_mode(LogicMode::Open);

    // requires: n >= 0
    let req = ge(var("n"), int(0));

    // invariant: acc == ident(i) && i >= 0
    let inv = and(
        eq(var("acc"), logic_fn_call("ident", vec![var("i")])),
        ge(var("i"), int(0)),
    );

    // condition: i < n
    let cond = lt(var("i"), var("n"));

    // body: only i changes; acc is "modified" but has no body_effect → havoced
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // pre-loop: i = 0, acc = 0
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop.insert("acc".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: &[bool_expr(true)],
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "acc"],
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
            logic_fns: Some(std::slice::from_ref(&ident_fn)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    // Key assertion: initialization passes (ident(0) = 0, acc = 0, so acc == ident(i))
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Initialization should pass: acc=0, ident(0)=0, so 0==0. Got {:?}",
        result.initialization
    );

    // Key assertion: preservation fails (acc is havoced, acc' is unconstrained)
    assert!(
        matches!(result.preservation, VerificationResult::Failed(_)),
        "Preservation should fail: acc havoced, acc'==ident(i') unprovable. Got {:?}",
        result.preservation
    );

    // all_verified must be false — sub-results not masked
    assert!(
        !result.all_verified(),
        "all_verified() must reflect preservation failure, not mask it"
    );
}

/// Isolation test: variant nonneg uses logic fn in variant expression.
///
/// ```text
/// #[logic(open)] fn measure(x) = x * 2
///
/// invariant: i >= 0 && i <= n
/// condition: i < n
/// variant: measure(n - i)
/// body: i' = i + 1
/// ```
///
/// Variant nonneg: invariant ∧ condition ⟹ measure(n - i) >= 0
/// With axiom: measure(n-i) = (n-i)*2, and since i < n ⟹ n-i > 0 ⟹ 2*(n-i) >= 2 > 0 ✓
/// Without axiom: measure(n-i) is uninterpreted, nonneg unprovable ✗
///
/// This covers #855 AC2: variant sub-results use logic fn axioms correctly.
///
/// Part of #855
#[test]
#[timeout(30000)]
fn test_variant_nonneg_with_logic_fn_in_variant_expression() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // measure(x) = x * 2
    let measure_fn = LogicFnDef::new(
        "measure".to_string(),
        "test::measure".to_string(),
        vec!["x".to_string()],
        mul(var("x"), int(2)),
    )
    .with_mode(LogicMode::Open);

    // requires: n > 0
    let req = gt(var("n"), int(0));

    // invariant: i >= 0 && i <= n
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    // condition: i < n
    let cond = lt(var("i"), var("n"));

    // body: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // variant: measure(n - i)
    let variant = logic_fn_call("measure", vec![sub(var("n"), var("i"))]);

    // pre-loop: i = 0
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: &[bool_expr(true)],
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&variant),
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig {
            transition_facts: vec![],
            logic_fns: Some(std::slice::from_ref(&measure_fn)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    // With axiom: measure(n-i) = 2*(n-i) >= 0 when i <= n (from invariant + condition)
    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Verified(_))),
        "Variant nonneg with measure(n-i) = 2*(n-i) should verify: got {:?}",
        result.variant_nonneg
    );

    // Negative control: without axiom, measure(n-i) is uninterpreted
    let result_no_fn = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: &[bool_expr(true)],
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&variant),
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // Without axiom: measure(n-i) is uninterpreted, so ay should find a
    // counterexample.
    assert!(
        matches!(
            result_no_fn.variant_nonneg,
            Some(VerificationResult::Failed(_))
        ),
        "Without axiom, variant nonneg should fail (measure uninterpreted). Got {:?}",
        result_no_fn.variant_nonneg
    );
}

/// Isolation test: variant decrease uses logic fn in variant expression.
///
/// ```text
/// #[logic(open)] fn measure(x) = x * 2
///
/// invariant: i >= 0 && i <= n
/// condition: i < n
/// variant: measure(n - i)
/// body: i' = i + 1
/// ```
///
/// Variant decrease: measure(n - i') < measure(n - i)
/// With axiom: measure(n - (i+1)) = 2*(n-i-1) < 2*(n-i) = measure(n-i) ✓
/// Without axiom: measure terms are uninterpreted, decrease unprovable ✗
///
/// Part of #855
#[test]
#[timeout(30000)]
fn test_variant_decrease_with_logic_fn_in_variant_expression() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // measure(x) = x * 2
    let measure_fn = LogicFnDef::new(
        "measure".to_string(),
        "test::measure".to_string(),
        vec!["x".to_string()],
        mul(var("x"), int(2)),
    )
    .with_mode(LogicMode::Open);

    // invariant: i >= 0 && i <= n
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    // condition: i < n
    let cond = lt(var("i"), var("n"));

    // body: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // variant: measure(n - i)
    let variant = logic_fn_call("measure", vec![sub(var("n"), var("i"))]);

    // pre-loop: i = 0
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[bool_expr(true)],
        ensures: &[bool_expr(true)],
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&variant),
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig {
            transition_facts: vec![],
            logic_fns: Some(std::slice::from_ref(&measure_fn)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    // With axiom: measure(n-(i+1)) = 2*(n-i-1) < 2*(n-i) = measure(n-i) when i < n
    assert!(
        matches!(
            result.variant_decrease,
            Some(VerificationResult::Verified(_))
        ),
        "Variant decrease with measure(n-i) should verify: got {:?}",
        result.variant_decrease
    );

    // Negative control: without axiom
    let result_no_fn = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[bool_expr(true)],
        ensures: &[bool_expr(true)],
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&variant),
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // Without axiom: measure(n-i) is uninterpreted, so ay should find a
    // counterexample.
    assert!(
        matches!(
            result_no_fn.variant_decrease,
            Some(VerificationResult::Failed(_))
        ),
        "Without axiom, variant decrease should fail (measure uninterpreted). Got {:?}",
        result_no_fn.variant_decrease
    );
}

/// Sub-result independence: initialization fails while postcondition passes.
///
/// ```text
/// #[logic(open)] fn dbl(x) = x + x
///
/// invariant: acc == dbl(i) && i >= 0
/// ensures: result >= 0
/// pre-loop: i = 0, acc = 99    (WRONG: dbl(0) = 0 ≠ 99)
/// modified: acc                (so the bad entry value is not framed at exit)
/// return: acc
/// ```
///
/// Initialization FAILS: acc=99, dbl(0)=0+0=0, 99 ≠ 0.
/// Postcondition PASSES: invariant ∧ ¬condition ⟹ result = acc = dbl(i) = i+i.
///   Since i >= 0, dbl(i) = i+i >= 0, so result >= 0. ✓
///
/// This tests that the postcondition VC is evaluated independently of
/// initialization. `acc` is listed as modified on purpose: otherwise loop
/// framing would correctly carry the bad entry assignment `acc == 99` into the
/// postcondition base, making the base inconsistent rather than independent.
///
/// Part of #855
#[test]
#[timeout(60000)]
fn test_initialization_fails_postcondition_passes_independence() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // dbl(x) = x + x (linear — avoids nonlinear arithmetic issues)
    let dbl_fn = LogicFnDef::new(
        "dbl".to_string(),
        "test::dbl".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    // requires: n >= 0
    let req = ge(var("n"), int(0));

    // ensures: result >= 0
    let ens = ge(var("result"), int(0));

    // invariant: acc == dbl(i) && i >= 0
    let inv = and(
        eq(var("acc"), logic_fn_call("dbl", vec![var("i")])),
        ge(var("i"), int(0)),
    );

    // condition: i < n
    let cond = lt(var("i"), var("n"));

    // pre-loop: i = 0, acc = 99 (DELIBERATELY WRONG — dbl(0) = 0, not 99)
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop.insert("acc".to_string(), NamedBindingValue::untyped(int(99)));

    // return: acc
    let return_expr = var("acc");

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: std::slice::from_ref(&ens),
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["acc"],
        body_effect: &HashMap::new(),
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
            logic_fns: Some(std::slice::from_ref(&dbl_fn)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    // Initialization MUST fail: 99 != dbl(0) = 0+0 = 0
    assert!(
        matches!(result.initialization, VerificationResult::Failed(_)),
        "Initialization should fail: acc=99, dbl(0)=0, 99≠0. Got {:?}",
        result.initialization
    );

    // Postcondition should pass: invariant says acc == dbl(i) = i+i,
    // i >= 0, so acc = i+i >= 0, and result = acc, so result >= 0.
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Postcondition should pass: result = acc = dbl(i) = i+i >= 0. Got {:?}",
        result.postcondition
    );

    // all_verified must be false (initialization failed)
    assert!(
        !result.all_verified(),
        "all_verified() must be false when initialization fails: got {:?}",
        result.overall()
    );
}
