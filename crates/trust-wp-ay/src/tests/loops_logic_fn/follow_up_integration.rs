// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::*;

// =============================================================================
// Loop + logic_fn integration tests (#739 follow-up)
// =============================================================================

/// Integration: full end-to-end loop verification with logic function — all 5 VCs.
///
/// Tests that a complete loop with a discriminating logic function dependency
/// verifies across initialization, preservation, postcondition, variant nonneg,
/// and variant decrease simultaneously. Prior tests checked individual VCs;
/// this confirms the full pipeline holds together.
///
/// ```text
/// #[logic] fn cap(x) = x + 5   (Open)
///
/// requires: n >= 0
/// ensures:  result >= 5            (discriminating: needs cap(0) = 5)
/// invariant: acc == cap(i) && i >= 0 && i <= n
/// condition: i < n
/// variant: n - i
/// body: acc' = acc + 1, i' = i + 1
/// pre-loop: i = 0, acc = 5         (cap(0) = 0 + 5 = 5)
/// return: acc
/// ```
///
/// The invariant `acc == cap(i)` is discriminating: without the axiom
/// `cap(x) = x + 5`, the solver cannot prove `5 == cap(0)` for initialization.
/// The postcondition `result >= 5` is also discriminating: after the loop,
/// `result = acc = cap(n) = n + 5 >= 5` requires the axiom.
///
/// Re: #739
#[test]
#[timeout(90000)]
fn test_loop_full_end_to_end_with_logic_fn() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // cap(x) = x + 5
    let cap_fn = LogicFnDef::new(
        "cap".to_string(),
        "test::cap".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(5)),
    )
    .with_mode(LogicMode::Open);

    // requires: n >= 0
    let req = ge(var("n"), int(0));

    // ensures: result >= 5
    let ens = ge(var("result"), int(5));

    // invariant: acc == cap(i) && i >= 0 && i <= n
    let inv = and(
        eq(var("acc"), logic_fn_call("cap", vec![var("i")])),
        and(ge(var("i"), int(0)), le(var("i"), var("n"))),
    );

    // condition: i < n
    let cond = lt(var("i"), var("n"));

    // body: acc' = acc + 1, i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("acc".to_string(), add(var("acc"), int(1)));
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // variant: n - i
    let variant = sub(var("n"), var("i"));

    // pre-loop: i = 0, acc = 5 (= cap(0))
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop.insert("acc".to_string(), NamedBindingValue::untyped(int(5)));

    // return: acc
    let return_expr = var("acc");

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: std::slice::from_ref(&ens),
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "acc"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&variant),
        pre_loop_assignments: &pre_loop,
        return_expr: Some(&return_expr),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig {
            transition_facts: vec![],
            logic_fns: Some(std::slice::from_ref(&cap_fn)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Initialization (5 == cap(0)) should verify with axiom: got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Postcondition (cap(n) >= 5) should verify with axiom: got {:?}",
        result.postcondition
    );
    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Verified(_))),
        "Variant nonneg should verify: got {:?}",
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
    assert!(
        result.all_verified(),
        "All 5 VCs should verify for the full end-to-end loop: got {:?}",
        result.overall()
    );

    // Negative control: without axiom, initialization must fail (5 == cap(0) unprovable)
    let result_no_fn = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: std::slice::from_ref(&ens),
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i", "acc"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&variant),
        pre_loop_assignments: &pre_loop,
        return_expr: Some(&return_expr),
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        !result_no_fn.all_verified(),
        "Without axiom, full loop should NOT all-verify: got {:?}",
        result_no_fn.overall()
    );
}

/// Integration: preservation with tuple + logic function axioms combined.
///
/// Tests that both tuple constructor/accessor axioms AND logic function axioms
/// are available during preservation. Extends `test_loop_initialization_logic_fn_with_tuple_axioms`
/// which only tested initialization.
///
/// ```text
/// #[logic] fn pair_sum(p) = get_0(p) + get_1(p)   (Open)
///
/// invariant: pair_sum(state) >= 0
/// condition: i < n
/// body: state' = tuple2(get_0(state) + 1, get_1(state) + 1), i' = i + 1
/// ```
///
/// Preservation VC: `pair_sum(state) >= 0 && i < n => pair_sum(state') >= 0`
/// With axioms: pair_sum(tuple2(a+1, b+1)) = get_0(tuple2(a+1,b+1)) + get_1(tuple2(a+1,b+1))
///            = (a+1) + (b+1) = (a+b) + 2 >= 0 + 2 >= 0. ✓
///
/// Without pair_sum axiom: pair_sum(state') is uninterpreted. ✗
///
/// Re: #739
#[test]
#[timeout(90000)]
fn test_loop_preservation_logic_fn_with_tuple_axioms() {
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

    // invariant: pair_sum(state) >= 0 && i >= 0
    let inv = and(
        ge(logic_fn_call("pair_sum", vec![var("state")]), int(0)),
        ge(var("i"), int(0)),
    );

    // condition: i < 10
    let cond = lt(var("i"), int(10));

    // body: state' = tuple2(get_0(state) + 1, get_1(state) + 1), i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "state".to_string(),
        logic_fn_call(
            "__trust_wp_tuple2",
            vec![
                add(
                    logic_fn_call("__trust_wp_tuple_get_0", vec![var("state")]),
                    int(1),
                ),
                add(
                    logic_fn_call("__trust_wp_tuple_get_1", vec![var("state")]),
                    int(1),
                ),
            ],
        ),
    );
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // WITH pair_sum axiom: preservation should verify
    let result = verify_preservation(
        std::slice::from_ref(&inv),
        Some(&cond),
        &["state", "i"],
        &body_effect,
        &LoopEncoderConfig {
            transition_facts: vec![],
            logic_fns: Some(std::slice::from_ref(&pair_sum_fn)),
            ..LoopEncoderConfig::default()
        },
    )
    .unwrap();

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "With pair_sum axiom, preservation should verify: got {:?}",
        result
    );
}

/// Integration: Option axioms + logic function in loop invariant.
///
/// Tests that both Option axioms (`is_some`, `unwrap`) and a user-defined
/// logic function are correctly registered and interact during loop verification.
///
/// ```text
/// #[logic] fn abs_val(x) = if x >= 0 then x else 0 - x   (Open)
///
/// invariant: opt.is_some() && abs_val(opt.unwrap()) >= 0
/// pre-loop: opt = Some(42)
/// ```
///
/// Initialization VC: `opt = Some(42) => is_some(opt) && abs_val(unwrap(opt)) >= 0`
/// With all axioms: is_some(Some(42)) = true, unwrap(Some(42)) = 42,
///   abs_val(42) = 42 >= 0. ✓
///
/// The abs_val dependency is discriminating: without the axiom, abs_val(42) is
/// uninterpreted, so `abs_val(unwrap(Some(42))) >= 0` is unprovable.
///
/// Re: #739
#[test]
#[timeout(90000)]
fn test_loop_initialization_option_with_logic_fn() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // abs_val(x) = if x >= 0 then x else 0 - x
    let abs_val_fn = LogicFnDef::new(
        "abs_val".to_string(),
        "test::abs_val".to_string(),
        vec!["x".to_string()],
        ite(ge(var("x"), int(0)), var("x"), sub(int(0), var("x"))),
    )
    .with_mode(LogicMode::Open);

    // pre-loop: opt = Some(42)
    let some_42 = logic_fn_call("Some", vec![int(42)]);
    let mut pre_loop = HashMap::new();
    pre_loop.insert("opt".to_string(), NamedBindingValue::untyped(some_42));

    // invariant: opt.is_some() && abs_val(opt.unwrap()) >= 0
    let inv = and(
        method_call(var("opt"), "is_some", vec![]),
        ge(
            logic_fn_call("abs_val", vec![method_call(var("opt"), "unwrap", vec![])]),
            int(0),
        ),
    );

    // WITH abs_val axiom + Option axioms (auto-asserted): initialization should verify
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
            logic_fns: Some(std::slice::from_ref(&abs_val_fn)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Option + logic fn initialization should verify (abs_val(unwrap(Some(42))) = 42 >= 0): got {:?}",
        result.initialization
    );

    // WITHOUT abs_val axiom: initialization should NOT verify
    // abs_val(42) is uninterpreted, abs_val(42) >= 0 is unprovable
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

    // abs_val(42) is uninterpreted — the solver should find a model where
    // abs_val(42) = -1, making !(is_some(opt) && abs_val(unwrap(opt)) >= 0)
    // SAT. Expected result: Failed.
    assert!(
        matches!(result_no_fn.initialization, VerificationResult::Failed(_)),
        "Without abs_val axiom, initialization must fail: got {:?}",
        result_no_fn.initialization
    );
}

/// Documents ay E-matching limitation for transitive logic function chains.
///
/// Tests transitive closure filtering in `filter_logic_fns_for_loop_with_modes`
/// — both `inc` and `inc2` are correctly registered (transitive closure works).
/// However, ay's E-matching cannot resolve the chained nested application
/// `inc2(0) = inc(inc(0)) = inc(1) = 2` because it requires multiple rounds
/// of quantifier instantiation through intermediate UF applications.
///
/// ```text
/// #[logic] fn inc(x) = x + 1    (Open)
/// #[logic] fn inc2(x) = inc(inc(x))    (Open, references inc transitively)
///
/// invariant: acc == inc2(i)
/// pre-loop: i = 0, acc = 2        (inc2(0) = inc(inc(0)) = inc(1) = 2)
/// ```
///
/// Both axioms are asserted:
///   forall x. inc(x) = x + 1
///   forall x. inc2(x) = inc(inc(x))
/// But E-matching with `inc2(0)` as trigger instantiates inc2 to get `inc(inc(0))`,
/// then needs to instantiate `inc` for the fresh term `inc(0)`, then again for
/// `inc(1)`. This multi-step chain exceeds ay's single-round E-matching depth.
///
/// Result: Failed (counterexample with unresolved inc2(0)), confirming this is
/// a solver limitation rather than a trust-wp encoding bug.
///
/// Re: #739
#[test]
#[timeout(90000)]
fn test_loop_initialization_transitive_logic_fn_chain() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // inc(x) = x + 1
    let inc_fn = LogicFnDef::new(
        "inc".to_string(),
        "test::inc".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(1)),
    )
    .with_mode(LogicMode::Open);

    // inc2(x) = inc(inc(x))  — transitively depends on inc
    let inc2_fn = LogicFnDef::new(
        "inc2".to_string(),
        "test::inc2".to_string(),
        vec!["x".to_string()],
        logic_fn_call("inc", vec![logic_fn_call("inc", vec![var("x")])]),
    )
    .with_mode(LogicMode::Open);

    let logic_fns = vec![inc_fn, inc2_fn];

    // invariant: acc == inc2(i)
    let inv = eq(var("acc"), logic_fn_call("inc2", vec![var("i")]));

    // pre-loop: i = 0, acc = 2 (inc2(0) = inc(inc(0)) = inc(1) = 2)
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop.insert("acc".to_string(), NamedBindingValue::untyped(int(2)));

    // WITH both logic functions: ay can now chain through
    // inc2(0) → inc(inc(0)) → inc(1) → 2 via E-matching, verifying the
    // invariant initialization. Previously failed due to E-matching depth
    // limitation (ay pin pre-0b51dbdbd233). (#1603 Category C)
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
            logic_fns: Some(&logic_fns),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    // ay E-matching now chains through transitive logic function definitions.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Transitive chain initialization should verify (ay E-matching improved): got {:?}",
        result.initialization
    );

    // WITHOUT logic functions: also fails (uninterpreted inc2)
    let result_no_fns = verify_loop_invariant_positional(&LoopVerificationContext {
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

    // inc2(i) is uninterpreted without logic function axioms, so ay should
    // find a counterexample.
    assert!(
        matches!(result_no_fns.initialization, VerificationResult::Failed(_)),
        "Without logic fn axioms, initialization should fail: got {:?}",
        result_no_fns.initialization
    );
}
