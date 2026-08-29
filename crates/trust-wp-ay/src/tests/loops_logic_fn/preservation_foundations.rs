// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::*;

/// Loop preservation with logic function in invariant (#739).
///
/// Tests that logic_fn axiom registration plumbing works in the preservation
/// path: UFLIA encoder is selected, axioms are asserted, no errors occur.
///
/// NOTE: This invariant shape (`i <= double(n)` where `n` is NOT modified)
/// verifies by pure integer arithmetic (`i < double(n)` ⟹ `i+1 <= double(n)`)
/// regardless of `double`'s definition. It does NOT discriminate between
/// with-axiom and without-axiom cases. The companion test
/// `test_loop_preservation_logic_fn_primed_var_e_matching_gap` documents
/// the ay E-matching limitation that prevents writing a discriminating
/// preservation test for logic functions on modified variables.
///
/// ```text
/// #[logic(open)]
/// fn double(x: i32) -> i32 { x + x }
///
/// #[invariant(i >= 0 && i <= double(n))]
/// while i < double(n) { i += 1; }
/// ```
#[test]
#[timeout(60000)]
fn test_loop_preservation_with_logic_fn() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    let double_n = logic_fn_call("double", vec![var("n")]);

    // invariant: i >= 0 && i <= double(n)
    let inv = and(ge(var("i"), int(0)), le(var("i"), double_n.clone()));

    // condition: i < double(n)
    let cond = lt(var("i"), double_n);

    // body effect: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // WITH logic fn: preservation verifies (i' = i+1 <= double(n) = n+n when i < n+n).
    // The axiom `forall x. double(x) = x + x` is registered and available for
    // E-matching during the preservation check, even though pure integer arithmetic
    // suffices for this particular invariant shape.
    let result = verify_preservation(
        std::slice::from_ref(&inv),
        Some(&cond),
        &["i"],
        &body_effect,
        &LoopEncoderConfig {
            transition_facts: vec![],
            logic_fns: Some(std::slice::from_ref(&double_fn)),
            ..LoopEncoderConfig::default()
        },
    )
    .unwrap();

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "With logic fn axiom, preservation should verify: got {:?}",
        result
    );
}

/// Documents ay E-matching limitation for logic_fn axioms on primed variables
/// during loop preservation (#739 follow-up).
///
/// Invariant `acc == double(i)` with body `acc' = acc + 2, i' = i + 1` is
/// mathematically correct: with axiom `double(x) = x + x`, preservation holds
/// because `double(i+1) = (i+1)+(i+1) = double(i)+2 = acc+2`.
///
/// However, ay E-matching cannot instantiate `forall x. double(x) = x + x`
/// for `double(i_prime)` where `i_prime` is a fresh proxy variable introduced
/// during preservation substitution. This is a known ay solver limitation,
/// not a trust-wp encoding bug.
///
/// Result: both WITH and WITHOUT axiom paths fail to verify this preservation,
/// confirming the E-matching gap.
///
/// Re: #739
#[test]
#[timeout(60000)]
fn test_loop_preservation_logic_fn_primed_var_e_matching_gap() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    // invariant: acc == double(i)
    let inv = eq(var("acc"), logic_fn_call("double", vec![var("i")]));

    // condition: i < n
    let cond = lt(var("i"), var("n"));

    // body effect: acc' = acc + 2, i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("acc".to_string(), add(var("acc"), int(2)));
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // WITH axiom: fails due to E-matching limitation on primed variables.
    // The VC is acc == double(i) ∧ i < n ⟹ acc+2 == double(i_prime)
    // where i_prime is a fresh SMT variable. ay E-matching does not
    // instantiate the quantifier for double(i_prime).
    let result_with = verify_preservation(
        std::slice::from_ref(&inv),
        Some(&cond),
        &["acc", "i"],
        &body_effect,
        &LoopEncoderConfig {
            transition_facts: vec![],
            logic_fns: Some(std::slice::from_ref(&double_fn)),
            ..LoopEncoderConfig::default()
        },
    )
    .unwrap();

    // ay E-matching now correctly instantiates the quantifier for primed variables.
    // The formula acc == double(i) ∧ i < n ∧ acc' = acc+2 ∧ i' = i+1 ⟹ acc' == double(i')
    // is mathematically valid (given double(x) = x+x), and ay now proves it.
    // Previously: Failed or Unknown due to ay#2829/ay#2865 E-matching limitations.
    // Now: Verified, confirming the E-matching gap for primed variables is closed.
    // (#739, ay#2829, ay#2865)
    assert!(
        matches!(result_with, VerificationResult::Verified(_)),
        "preservation with axiom on primed vars should now Verify (ay E-matching fixed): got {result_with:?}",
    );

    // WITHOUT axiom: double is completely uninterpreted.
    let result_without = verify_preservation(
        std::slice::from_ref(&inv),
        Some(&cond),
        &["acc", "i"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .unwrap();

    // Without axiom, double is uninterpreted and ay should find a
    // counterexample.
    assert!(
        matches!(result_without, VerificationResult::Failed(_)),
        "Without axiom, solver should fail for uninterpreted double: got {:?}",
        result_without
    );
}

/// Loop invariant with tuple getter in expression (#739 AC).
///
/// Models a loop that tracks a pair (i, sum) and uses tuple_get_0 in the
/// invariant. This requires UFLIA (tuple functions are uninterpreted) and
/// tuple axioms to be asserted. Without proper encoder selection, the loop
/// would use QF_LIA and fail to handle the UF.
///
/// ```text
/// #[requires(n >= 0)]
/// #[invariant(__trust_wp_tuple_get_0(state) >= 0)]
/// fn counting_pair(n: i32) {
///     let mut state = __trust_wp_tuple2(0, 0);
///     while __trust_wp_tuple_get_0(state) < n {
///         state = __trust_wp_tuple2(
///             __trust_wp_tuple_get_0(state) + 1,
///             __trust_wp_tuple_get_1(state) + __trust_wp_tuple_get_0(state)
///         );
///     }
/// }
/// ```
#[test]
#[timeout(60000)]
fn test_loop_preservation_with_tuple_functions() {
    // invariant: __trust_wp_tuple_get_0(state) >= 0
    let inv = ge(
        logic_fn_call("__trust_wp_tuple_get_0", vec![var("state")]),
        int(0),
    );

    // loop condition: __trust_wp_tuple_get_0(state) < n
    let cond = lt(
        logic_fn_call("__trust_wp_tuple_get_0", vec![var("state")]),
        var("n"),
    );

    // requires: n >= 0
    let req = ge(var("n"), int(0));

    // body effect: state' = __trust_wp_tuple2(get_0(state) + 1, get_1(state) + get_0(state))
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "state".to_string(),
        logic_fn_call(
            "__trust_wp_tuple2",
            vec![
                // get_0(state) + 1
                add(
                    logic_fn_call("__trust_wp_tuple_get_0", vec![var("state")]),
                    int(1),
                ),
                // get_1(state) + get_0(state)
                add(
                    logic_fn_call("__trust_wp_tuple_get_1", vec![var("state")]),
                    logic_fn_call("__trust_wp_tuple_get_0", vec![var("state")]),
                ),
            ],
        ),
    );

    // pre-loop assignment: state = __trust_wp_tuple2(0, 0)
    let mut pre_loop = HashMap::new();
    pre_loop.insert(
        "state".to_string(),
        NamedBindingValue::untyped(logic_fn_call("__trust_wp_tuple2", vec![int(0), int(0)])),
    );

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: &[],
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["state"],
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
    })
    .unwrap();

    // Initialization: get_0(tuple2(0, 0)) >= 0
    // With tuple axioms: get_0(tuple2(0, 0)) = 0 >= 0 ✓
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Initialization should verify (get_0(tuple2(0,0)) = 0 >= 0 via tuple axiom): got {:?}",
        result.initialization
    );

    // Preservation: get_0(state) >= 0 ∧ get_0(state) < n →
    //   get_0(tuple2(get_0(state)+1, ...)) >= 0
    // With tuple axioms: get_0(tuple2(x, y)) = x, so x+1 >= 0 when x >= 0 ✓
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "Preservation should verify (get_0(tuple2(get_0(state)+1, _)) = get_0(state)+1 >= 0): got {:?}",
        result.preservation
    );
}
