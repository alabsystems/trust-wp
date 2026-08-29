// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::*;

fn assert_failed_result(result: &VerificationResult, context: &str) {
    match result {
        VerificationResult::Failed(_) => {}
        other => panic!("{context} should fail verification; got {other:?}"),
    }
}

/// Integration: Option axioms in loop initialization.
///
/// ```text
/// invariant: opt.is_some() && opt.unwrap() >= 0
/// pre-loop: opt = Some(42)
/// ```
///
/// Requires Option axioms (registered via `assert_loop_axioms()` ->
/// `assert_option_result_axioms()`):
///   - `is_some(logic_Some(x))` => true
///   - `spec_unwrap(logic_Some(x))` => x  (internal: method "unwrap" -> "spec_unwrap" UF)
///
/// The `is_some` and `unwrap` method names are registered through the
/// `PureExpr::MethodCall` encoding path (which populates `spec_functions`),
/// while the `Some` constructor goes through `PureExpr::LogicFnCall` with
/// name `"Some"` (the encoder adds the `logic_` prefix internally).
#[test]
#[timeout(30000)]
fn test_loop_initialization_with_option_axioms() {
    // opt = Some(42) — constructor via LogicFnCall (encoder maps "Some" -> "logic_Some")
    let some_42 = logic_fn_call("Some", vec![int(42)]);

    // invariant: opt.is_some() && opt.unwrap() >= 0
    // Using MethodCall so the encoder registers these in spec_functions
    let inv = and(
        method_call(var("opt"), "is_some", vec![]),
        ge(method_call(var("opt"), "unwrap", vec![]), int(0)),
    );

    // pre-loop: opt = Some(42)
    let mut pre_loop = HashMap::new();
    pre_loop.insert("opt".to_string(), NamedBindingValue::untyped(some_42));

    // Loop verification calls assert_loop_axioms() which calls assert_option_result_axioms().
    // With these axioms: is_some(logic_Some(42)) = true, spec_unwrap(logic_Some(42)) = 42 >= 0. ✓
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
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Option axioms should allow is_some(Some(42)) to verify: got {:?}",
        result.initialization
    );
}

/// Raw native-constructor companion for `test_loop_initialization_with_option_axioms`.
///
/// `verify_loop_invariant` always asserts Option/Result axioms, so the "without
/// axiom" arm is expressed with a raw encoder over the equivalent initialization
/// formula: `opt = Some(42) => opt.is_some() && opt.unwrap() >= 0`.
///
/// This is no longer a true negative control: stdlib constructors and spec
/// methods are now encoded through the native datatype/tester/selector path,
/// so `Some(42).is_some()` and `Some(42).unwrap() == 42` hold without an
/// explicit `assert_option_result_axioms()` call.
///
/// Re: #845
#[test]
#[timeout(30000)]
fn test_loop_initialization_with_option_axioms_negative_control_without_axioms() {
    let some_42 = logic_fn_call("Some", vec![int(42)]);
    let opt = var_with_sort(
        "opt",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("OptionInt")),
    );

    let invariant = and(
        method_call(opt.clone(), "is_some", vec![]),
        ge(method_call(opt.clone(), "unwrap", vec![]), int(0)),
    );

    let assignment = eq(opt, some_42);

    let mut without_axioms = AYEncoder::new_with_quantifiers();
    without_axioms.register_sort_hints(std::slice::from_ref(&assignment));
    without_axioms.register_sort_hints(std::slice::from_ref(&invariant));
    without_axioms.register_formula_sort_hints(std::slice::from_ref(&invariant));

    let assignment_term = without_axioms.encode_pure(&assignment).unwrap();
    without_axioms.assert_term(assignment_term);
    let invariant_term = without_axioms.encode_pure(&invariant).unwrap();
    let neg_invariant = {
        let solver = without_axioms.solver_mut();
        solver.not(invariant_term)
    };
    without_axioms.assert_term(neg_invariant);

    let result_without = without_axioms.check_sat();
    assert!(
        matches!(result_without, SolveResult::Unsat(_)),
        "Native Option constructor/tester/selector semantics should make the negated invariant UNSAT even without explicit axioms, got: {:?}",
        result_without
    );

    let mut with_axioms = AYEncoder::new_with_quantifiers();
    with_axioms.register_sort_hints(std::slice::from_ref(&assignment));
    with_axioms.register_sort_hints(std::slice::from_ref(&invariant));
    with_axioms.register_formula_sort_hints(std::slice::from_ref(&invariant));

    let assignment_term = with_axioms.encode_pure(&assignment).unwrap();
    with_axioms.assert_term(assignment_term);
    let invariant_term = with_axioms.encode_pure(&invariant).unwrap();
    let neg_invariant = {
        let solver = with_axioms.solver_mut();
        solver.not(invariant_term)
    };
    with_axioms.assert_term(neg_invariant);
    with_axioms.assert_option_result_axioms();

    assert!(
        matches!(with_axioms.check_sat(), SolveResult::Unsat(_)),
        "With Option axioms, negated invariant should be UNSAT"
    );
}

/// Preservation must not treat `unwrap_or_default` as inert Option demand.
///
/// The primed invariant is proved from `opt' = Some(42)`. If preservation
/// skips the datatype axiom path, the solver sees `unwrap_or_default(opt')`
/// as an unconstrained method result and this VC stops verifying.
#[test]
#[timeout(30000)]
fn test_loop_preservation_unwrap_or_default_source_demand_uses_axioms() {
    let invariant = ge(method_call(var("opt"), "unwrap_or_default", vec![]), int(0));
    let loop_condition = bool_expr(true);

    let mut body_effect = HashMap::new();
    body_effect.insert("opt".to_string(), logic_fn_call("Some", vec![int(42)]));

    let result = verify_preservation(
        std::slice::from_ref(&invariant),
        Some(&loop_condition),
        &["opt"],
        &body_effect,
        &LoopEncoderConfig::default(),
    )
    .expect("unwrap_or_default preservation should encode");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "unwrap_or_default source demand should force Option axioms in preservation: {result:?}"
    );
}

/// Integration: postcondition with logic_fn applied to loop-modified variable.
///
/// ```text
/// #[logic] fn double(x) = x + x   (Open)
///
/// requires: n >= 0
/// invariant: i >= 0 && i <= n
/// condition: i < n
/// ensures: double(i) == double(n)   (after loop, i == n)
/// body: i' = i + 1
/// return: i
/// pre-loop: i = 0
/// ```
///
/// Postcondition VC: `inv && !cond => double(result) == double(n)`
/// After loop: i == n (from inv `i <= n` and `!(i < n)` => `i == n`).
/// With axiom: `double(n) = n + n = double(n)`. ✓
/// Without axiom: `double(result)` and `double(n)` are uninterpreted;
///   but since result == n, `double(result) == double(n)` is provable by congruence
///   IF the solver treats `double` as a function (UF). Test verifies axiom path.
///
/// Note: This is a NON-DISCRIMINATING plumbing test — the ensures clause
/// `double(result) == double(n)` is provable by UF congruence alone (since
/// `result == n`). See `test_loop_postcondition_logic_fn_discriminating` for
/// the discriminating companion that requires the axiom body.
#[test]
#[timeout(30000)]
fn test_loop_postcondition_logic_fn_on_modified_variable() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    let req = ge(var("n"), int(0));

    // ensures: double(result) == double(n)
    let ens = eq(
        logic_fn_call("double", vec![var("result")]),
        logic_fn_call("double", vec![var("n")]),
    );

    // invariant: i >= 0 && i <= n
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    // condition: i < n
    let cond = lt(var("i"), var("n"));

    // body: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let return_expr = var("i");

    // With logic fn: postcondition should verify
    // inv && !(i < n) => i == n => double(result) == double(n) via congruence + axiom
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
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Postcondition double(result) == double(n) should verify: got {:?}",
        result.postcondition
    );
}

/// Discriminating postcondition test: `double(result) == 2 * n` genuinely
/// requires the axiom body (`double(x) = x + x`), not just UF congruence.
///
/// The non-discriminating sibling test above uses `double(result) == double(n)`,
/// which is provable by congruence alone (since `result == n`). This test
/// uses `2 * n` on the RHS, which forces the solver to expand the axiom.
#[test]
#[timeout(30000)]
fn test_loop_postcondition_logic_fn_discriminating() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    let req = ge(var("n"), int(0));

    // ensures: double(result) == result + result
    // This requires axiom expansion: double(n) = n + n = result + result
    // (since result == n post-loop). Unlike `double(result) == double(n)`,
    // UF congruence alone cannot prove this — the solver must know the body.
    let ens = eq(
        logic_fn_call("double", vec![var("result")]),
        add(var("result"), var("result")),
    );

    // invariant: i >= 0 && i <= n
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    // condition: i < n
    let cond = lt(var("i"), var("n"));

    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let return_expr = var("i");

    // WITH axiom: postcondition should verify
    // double(result) = result + result (by axiom expansion) ✓
    let result_with = verify_loop_invariant_positional(&LoopVerificationContext {
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
        matches!(result_with.postcondition, VerificationResult::Verified(_)),
        "Postcondition double(result) == result+result should verify WITH axiom: got {:?}",
        result_with.postcondition
    );

    // WITHOUT axiom: must fail with a concrete counterexample. If this becomes
    // Unknown, the negative control is no longer proving the missing-axiom path.
    let result_without = verify_loop_invariant_positional(&LoopVerificationContext {
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

    assert_failed_result(
        &result_without.postcondition,
        "postcondition double(result) == result+result without axiom",
    );
}

/// Regression: logic function referenced ONLY in `return_expr` must not
/// be filtered out by `filter_logic_fns_for_loop_with_modes` (#834).
///
/// ```text
/// #[logic] fn compute(x) = x * 2    (Open)
///
/// requires: n >= 0
/// invariant: i >= 0 && i <= n
/// condition: i < n
/// body: i' = i + 1
/// pre-loop: i = 0
/// return_expr: compute(i)            ← logic fn ONLY here
/// ensures: result >= 0               ← no logic fn name here
/// ```
///
/// After result substitution, postcondition becomes `compute(i) >= 0`.
/// Without the #834 fix, `compute` is filtered out and treated as
/// uninterpreted, making the postcondition unprovable. With the fix,
/// the `compute` axiom is included: `compute(i) = i * 2`, and since
/// `i == n >= 0` at loop exit, `compute(i) = 2*n >= 0`.
#[test]
#[timeout(30000)]
fn test_loop_postcondition_logic_fn_only_in_return_expr() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // compute(x) = x * 2
    let compute_fn = LogicFnDef::new(
        "compute".to_string(),
        "test::compute".to_string(),
        vec!["x".to_string()],
        mul(var("x"), int(2)),
    )
    .with_mode(LogicMode::Open);

    // requires: n >= 0
    let req = ge(var("n"), int(0));

    // ensures: result >= 0  (NO logic fn name here — only `result`)
    let ens = ge(var("result"), int(0));

    // invariant: i >= 0 && i <= n
    let inv = and(ge(var("i"), int(0)), le(var("i"), var("n")));

    // condition: i < n
    let cond = lt(var("i"), var("n"));

    // body: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    // return_expr: compute(i) — logic fn ONLY referenced here
    let return_expr = logic_fn_call("compute", vec![var("i")]);

    // WITH logic fn: postcondition should verify.
    // After substitution: ensures becomes `compute(i) >= 0`.
    // Axiom: compute(i) = i * 2.  At loop exit: i == n >= 0, so compute(i) = 2*n >= 0.
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
            logic_fns: Some(std::slice::from_ref(&compute_fn)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    assert!(
        matches!(result.postcondition, VerificationResult::Verified(_)),
        "Postcondition with logic fn only in return_expr should verify (#834): got {:?}",
        result.postcondition
    );

    // WITHOUT logic fn: postcondition should fail with a counterexample.
    // compute(i) is uninterpreted, compute(i) >= 0 is unprovable.
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

    // compute(i) is uninterpreted without the axiom, so ay should find a
    // counterexample.
    assert_failed_result(
        &result_no_fn.postcondition,
        "postcondition with uninterpreted compute without axiom (#834)",
    );
}
