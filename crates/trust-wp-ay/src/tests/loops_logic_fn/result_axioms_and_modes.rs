// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::*;

// =============================================================================
// Result axiom integration tests (gap: Option axioms have 3 tests, Result has 0)
// =============================================================================

/// Loop initialization with Result axioms: `Ok(x)` constructor + `is_ok` + `unwrap`.
///
/// Models:
/// ```rust
/// fn process_items(items: &[i32]) -> Result<i32, ()> {
///     let mut result_val: Result<i32, ()> = Ok(0);
///     #[invariant(result_val.is_ok() && result_val.unwrap() >= 0)]
///     for item in items {
///         result_val = Ok(result_val.unwrap() + item.abs());
///     }
///     result_val
/// }
/// ```
///
/// Initialization check: `result_val = Ok(0)` ⟹ `is_ok(result_val) && unwrap(result_val) >= 0`
/// With Result axioms: `is_ok(Ok(0)) = true`, `unwrap(Ok(0)) = 0`, `0 >= 0` ✓
/// Without axioms: `is_ok` and `unwrap` are uninterpreted on `Ok(0)` ✗
#[test]
#[timeout(30000)]
fn test_loop_initialization_with_result_axioms() {
    // pre-loop: result_val = Ok(0)
    let ok_0 = logic_fn_call("Ok", vec![int(0)]);

    // invariant: result_val.is_ok() && result_val.unwrap() >= 0
    let inv = and(
        method_call(var("result_val"), "is_ok", vec![]),
        ge(method_call(var("result_val"), "unwrap", vec![]), int(0)),
    );

    let mut pre_loop = HashMap::new();
    pre_loop.insert("result_val".to_string(), NamedBindingValue::untyped(ok_0));

    // Loop verification calls assert_option_result_axioms() which includes Result axioms.
    // With axioms: is_ok(logic_Ok(0)) = true, spec_unwrap(logic_Ok(0)) = 0, 0 >= 0 ✓
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
        "Result axioms should verify is_ok(Ok(0)) && unwrap(Ok(0)) >= 0: got {:?}",
        result.initialization
    );
}

/// Raw native-constructor companion for Result initialization.
///
/// Companion to `test_loop_initialization_with_result_axioms`. The raw encoder
/// check is typed as `ResultIntInt` so it follows the same native
/// constructor/tester/selector semantics as loop bootstrap. Under those
/// semantics, `Ok(0).is_ok()` and `Ok(0).unwrap() == 0` are built in, so the
/// negated invariant is UNSAT even before the legacy UF axiom block is asserted.
///
/// Re: #739 gap analysis
#[test]
#[timeout(30000)]
fn test_loop_initialization_result_axioms_negative_control() {
    let ok_0 = logic_fn_call("Ok", vec![int(0)]);
    let result_val = var_with_sort(
        "result_val",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("ResultIntInt")),
    );

    let invariant = and(
        method_call(result_val.clone(), "is_ok", vec![]),
        ge(method_call(result_val.clone(), "unwrap", vec![]), int(0)),
    );

    let assignment = eq(result_val, ok_0);

    // Without explicit axioms: native datatype semantics are already enough.
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
        "Native Result constructor/tester/selector semantics should make the negated invariant UNSAT even without explicit axioms, got: {:?}",
        result_without
    );

    // With the legacy UF axiom assertion as well: same formula remains UNSAT.
    // Encode first so any fallback symbols needed by the assertion path exist.
    let mut with_axioms = AYEncoder::new_with_quantifiers();
    with_axioms.register_sort_hints(std::slice::from_ref(&assignment));
    with_axioms.register_sort_hints(std::slice::from_ref(&invariant));
    with_axioms.register_formula_sort_hints(std::slice::from_ref(&invariant));

    let assignment_term2 = with_axioms.encode_pure(&assignment).unwrap();
    with_axioms.assert_term(assignment_term2);
    let invariant_term2 = with_axioms.encode_pure(&invariant).unwrap();
    // Assert axioms AFTER encoding (spec_functions now populated)
    with_axioms.assert_option_result_axioms();
    let neg_invariant2 = {
        let solver = with_axioms.solver_mut();
        solver.not(invariant_term2)
    };
    with_axioms.assert_term(neg_invariant2);

    let with_axioms_result = with_axioms.check_sat();
    assert!(
        matches!(with_axioms_result, SolveResult::Unsat(_)),
        "With Result axioms, negated invariant should be UNSAT: got {with_axioms_result:?}"
    );
}

// =============================================================================
// LogicMode::Default suppression in loop context (gap: only Open tested)
// =============================================================================

/// LogicMode::Default correctly suppresses axiom body in loop verification.
///
/// Uses the same `double(x) = x + x` logic function as the original #739 regression
/// test, but with `LogicMode::Default` instead of `LogicMode::Open`. In Default mode,
/// the body is opaque (not emitted as a defining axiom), so `double(0)` remains
/// uninterpreted and the invariant `acc == double(i)` cannot be proved.
///
/// This test confirms that mode handling works correctly in the loop verification
/// path — not just in function verification.
#[test]
#[timeout(30000)]
fn test_loop_initialization_logic_fn_default_mode_suppresses_axiom() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // double(x) = x + x — but in Default mode (body is opaque)
    let double_fn = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Default);

    // invariant: acc == double(i)
    let inv = eq(var("acc"), logic_fn_call("double", vec![var("i")]));

    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop.insert("acc".to_string(), NamedBindingValue::untyped(int(0)));

    // With Default-mode logic function: initialization should NOT verify
    // (double is uninterpreted; 0 == double(0) is unprovable)
    let result_default = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("n"), int(0))],
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

    // Default mode: function IS declared as UF but no defining axiom emitted.
    // Solver can assign double(0) to any value and finds a counterexample where
    // double(0) ≠ 0, so this should be Failed.
    assert!(
        matches!(result_default.initialization, VerificationResult::Failed(_)),
        "Default-mode logic fn should suppress axiom, making init fail. Got {:?}",
        result_default.initialization
    );

    // Confirm Open mode DOES verify (control arm)
    let double_fn_open = LogicFnDef::new(
        "double".to_string(),
        "test::double".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    let inv2 = eq(var("acc"), logic_fn_call("double", vec![var("i")]));

    let mut pre_loop2 = HashMap::new();
    pre_loop2.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop2.insert("acc".to_string(), NamedBindingValue::untyped(int(0)));

    let result_open = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("n"), int(0))],
        ensures: &[],
        invariants: std::slice::from_ref(&inv2),
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &HashMap::new(),
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop2,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig {
            transition_facts: vec![],
            logic_fns: Some(std::slice::from_ref(&double_fn_open)),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    assert!(
        matches!(result_open.initialization, VerificationResult::Verified(_)),
        "Open-mode logic fn should emit axiom, making init provable: got {:?}",
        result_open.initialization
    );
}

// =============================================================================
// Multiple interacting logic_fns in preservation (gap: only init tested with 2+ fns)
// =============================================================================

/// Two logic functions on *unmodified* variables both needed for preservation.
///
/// Due to the ay E-matching gap on primed variables (documented in
/// `test_loop_preservation_logic_fn_primed_var_e_matching_gap`), logic functions
/// called on *modified* variables in preservation are a known limitation. This
/// test exercises the case where both logic functions are called on *unmodified*
/// variables and the primed invariant requires both axiom bodies.
///
/// Models:
/// ```rust
/// #[logic(open)]
/// fn bound(x: Int) -> Int {
///     x + x
/// }
/// #[logic(open)]
/// fn base(x: Int) -> Int {
///     x + 1
/// }
///
/// #[requires(n >= 0)]
/// fn compute(n: i32) -> i32 {
///     let mut i = 0;
///     let mut acc = 1;
///     #[invariant(i >= 0 && i <= bound(n) && acc >= base(0))]
///     while i < n {
///         i += 1;
///         acc += 1;
///     }
///     acc
/// }
/// ```
///
/// Preservation (only `i` and `acc` modified, `n` unmodified):
/// - `bound(n) = n+n`: `i < n ⟹ i+1 <= n <= 2n = bound(n)` ✓
/// - `base(0) = 0+1 = 1`: `acc >= 1 ⟹ acc+1 >= 2 >= 1 = base(0)` ✓
///
/// Without axioms: both `bound(n)` and `base(0)` are uninterpreted, making
/// `i+1 <= bound(n)` and `acc+1 >= base(0)` unprovable.
#[test]
#[timeout(60000)]
fn test_loop_preservation_two_logic_fns_on_unmodified_vars() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // bound(x) = x + x (gives 2n)
    let bound_fn = LogicFnDef::new(
        "bound".to_string(),
        "test::bound".to_string(),
        vec!["x".to_string()],
        add(var("x"), var("x")),
    )
    .with_mode(LogicMode::Open);

    // base(x) = x + 1 (gives lower bound)
    let base_fn = LogicFnDef::new(
        "base".to_string(),
        "test::base".to_string(),
        vec!["x".to_string()],
        add(var("x"), int(1)),
    )
    .with_mode(LogicMode::Open);

    let logic_fns = vec![bound_fn, base_fn];

    // invariant: i >= 0 && i <= bound(n) && acc >= base(0)
    //   bound(n) = n+n = 2n, base(0) = 0+1 = 1
    // Both logic functions are on *unmodified* variables (n and constant 0),
    // avoiding the ay E-matching primed-variable gap.
    let inv = and(
        and(
            ge(var("i"), int(0)),
            le(var("i"), logic_fn_call("bound", vec![var("n")])),
        ),
        ge(var("acc"), logic_fn_call("base", vec![int(0)])),
    );

    let cond = lt(var("i"), var("n"));

    // body: i' = i + 1, acc' = acc + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));
    body_effect.insert("acc".to_string(), add(var("acc"), int(1)));

    // pre-loop: i = 0, acc = 1
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
    pre_loop.insert("acc".to_string(), NamedBindingValue::untyped(int(1)));

    // With both logic functions: preservation should verify
    let result_with = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("n"), int(0))],
        ensures: &[],
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
            logic_fns: Some(&logic_fns),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    assert!(
        matches!(result_with.initialization, VerificationResult::Verified(_)),
        "With both axioms: initialization should verify (0>=0, 0<=2n, 1>=1): got {:?}",
        result_with.initialization
    );

    assert!(
        matches!(result_with.preservation, VerificationResult::Verified(_)),
        "With both axioms: preservation should verify (i+1<=2n, acc+1>=1): got {:?}",
        result_with.preservation
    );

    // Without logic functions: preservation should NOT verify
    // Both bound(n) and base(0) are uninterpreted, making bounds unprovable.
    let result_without = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[ge(var("n"), int(0))],
        ensures: &[],
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
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // Without axioms: bound(n) and base(0) are uninterpreted, so ay should
    // find a counterexample.
    assert!(
        matches!(result_without.preservation, VerificationResult::Failed(_)),
        "Without axioms: preservation should fail \
         (bound/base uninterpreted). Got {:?}",
        result_without.preservation
    );
}
