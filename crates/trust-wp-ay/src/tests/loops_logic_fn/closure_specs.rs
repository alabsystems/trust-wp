// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::formula::NamedBindingValue;

use super::*;

// =============================================================================
// Closure-spec method calls in loop invariants (#739 AC: assert_loop_axioms)
//
// These tests exercise the closure law axiom registration path in loop
// verification. Prior to #739, closure laws (fn_mut_once, fn_closure_laws)
// were only asserted in function-level verification. The fix added
// `assert_loop_axioms` to all five loop sub-verifiers.
//
// Coverage gap: all 38 tests above exercise logic_fns, tuples, and
// Option/Result in loops, but NONE exercise closure-spec predicates
// (precondition, postcondition, postcondition_mut) in loop invariants.
// =============================================================================

/// Loop invariant referencing a closure postcondition.
///
/// Models a loop that calls a closure `f` on each element and tracks
/// that the closure's postcondition holds on the accumulated result:
///
/// ```text
/// #[requires(f.precondition(0))]
/// #[requires(f.postcondition(0, init))]
/// #[invariant(f.postcondition(0, acc))]
/// while i < n {
///     // (body does NOT modify f — only acc changes)
///     acc = g(acc); // simplified: acc' = acc + 1
///     i += 1;
/// }
/// ```
///
/// The invariant `f.postcondition(0, acc)` requires the encoder to:
/// 1. Select UFLIA (closure spec methods are uninterpreted functions)
/// 2. Declare the `closure_postcondition_3_i_i_i` symbol
/// 3. Assert closure law axioms via `assert_loop_axioms`
///
/// Since postcondition is uninterpreted and we assume it holds on the
/// initial value, preservation requires that postcondition(0, acc+1)
/// follows from postcondition(0, acc). This CANNOT be proven without
/// additional axioms about postcondition's behavior, so preservation
/// should fail (the solver finds a counterexample where
/// postcondition(0, acc) holds but postcondition(0, acc+1) does not).
///
/// The initialization check CAN be proven because we explicitly assume
/// f.postcondition(0, acc) in requires and pre_loop_assignments set
/// acc = init where f.postcondition(0, init) is in requires.
///
/// Re: #739
#[test]
#[timeout(30000)]
fn test_loop_initialization_with_closure_postcondition_in_invariant() {
    // requires: f.postcondition(0, init)
    let req = method_call(var("f"), "postcondition", vec![int(0), var("init")]);

    // invariant: f.postcondition(0, acc)
    let inv = method_call(var("f"), "postcondition", vec![int(0), var("acc")]);

    // pre-loop: acc = init
    let mut pre_loop = HashMap::new();
    pre_loop.insert("acc".to_string(), NamedBindingValue::untyped(var("init")));

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
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // Initialization: requires f.postcondition(0, init), pre-loop acc=init,
    // so the invariant f.postcondition(0, acc) becomes f.postcondition(0, init)
    // which is directly assumed. Should verify.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Initialization with closure postcondition in invariant should verify \
         (postcondition(0, init) is assumed, acc=init): got {:?}",
        result.initialization
    );
}

/// Negative control: closure postcondition invariant fails without matching requires.
///
/// Same as the positive test above but WITHOUT the requires assumption.
/// The invariant f.postcondition(0, acc) has no backing assumption, so
/// initialization should fail: the solver can set postcondition(0, init)
/// to false since it's uninterpreted.
///
/// Re: #739
#[test]
#[timeout(30000)]
fn test_loop_initialization_closure_postcondition_fails_without_assumption() {
    // NO requires — postcondition is uninterpreted and unconstrained

    // invariant: f.postcondition(0, acc)
    let inv = method_call(var("f"), "postcondition", vec![int(0), var("acc")]);

    // pre-loop: acc = 0
    let mut pre_loop = HashMap::new();
    pre_loop.insert("acc".to_string(), NamedBindingValue::untyped(int(0)));

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

    // Without the assumption, postcondition(0, 0) is uninterpreted.
    // The solver finds a counterexample where postcondition(0, 0) = false.
    assert!(
        matches!(result.initialization, VerificationResult::Failed(_)),
        "Without requires assumption, closure postcondition invariant should fail \
         (postcondition is uninterpreted, solver sets it to false): got {:?}",
        result.initialization
    );
}

/// Loop with closure precondition and postcondition in loop verification.
///
/// Tests that `precondition` and `postcondition` closure-spec symbols are
/// correctly declared in the loop context, and that initialization/preservation
/// produce the expected outcomes (init passes via assumption, preservation
/// fails because postcondition is uninterpreted).
///
/// ```text
/// requires: f.precondition(x)
/// requires: f.postcondition(x, result_0)  // Fn call assumption
/// invariant: f.postcondition(x, acc)
/// pre-loop: acc = result_0, i = 0
/// body: i' = i + 1, acc' = acc + 1
/// ```
///
/// This test exercises multiple closure-spec symbols in a single loop
/// verification call, covering both initialization and preservation paths.
///
/// Re: #739
#[test]
#[timeout(30000)]
fn test_loop_invariant_with_closure_precondition_and_postcondition() {
    // requires: f.precondition(x) AND f.postcondition(x, result_0) AND n >= 0
    let req_precond = method_call(var("f"), "precondition", vec![var("x")]);
    let req_postcond = method_call(var("f"), "postcondition", vec![var("x"), var("result_0")]);
    // n >= 0 required so auto-invariant `i <= n` is provable at init (0 <= n).
    let req_n_nonneg = ge(var("n"), int(0));

    // invariant: f.postcondition(x, acc)
    let inv = method_call(var("f"), "postcondition", vec![var("x"), var("acc")]);

    // pre-loop: acc = result_0
    let mut pre_loop = HashMap::new();
    pre_loop.insert(
        "acc".to_string(),
        NamedBindingValue::untyped(var("result_0")),
    );

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req_precond, req_postcond, req_n_nonneg],
        ensures: &[],
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&lt(var("i"), var("n"))),
        condition_is_body_break: false,
        modified_vars: &["i", "acc"],
        body_effect: &{
            let mut be = HashMap::new();
            be.insert("i".to_string(), add(var("i"), int(1)));
            be.insert("acc".to_string(), add(var("acc"), int(1)));
            be
        },
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &{
            let mut pl = pre_loop.clone();
            pl.insert("i".to_string(), NamedBindingValue::untyped(int(0)));
            pl
        },
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // Initialization: acc = result_0, postcondition(x, result_0) is assumed,
    // so postcondition(x, acc) = postcondition(x, result_0) holds.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Initialization with closure precondition+postcondition should verify: got {:?}",
        result.initialization
    );

    // Preservation: postcondition(x, acc) does NOT imply postcondition(x, acc+1)
    // for uninterpreted postcondition. Should fail.
    assert!(
        matches!(result.preservation, VerificationResult::Failed(_)),
        "Preservation should fail (postcondition is uninterpreted, \
         postcondition(x, acc) ⇏ postcondition(x, acc+1)): got {:?}",
        result.preservation
    );
}

/// Loop postcondition_once in invariant — plumbing test.
///
/// Uses only `postcondition_once` (no cross-trait law needed). This is a
/// plumbing test verifying that `postcondition_once` method calls in loop
/// invariants trigger the UFLIA encoder path and that `assert_loop_axioms`
/// runs without errors.
///
/// ```text
/// requires: f.postcondition_once(x, init)
/// invariant: f.postcondition_once(x, acc)
/// pre-loop: acc = init
/// ```
///
/// Re: #739
#[test]
#[timeout(30000)]
fn test_loop_initialization_postcondition_once_in_invariant() {
    // requires: f.postcondition_once(x, init)
    let req = method_call(var("f"), "postcondition_once", vec![var("x"), var("init")]);

    // invariant: f.postcondition_once(x, acc)
    let inv = method_call(var("f"), "postcondition_once", vec![var("x"), var("acc")]);

    // pre-loop: acc = init
    let mut pre_loop = HashMap::new();
    pre_loop.insert("acc".to_string(), NamedBindingValue::untyped(var("init")));

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
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // postcondition_once(x, init) is assumed, acc = init, so
    // postcondition_once(x, acc) = postcondition_once(x, init) holds.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Initialization with postcondition_once should verify \
         (direct assumption substitution): got {:?}",
        result.initialization
    );
}

/// Closure postcondition_mut invariant with postcondition_once in requires
/// exercises the FnMut→FnOnce law forward axiom in loop context.
///
/// ```text
/// requires: f.postcondition_mut(x, f_state, init)
/// invariant: f.postcondition_once(x, acc)
/// pre-loop: acc = init
/// ```
///
/// The FnMut law axiom says:
///   postcondition_mut(self, arg, res_state, result)
///     ⟹ postcondition_once(self, arg, result)
///
/// So from postcondition_mut(f, x, f_state, init) we derive
/// postcondition_once(f, x, init). With acc = init, the invariant
/// postcondition_once(f, x, acc) holds.
///
/// This test will ONLY pass if assert_fn_mut_once_law() fires in the
/// loop initialization verifier. Without it, postcondition_once and
/// postcondition_mut are unrelated uninterpreted functions.
///
/// Re: #739
#[test]
#[timeout(30000)]
fn test_loop_initialization_fnmut_law_fires_in_loop_context() {
    // requires: f.postcondition_mut(x, f_state, init)
    let req = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("f_state"), var("init")],
    );

    // invariant: f.postcondition_once(x, acc)
    let inv = method_call(var("f"), "postcondition_once", vec![var("x"), var("acc")]);

    // pre-loop: acc = init
    let mut pre_loop = HashMap::new();
    pre_loop.insert("acc".to_string(), NamedBindingValue::untyped(var("init")));

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
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    // With the FnMut law:
    //   postcondition_mut(f, x, f_state, init) ⟹ postcondition_once(f, x, init)
    // So postcondition_once(f, x, acc) with acc=init should verify.
    //
    // Without the law, postcondition_once and postcondition_mut are unrelated
    // uninterpreted functions, and the solver would find a counterexample.
    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "FnMut law should fire in loop context: postcondition_mut ⟹ postcondition_once. \
         If this fails, assert_fn_mut_once_law() is not being called in loop initialization. \
         Got {:?}",
        result.initialization
    );
}
