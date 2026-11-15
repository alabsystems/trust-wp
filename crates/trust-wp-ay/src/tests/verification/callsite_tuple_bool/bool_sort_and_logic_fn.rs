// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

/// Regression: `!(result > 0)` should NOT classify `result` as Bool.
///
/// The `Not` negates the comparison (Bool), but `result` inside is Int.
/// If `result_is_bool_by_postcondition` treats `Not(...)` as evidence that
/// all variables inside must be Bool, `result = x + 1` would panic with
/// `mk_eq expects same sort, got Bool = Int`.
#[test]
#[timeout(30000)]
fn test_verify_not_comparison_does_not_force_bool_sort() {
    let req = gt(var("x"), int(0));
    // body: result = x + 1
    let body = add(var("x"), int(1));
    // ensures: !(result <= 0), equivalent to result > 0
    let ens = not(le(var("result"), int(0)));

    let result = verify_function_with_modes(
        VerificationRequest::new(std::slice::from_ref(&req), &[ens]).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "!(result <= 0) with body x+1, x > 0 should verify without Bool sort panic: {result:?}"
    );
}

/// Regression: `if (result > 0) then 1 else 0` should NOT classify `result` as Bool.
///
/// The Ite condition is a Bool context, but `result > 0` is a comparison
/// where `result` is Int. If `result_is_bool_by_postcondition` treats the
/// Ite condition as evidence that all variables inside must be Bool,
/// `result = x + 1` would panic with `mk_eq expects same sort, got Bool = Int`.
#[test]
#[timeout(30000)]
fn test_verify_ite_comparison_condition_does_not_force_bool_sort() {
    let req = gt(var("x"), int(0));
    // body: result = x + 1
    let body = add(var("x"), int(1));
    // ensures: if (result > 0) then true else false
    // This is a tautology when result > 0, which holds since x > 0 and result = x + 1.
    let ens = ite(gt(var("result"), int(0)), bool_expr(true), bool_expr(false));

    let result = verify_function_with_modes(
        VerificationRequest::new(std::slice::from_ref(&req), &[ens]).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Ite with comparison condition should verify without Bool sort panic: {result:?}"
    );
}

/// Bare variable postcondition: `ensures(b)` where `b` is a bool param.
/// Before `register_formula_sort_hints`, the bare `Var("b")` defaulted to Int,
/// causing `mk_not(Int)` panic when the ensures was negated. (#544)
///
/// Strengthened: also checks that `body = true` produces a definite result
/// (not just the absence of a panic).
#[test]
#[timeout(30000)]
fn test_verify_bare_var_postcondition_no_sort_panic() {
    // requires: true (no precondition)
    // ensures: b   (bare variable — implicitly Bool)
    // body: true   (satisfies ensures)
    let ens = var("b");
    let body = bool_expr(true);

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)));
    assert!(
        result.is_ok(),
        "Bare variable postcondition should not panic with sort mismatch: {result:?}"
    );
    // `b` is unconstrained (free variable, not bound to `result`). The solver
    // finds a counterexample where b = false. Pinned to Failed per #774 audit.
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Failed(_)),
        "Unconstrained `b` in postcondition: solver should find counterexample (b=false), got {vr:?}"
    );
}

/// Bare integer as postcondition: `ensures(42)` should be rejected. (#1028, #1077)
/// `is_definitely_non_bool` catches Int literals before they reach ay's mk_not.
#[test]
#[timeout(30000)]
fn test_verify_bare_int_postcondition_rejected() {
    let ens = int(42);
    let body = int(42);
    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)));
    assert!(
        result.is_err(),
        "Bare integer postcondition should be rejected as non-boolean: {result:?}"
    );
    let err_msg = format!("{:?}", result.unwrap_err());
    assert!(
        err_msg.contains("must be boolean"),
        "Error should mention boolean requirement: {err_msg}"
    );
}

/// Arithmetic expression as postcondition: `ensures(x + 1)` should be rejected. (#1028, #1077)
#[test]
#[timeout(30000)]
fn test_verify_arithmetic_postcondition_rejected() {
    let ens = PureExpr::BinOp(Arc::new(var("x")), BinOp::Add, Arc::new(int(1)));
    let body = int(42);
    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)));
    assert!(
        result.is_err(),
        "Arithmetic postcondition should be rejected as non-boolean: {result:?}"
    );
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("boolean") || err_msg.contains("Bool"),
        "Error should mention boolean requirement, got: {err_msg}"
    );
}

/// Logic function call as postcondition: `ensures(is_valid(result))`.
/// The logic function defaults to Int return sort but the postcondition context
/// requires Bool. `register_formula_sort_hints` detects this. (#544)
///
/// Strengthened: checks for definite result, not just non-panic.
#[test]
#[timeout(30000)]
fn test_verify_logic_fn_postcondition_no_sort_panic() {
    // ensures: is_valid(result)  — logic fn call at top level of postcondition
    let ens = logic_fn_call("is_valid", vec![var("result")]);
    let body = int(42);

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)));
    assert!(
        result.is_ok(),
        "Logic function postcondition should not panic with sort mismatch: {result:?}"
    );
    // is_valid is uninterpreted (no definition provided), so the solver finds
    // a counterexample with is_valid(42) false.
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Failed(_)),
        "Uninterpreted is_valid(result) should fail with a counterexample, got {vr:?}"
    );
}

/// Logic function with definition as postcondition: `ensures(is_positive(result))`
/// where `is_positive(x) = x > 0`. With `body = 42`, should verify.
/// This complements `test_verify_logic_fn_postcondition_no_sort_panic` by
/// checking semantic correctness, not just non-crash. (#544, #552)
#[test]
#[timeout(30000)]
fn test_verify_logic_fn_postcondition_positive() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};
    // Define: is_positive(x) = x > 0 (Open mode so axiom is emitted)
    let mut logic_fn = LogicFnDef::new(
        "is_positive".to_string(),
        "crate::is_positive".to_string(),
        vec!["x".to_string()],
        gt(var("x"), int(0)),
    );
    logic_fn.set_mode(LogicMode::Open);
    // ensures: is_positive(result)
    let ens = logic_fn_call("is_positive", vec![var("result")]);
    // body: 42  (positive, so postcondition should hold)
    let body = int(42);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .logic_fns(Some(&[logic_fn])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "is_positive(42) should verify: {result:?}"
    );
}

/// Logic function with definition as postcondition — negative case.
/// `ensures(is_positive(result))` where `body = -1` should FAIL.
/// This catches bugs where logic fn postconditions are vacuously true. (#552)
#[test]
#[timeout(30000)]
fn test_verify_logic_fn_postcondition_negative() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};
    // Define: is_positive(x) = x > 0 (Open mode so axiom is emitted)
    let mut logic_fn = LogicFnDef::new(
        "is_positive".to_string(),
        "crate::is_positive".to_string(),
        vec!["x".to_string()],
        gt(var("x"), int(0)),
    );
    logic_fn.set_mode(LogicMode::Open);
    // ensures: is_positive(result)
    let ens = logic_fn_call("is_positive", vec![var("result")]);
    // body: -1  (negative, so postcondition should fail)
    let body = neg(int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .logic_fns(Some(&[logic_fn])),
    )
    .unwrap();
    assert!(
        crate::tests::rejected(&result),
        "is_positive(-1) should produce counterexample: {result:?}"
    );
}

/// Quantified Bool postconditions must still keep an alias result Bool-sorted.
///
/// Regression for #2624: when `return_expr` is a temporary alias (`call_0`) and
/// the only Bool evidence is under a quantifier body, the result-binding path
/// must not leave `result` as Int. Using a declared Bool-returning logic fn in
/// the quantified equality exercises the remaining context-sensitive case.
#[test]
#[timeout(30000)]
fn test_verify_quantified_logic_fn_bool_equality_on_alias_result_no_sort_panic() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let predicate = LogicFnDef::new(
        "predicate".to_string(),
        "test::predicate".to_string(),
        vec!["x".to_string()],
        gt(var("x"), int(0)),
    )
    .with_mode(LogicMode::Open);

    let body = var("call_0");
    let ens = forall(
        "x",
        eq(var("result"), logic_fn_call("predicate", vec![var("x")])),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .logic_fns(Some(&[predicate])),
    );
    assert!(
        result.is_ok(),
        "quantified Bool logic-fn equality on alias result should not error or sort-panic: {result:?}"
    );

    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Failed(_)),
        "forall x. result == predicate(x) is not universally valid for an unconstrained alias body; \
         expected Failed, got {vr:?}"
    );
}

/// A quantified tautology with direct `result == predicate(x)` comparisons
/// should verify when the only Bool evidence for `result` comes from the
/// quantified postcondition itself.
///
/// This targets the remaining `#2624` risk from the adopted design: the direct
/// equality arm still needs a Bool-aware oracle for declared logic-function
/// ranges under quantifiers, not the generic fallback-to-Int sort inference.
#[test]
#[timeout(30000)]
fn test_verify_quantified_logic_fn_bool_tautology_with_alias_result() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let predicate = LogicFnDef::new(
        "predicate".to_string(),
        "test::predicate".to_string(),
        vec!["x".to_string()],
        gt(var("x"), int(0)),
    )
    .with_mode(LogicMode::Open);

    let predicate_call = logic_fn_call("predicate", vec![var("x")]);
    let typed_eq_tautology = or(
        eq(var("result"), predicate_call.clone()),
        ne(var("result"), predicate_call.clone()),
    );
    let predicate_bool_tautology = or(predicate_call.clone(), not(predicate_call));
    let ens = forall("x", and(typed_eq_tautology, predicate_bool_tautology));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&var("call_0")))
            .logic_fns(Some(&[predicate])),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "quantified Bool equality tautology should verify for alias results: {result:?}"
    );
}

/// Quantifier-body wrapper traversal must preserve Bool evidence for alias
/// results.
///
/// The worker patch fixed bare quantifier recursion only. The adopted `#2624`
/// design also required sort-preserving wrappers such as `let` to recurse,
/// because contracts routinely carry Bool postconditions through wrapper nodes.
#[test]
#[timeout(30000)]
fn test_verify_quantified_let_wrapper_bool_tautology_with_alias_result() {
    let wrapped_result_bool = let_bind("tmp", int(0), or(var("result"), not(var("result"))));
    let ens = forall("x", wrapped_result_bool);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).return_expr(Some(&var("call_0"))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "quantified let-wrapper Bool tautology should verify for alias results: {result:?}"
    );
}

/// User-defined Bool-returning logic fn called in method syntax verifies correctly.
///
/// Regression test for #1820 AC-2/AC-3: a registered logic function
/// `is_valid(x) := x > 0` is called as `result.is_valid()` in a postcondition.
/// Before #1820, unrecognized method calls silently created Int-returning UFs,
/// causing sort mismatches or false positives. Now the fallback routes
/// registered logic functions through `encode_logic_fn_call_impl`, which
/// infers Bool from the body, producing correct Sort::Bool encoding.
#[test]
#[timeout(30000)]
fn test_verify_bool_logic_fn_method_syntax_positive() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};
    // Define: is_valid(x) = x > 0 (Open mode so defining axiom is emitted)
    let logic_fn = LogicFnDef::new(
        "is_valid".to_string(),
        "test::is_valid".to_string(),
        vec!["x".to_string()],
        gt(var("x"), int(0)),
    )
    .with_mode(LogicMode::Open);
    // ensures: result.is_valid()  (method syntax — dispatched to logic fn encoder)
    let ens = method_call(var("result"), "is_valid", vec![]);
    // body: 42  (positive, so is_valid(42) = 42 > 0 = true)
    let body = int(42);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .logic_fns(Some(&[logic_fn])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "result.is_valid() with body=42 should verify: {result:?} (#1820)"
    );
}

/// Negative case: user-defined Bool logic fn in method syntax fails when body violates.
#[test]
#[timeout(30000)]
fn test_verify_bool_logic_fn_method_syntax_negative() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};
    let logic_fn = LogicFnDef::new(
        "is_valid".to_string(),
        "test::is_valid".to_string(),
        vec!["x".to_string()],
        gt(var("x"), int(0)),
    )
    .with_mode(LogicMode::Open);
    // ensures: result.is_valid()
    let ens = method_call(var("result"), "is_valid", vec![]);
    // body: -1  (negative, so is_valid(-1) = -1 > 0 = false)
    let body = neg(int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .logic_fns(Some(&[logic_fn])),
    )
    .unwrap();
    assert!(
        crate::tests::rejected(&result),
        "result.is_valid() with body=-1 should fail: {result:?} (#1820)"
    );
}

/// Bare variable precondition: `requires(flag)` where `flag` is a bool param.
/// Preconditions are asserted via `assert_term` which requires Bool. (#544)
#[test]
#[timeout(30000)]
fn test_verify_bare_var_precondition_no_sort_panic() {
    // requires: flag  (bare variable — implicitly Bool)
    // ensures: result > 0
    // body: 1
    let req = var("flag");
    let ens = gt(var("result"), int(0));
    let body = int(1);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    );
    assert!(
        result.is_ok(),
        "Bare variable precondition should not panic with sort mismatch: {result:?}"
    );
    // body = 1, ensures(result > 0): 1 > 0 is true, so verification should succeed.
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "body=1 with ensures(result > 0) should verify: {vr:?}"
    );
}

/// Bare variable in loop invariant: `invariant(active)`.
/// Loop invariants are formula contexts, asserted via `assert_term`. (#544)
///
/// With `requires(active)`, initialization should verify (active => active).
/// Previously, `active` as a bare variable would cause a sort mismatch panic
/// because the encoder would default it to Int instead of Bool.
#[test]
#[timeout(30000)]
fn test_verify_bare_var_invariant_no_sort_panic() {
    // invariant: active  (bare variable — implicitly Bool)
    let inv = var("active");
    // requires: active  (establishes the invariant for initialization)
    let req = var("active");

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
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
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    });
    assert!(
        result.is_ok(),
        "Bare variable invariant should not panic with sort mismatch: {result:?}"
    );
    let loop_result = result.unwrap();
    assert!(
        matches!(loop_result.initialization, VerificationResult::Verified(_)),
        "active => active should verify for initialization: {:?}",
        loop_result.initialization
    );
}

/// Regression: nested Ite from MIR-desugared `&&` must not panic with Int/Bool
/// branch sort mismatches in `verify_function` (#544).
///
/// Mirrors `reference/creusot/tests/should_succeed/traits/04.rs` body shape:
/// `Ite(_call_3, Ite(_call_6, _call_0, false), false)`.
///
/// This contract is intentionally false for unconstrained calls, so the solver
/// should return `Failed(_)` (counterexample), not panic.
#[test]
#[timeout(30000)]
fn test_verify_nested_ite_bool_literal_branches_no_sort_panic() {
    let ens = eq(var("result"), bool_expr(false));

    let body = ite(
        var("_call_3"),
        ite(var("_call_6"), var("_call_0"), bool_expr(false)),
        bool_expr(false),
    );

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)));
    assert!(
        result.is_ok(),
        "Nested Ite with Bool(false) branches should not panic: {result:?}"
    );
    assert!(
        matches!(result.as_ref().unwrap(), VerificationResult::Failed(_)),
        "Expected a real counterexample (not a panic): {result:?}"
    );
}

/// Regression test for #659: mixed invariant/non-invariant types.
///
/// Simulates two functions in a crate where only `WithInv` has `#[invariant]`:
///   - `WithInv` has `#[invariant(self > 0)]`, `PlainType` does not.
///   - Per-type matching (#659) ensures only `WithInv` params/returns get
///     invariant injection; `PlainType` variables are unconstrained.
///
/// Case 1 (positive): `fn identity(a: WithInv) -> WithInv { a }`
///   - `a.__trust_wp_invariant_WithInv()` assumed, `result = a`,
///     `result.__trust_wp_invariant_WithInv()` should verify via body axiom.
///
/// Case 2 (negative): `fn pass_through(b: PlainType) -> WithInv { b }`
///   - No invariant precondition for `b` (correct per #659 per-type matching).
///   - `result.__trust_wp_invariant_WithInv()` should fail because `b` has no
///     invariant axiom and no relationship to the `WithInv` invariant.
#[test]
#[timeout(30000)]
fn test_verify_mixed_type_invariant_selective_injection() {
    use trust_wp_core::logic::type_invariant_method_name;

    // Only WithInv has an invariant definition
    let with_inv_def = trust_wp_core::type_invariant_def! {
        type_name: "WithInv".to_string(),
        self_param: "self".to_string(),
        param_sort: None, // Int
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    let with_inv_method = type_invariant_method_name("WithInv");

    // --- Case 1: Correct injection (only WithInv gets clauses) ---
    // requires: a.__trust_wp_invariant_WithInv()  (auto-injected for WithInv param)
    // ensures: result.__trust_wp_invariant_WithInv()  (auto-injected for WithInv return)
    // body: result = a
    let req_a_inv = method_call(var("a"), &with_inv_method, vec![]);
    let ens_result_inv = method_call(var("result"), &with_inv_method, vec![]);
    let body = var("a");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_a_inv], std::slice::from_ref(&ens_result_inv))
            .return_expr(Some(&body))
            .type_invariants(Some(std::slice::from_ref(&with_inv_def))),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "With only WithInv injection, identity function should verify: {result:?}"
    );

    // --- Case 2: b has NO invariant injection (PlainType is unconstrained) ---
    // Verify that b does NOT contribute to invariant reasoning.
    // body: result = b (PlainType, no invariant)
    // ensures: result.__trust_wp_invariant_WithInv()
    // This should FAIL because b has no invariant axiom connection to WithInv.
    let body_b = var("b");

    let result_b = verify_function_with_modes(
        VerificationRequest::new(
            &[], // No invariant precondition for b (correct per #659)
            &[ens_result_inv],
        )
        .return_expr(Some(&body_b))
        .type_invariants(Some(std::slice::from_ref(&with_inv_def))),
    );
    assert!(
        crate::tests::rejected_ok(&result_b),
        "PlainType b has no invariant — returning b should produce Failed (invariant() is \
         uninterpreted UF, solver finds counterexample): {result_b:?}"
    );
}
