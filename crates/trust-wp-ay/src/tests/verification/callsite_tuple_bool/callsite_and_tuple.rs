// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================================================================
// Call-site precondition obligation tests (#478)
// ============================================================================

/// Simulate the Hoare-logic call rule: a caller that satisfies the callee's
/// precondition should verify when the callee obligation is added to ensures.
///
/// Models:
///   callee: requires(n > 0), ensures(result == n + 1)
///   caller: requires(x > 5), ensures(result > x), body: callee(x)
///
/// The call-site obligation `x > 0` (callee's requires substituted with
/// actual arg `x`) is added to the caller's ensures. The caller's
/// precondition `x > 5` implies `x > 0`, so this verifies.
#[test]
#[timeout(30000)]
fn test_call_site_obligation_satisfied() {
    // Caller requires: x > 5
    let caller_req = gt(var("x"), int(5));

    // Caller body: result = x + 1 (inlined callee postcondition)
    let body = add(var("x"), int(1));

    // Caller ensures: result > x
    let caller_ens = gt(var("result"), var("x"));

    // Call-site obligation: x > 0 (callee's requires, substituted)
    let call_obligation = gt(var("x"), int(0));

    // Both the caller's postcondition AND the callee's precondition must hold
    let result = verify_function_with_modes(
        VerificationRequest::new(&[caller_req], &[caller_ens, call_obligation])
            .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Caller satisfies callee precondition (x > 5 implies x > 0): {result:?}"
    );
}

/// Simulate the Hoare-logic call rule: a caller that does NOT satisfy the
/// callee's precondition should fail verification.
///
/// Models:
///   callee: requires(n > 100), ensures(result == n + 1)
///   caller: requires(x > 0), ensures(result > x), body: callee(x)
///
/// The call-site obligation `x > 100` cannot be proven from `x > 0`.
/// This is the soundness gap described in #478 — previously, the callee's
/// postcondition would be assumed without checking the precondition.
#[test]
#[timeout(30000)]
fn test_call_site_obligation_unsatisfied() {
    // Caller requires: x > 0 (too weak to imply callee's requires)
    let caller_req = gt(var("x"), int(0));

    // Caller body: result = x + 1 (inlined callee postcondition)
    let body = add(var("x"), int(1));

    // Caller ensures: result > x (this alone would verify)
    let caller_ens = gt(var("result"), var("x"));

    // Call-site obligation: x > 100 (callee's requires, substituted)
    // This CANNOT be proven from the caller's requires (x > 0)
    let call_obligation = gt(var("x"), int(100));

    // Verification should FAIL because the callee's precondition is not satisfied
    let result = verify_function_with_modes(
        VerificationRequest::new(&[caller_req], &[caller_ens, call_obligation])
            .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "Caller does NOT satisfy callee precondition (x > 0 does not imply x > 100): {result:?}"
    );
}

/// Call-chain composition test: callee with no precondition (#799).
///
/// Models:
///   callee: ensures(result > 5)  [no requires]
///   caller: requires(true), ensures(result >= 0), body: callee()
///
/// The caller uses the callee's postcondition (result > 5) as an assumption.
/// Since the callee has no precondition, there is no call-site obligation.
/// The caller proves a weaker property (result >= 0) from the callee's
/// stronger guarantee (result > 5), testing non-trivial composition.
#[test]
#[timeout(30000)]
fn test_call_chain_callee_no_precondition() {
    // Callee postcondition assumed after the call: result > 5
    let callee_post = gt(var("result"), int(5));

    // Caller postcondition: result >= 0 (weaker, follows from result > 5)
    let caller_ens = ge(var("result"), int(0));

    // Caller body: result = call_result (modeled as callee postcondition assumption)
    // No body expression — postcondition follows from callee's guarantees.
    // We model this by adding the callee postcondition as a requires (assumption).
    let result =
        verify_function_with_modes(VerificationRequest::new(&[callee_post], &[caller_ens]));
    let vr = result.expect("callsite encoding should not error");
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "Caller should strictly verify result>=0 from callee guarantee result>5: {vr:?}"
    );
}

/// Test that tuple constructor/destructor axioms enable verification of
/// tuple field access postconditions.
///
/// Scenario: `fn f(x: i32, y: i32) -> (i32, i32) { (x, y) }`
/// with `ensures(result.0 == x && result.1 == y)`.
///
/// Without tuple axioms, `__trust_wp_tuple_get_0(__trust_wp_tuple2(x, y))` is
/// uninterpreted and verification fails. With axioms, the solver knows
/// `get_0(tuple2(x, y)) = x` and verification succeeds.
///
/// Regression test for #509.
#[test]
#[timeout(30000)]
fn test_tuple_field_access_axiom() {
    use trust_wp_core::formula::internal::tuple_lowering::{
        tuple_field_logic_fn_name, tuple_logic_fn_name,
    };

    // body: result = __trust_wp_tuple2(x, y)
    let body = logic_fn_call(&tuple_logic_fn_name(2), vec![var("x"), var("y")]);

    // ensures: __trust_wp_tuple_get_0(result) == x
    let ens_field0 = eq(
        logic_fn_call(&tuple_field_logic_fn_name(0), vec![var("result")]),
        var("x"),
    );

    // ensures: __trust_wp_tuple_get_1(result) == y
    let ens_field1 = eq(
        logic_fn_call(&tuple_field_logic_fn_name(1), vec![var("result")]),
        var("y"),
    );

    // With tuple axioms, both postconditions should verify
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens_field0, ens_field1]).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Tuple field access should verify with constructor/destructor axioms (#509): {result:?}"
    );
}

/// Test that tuple axioms work correctly for 3-element tuples.
///
/// Scenario: `fn f(a: i32, b: i32, c: i32) -> (i32, i32, i32) { (a, b, c) }`
/// with `ensures(result.1 == b)`.
///
/// Regression test for #509.
#[test]
#[timeout(30000)]
fn test_tuple3_field_access_axiom() {
    use trust_wp_core::formula::internal::tuple_lowering::{
        tuple_field_logic_fn_name, tuple_logic_fn_name,
    };

    // body: result = __trust_wp_tuple3(a, b, c)
    let body = logic_fn_call(&tuple_logic_fn_name(3), vec![var("a"), var("b"), var("c")]);

    // ensures: __trust_wp_tuple_get_1(result) == b
    let ens = eq(
        logic_fn_call(&tuple_field_logic_fn_name(1), vec![var("result")]),
        var("b"),
    );

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)));
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "3-tuple field access should verify with axioms (#509): {result:?}"
    );
}

// ============================================================================
// N-ary AND semantic equivalence tests (#506)
//
// Validates that verify_function with multiple ensures clauses (which uses
// and_many internally) produces identical results to a single combined
// ensures clause built from a binary AND tree.
//
// Per SMT-LIB2 §3.6.1, (and e0 e1 e2) ≡ (and (and e0 e1) e2) — these tests
// verify this equivalence holds through the full ay encoding pipeline.
// ============================================================================

/// Three independent postconditions: result > x, result > 0, result <= x + 5.
/// Body: result = x + 1, requires: x > 0.
/// All three hold → Verified. Tests n-ary AND in the positive case.
#[test]
#[timeout(30000)]
fn test_nary_and_equivalence_positive() {
    let req = gt(var("x"), int(0));
    let body = add(var("x"), int(1));
    // ens1: result > x
    let ens1 = gt(var("result"), var("x"));
    // ens2: result > 0
    let ens2 = gt(var("result"), int(0));
    // ens3: result <= x + 5 (equiv: result < x + 6, but use Le for solver stability)
    let ens3 = le(var("result"), add(var("x"), int(5)));

    // Method A: three separate ensures (uses and_many internally)
    let result_nary = verify_function_with_modes(
        VerificationRequest::new(
            std::slice::from_ref(&req),
            &[ens1.clone(), ens2.clone(), ens3.clone()],
        )
        .return_expr(Some(&body)),
    );
    assert!(
        matches!(result_nary, Ok(VerificationResult::Verified(_))),
        "N-ary AND with 3 ensures should verify: {result_nary:?}"
    );

    // Method B: single combined ensures using binary AND tree
    let combined = and(and(ens1, ens2), ens3);
    let result_binary = verify_function_with_modes(
        VerificationRequest::new(std::slice::from_ref(&req), &[combined]).return_expr(Some(&body)),
    );
    assert!(
        matches!(result_binary, Ok(VerificationResult::Verified(_))),
        "Binary AND tree with combined ensures should also verify: {result_binary:?}"
    );
}

/// Three postconditions where the third is unsatisfiable: result > x, result > 0, result < 0.
/// Body: result = x + 1, requires: x > 0.
/// The third ensures fails → Failed. Tests n-ary AND in the negative case.
#[test]
#[timeout(30000)]
fn test_nary_and_equivalence_negative() {
    let req = gt(var("x"), int(0));
    let body = add(var("x"), int(1));
    // ens1: result > x (true)
    let ens1 = gt(var("result"), var("x"));
    // ens2: result > 0 (true)
    let ens2 = gt(var("result"), int(0));
    // ens3: result < 0 (FALSE — contradicts body x+1 with x > 0)
    let ens3 = lt(var("result"), int(0));

    // Method A: three separate ensures (uses and_many internally)
    let result_nary = verify_function_with_modes(
        VerificationRequest::new(
            std::slice::from_ref(&req),
            &[ens1.clone(), ens2.clone(), ens3.clone()],
        )
        .return_expr(Some(&body)),
    );
    assert!(
        matches!(result_nary, Ok(VerificationResult::Failed(_))),
        "N-ary AND with unsatisfiable ensures should fail: {result_nary:?}"
    );

    // Method B: single combined ensures using binary AND tree
    let combined = and(and(ens1, ens2), ens3);
    let result_binary = verify_function_with_modes(
        VerificationRequest::new(std::slice::from_ref(&req), &[combined]).return_expr(Some(&body)),
    );
    assert!(
        matches!(result_binary, Ok(VerificationResult::Failed(_))),
        "Binary AND tree with unsatisfiable ensures should also fail: {result_binary:?}"
    );
}

/// Four postconditions — tests that arity > 3 also works correctly and that
/// the n-ary AND encoding is equivalent to a nested binary AND tree.
/// Body: result = a + b, requires: a > 0 ∧ b > 0.
/// ens1: result > a, ens2: result > b, ens3: result > 0, ens4: result == a + b.
#[test]
#[timeout(30000)]
fn test_nary_and_equivalence_four_ensures() {
    let req_a = gt(var("a"), int(0));
    let req_b = gt(var("b"), int(0));
    let body = add(var("a"), var("b"));

    let ens1 = gt(var("result"), var("a"));
    let ens2 = gt(var("result"), var("b"));
    let ens3 = gt(var("result"), int(0));
    let ens4 = eq(var("result"), add(var("a"), var("b")));

    // Method A: four separate ensures (uses and_many internally)
    let result_nary = verify_function_with_modes(
        VerificationRequest::new(
            &[req_a.clone(), req_b.clone()],
            &[ens1.clone(), ens2.clone(), ens3.clone(), ens4.clone()],
        )
        .return_expr(Some(&body)),
    );
    assert!(
        matches!(result_nary, Ok(VerificationResult::Verified(_))),
        "N-ary AND with 4 ensures should verify: {result_nary:?}"
    );

    // Method B: single combined ensures using nested binary AND tree
    // ((ens1 ∧ ens2) ∧ ens3) ∧ ens4
    let combined = and(and(and(ens1, ens2), ens3), ens4);
    let result_binary = verify_function_with_modes(
        VerificationRequest::new(&[req_a, req_b], &[combined]).return_expr(Some(&body)),
    );
    assert!(
        matches!(result_binary, Ok(VerificationResult::Verified(_))),
        "Binary AND tree with 4 combined ensures should also verify: {result_binary:?}"
    );
}

/// Four postconditions where the fourth is unsatisfiable — tests that arity > 3
/// negative cases also produce identical results through both encodings.
/// Body: result = a + b, requires: a > 0 ∧ b > 0.
/// ens1: result > a, ens2: result > b, ens3: result > 0, ens4: result < 0 (FALSE).
#[test]
#[timeout(30000)]
fn test_nary_and_equivalence_four_ensures_negative() {
    let req_a = gt(var("a"), int(0));
    let req_b = gt(var("b"), int(0));
    let body = add(var("a"), var("b"));

    // ens1: result > a (true)
    let ens1 = gt(var("result"), var("a"));
    // ens2: result > b (true)
    let ens2 = gt(var("result"), var("b"));
    // ens3: result > 0 (true)
    let ens3 = gt(var("result"), int(0));
    // ens4: result < 0 (FALSE — contradicts body a+b with a > 0, b > 0)
    let ens4 = lt(var("result"), int(0));

    // Method A: four separate ensures (uses and_many internally)
    let result_nary = verify_function_with_modes(
        VerificationRequest::new(
            &[req_a.clone(), req_b.clone()],
            &[ens1.clone(), ens2.clone(), ens3.clone(), ens4.clone()],
        )
        .return_expr(Some(&body)),
    );
    assert!(
        matches!(result_nary, Ok(VerificationResult::Failed(_))),
        "N-ary AND with unsatisfiable 4th ensure should fail: {result_nary:?}"
    );

    // Method B: single combined ensures using nested binary AND tree
    // ((ens1 ∧ ens2) ∧ ens3) ∧ ens4
    let combined = and(and(and(ens1, ens2), ens3), ens4);
    let result_binary = verify_function_with_modes(
        VerificationRequest::new(&[req_a, req_b], &[combined]).return_expr(Some(&body)),
    );
    assert!(
        matches!(result_binary, Ok(VerificationResult::Failed(_))),
        "Binary AND tree with unsatisfiable 4th ensure should also fail: {result_binary:?}"
    );
}

/// Test that without the constructor in scope, tuple field access is uninterpreted
/// and a strong postcondition fails (sanity check).
///
/// Scenario: `fn f(x: i32) -> i32 { ... }` where result is opaque,
/// postcondition: `__trust_wp_tuple_get_0(result) == x` — this should NOT verify
/// because there's no constructor to connect the accessor to.
#[test]
#[timeout(30000)]
fn test_tuple_field_access_without_constructor_fails() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

    // No body — result is unconstrained
    // ensures: __trust_wp_tuple_get_0(result) == x
    let ens = eq(
        logic_fn_call(&tuple_field_logic_fn_name(0), vec![var("result")]),
        var("x"),
    );

    let result = verify_function_with_modes(VerificationRequest::new(&[], &[ens]));
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "Tuple field access without constructor should be uninterpreted and fail: {result:?}"
    );
}

/// Test `verify_function` with a Bool-returning body. (#544 Phase 1)
///
/// Scenario: `fn is_positive(x: i32) -> bool { x > 0 }`
/// requires: true (no precondition)
/// ensures: result == (x > 0)
/// body: x > 0
///
/// The `result` variable must be declared with `Sort::Bool` (not `Sort::Int`)
/// for the equality `result == (x > 0)` to be well-sorted. Before this fix,
/// result was hardcoded to `Sort::Int`, causing a ay panic on `mk_eq(Int, Bool)`.
#[test]
#[timeout(30000)]
fn test_verify_bool_returning_function() {
    // body: x > 0 (returns Bool)
    let body = gt(var("x"), int(0));

    // ensures: result == (x > 0)
    let ens = eq(var("result"), gt(var("x"), int(0)));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Bool-returning function should verify: {result:?}"
    );
}

/// Negative test: Bool-returning function with wrong postcondition. (#544 Phase 1)
///
/// Scenario: `fn is_positive(x: i32) -> bool { x > 0 }`
/// ensures: result == (x < 0)  — wrong
///
/// Should fail with counterexample.
#[test]
#[timeout(30000)]
fn test_verify_bool_returning_function_wrong_post() {
    // body: x > 0 (returns Bool)
    let body = gt(var("x"), int(0));

    // ensures: result == (x < 0) — wrong
    let ens = eq(var("result"), lt(var("x"), int(0)));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Bool-returning function with wrong post should fail: {result:?}"
    );
}

/// Regression: bool result aliases (`result = _call_0`) must stay Bool-sorted (#544).
///
/// Creusot compatibility tests can extract the return expression as a temporary
/// variable (`_call_0`). If postconditions require `result` to be Bool
/// (`result == true`), both `result` and `_call_0` must be declared Bool.
#[test]
#[timeout(30000)]
fn test_verify_bool_result_alias_var() {
    // return_expr extracted as a temporary variable alias
    let body = var("_call_0");

    // ensures: result == true
    let ens = eq(var("result"), bool_expr(true));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Bool result alias should not panic and should produce a counterexample: {result:?}"
    );
}

/// Regression: bool result aliases should remain stable when logic functions are
/// in scope (driver-like path that registers logic signatures before verification).
#[test]
#[timeout(30000)]
fn test_verify_bool_result_alias_var_with_logic_scope() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let body = var("_call_0");
    let ens = eq(var("result"), bool_expr(true));

    let logic_fn = LogicFnDef::new(
        "id_bool".to_string(),
        "test::id_bool".to_string(),
        vec!["b".to_string()],
        var("b"),
    )
    .with_mode(LogicMode::Open);

    let logic_fns = [logic_fn];
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .logic_fns(Some(&logic_fns)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Bool result alias with logic scope should not panic: {result:?}"
    );
}

/// Regression (#816): bool-returning call result with ExprSort::Bool annotation
/// must not ICE with `mk_eq expects same sort, got Int = Bool`.
///
/// Scenario: `id_bool(flag)` returns bool, return_expr is `Var("call_0", Bool)`.
/// Without proper sort propagation, `result` is declared Int while `call_0`
/// encodes as Bool, causing a ay sort mismatch panic.
#[test]
#[timeout(30000)]
fn test_verify_bool_call_result_with_expr_sort_annotation_816() {
    use crate::ExprSort;

    // return_expr: call_0 with explicit Bool sort annotation (from MIR type info)
    let body = var_with_sort("call_0", ExprSort::Bool);

    // ensures: result (bare Bool postcondition, as proof_assert generates)
    let ens = var("result");

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .unwrap();
    // Postcondition `result` means "result == true" (bare Bool predicate).
    // No precondition guarantees call_0 is true, so solver finds counterexample
    // where call_0 = false → result = false, violating the postcondition.
    // The key assertion: this must not panic with sort mismatch (#816).
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Bool call result with bare `result` postcondition should fail \
         (no guarantee call_0 is true) (#816): {result:?}"
    );
}

/// Regression (#816): bool call result WITHOUT ExprSort annotation should still
/// be detected as Bool via postcondition analysis (defense in depth).
#[test]
#[timeout(30000)]
fn test_verify_bool_call_result_no_annotation_postcond_detection_816() {
    // return_expr: call_0 with no sort annotation (legacy path)
    let body = var("call_0");

    // ensures: result == true (explicit Bool postcondition)
    let ens = eq(var("result"), bool_expr(true));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Bool call result detected via postcondition should not panic (#816): {result:?}"
    );
}

/// Regression (#1277/#1332): when postconditions do not mention `result`,
/// verification should not force a `result = return_expr` bridge.
///
/// This pattern appears in proof_assert verification: the body marker helps
/// extraction, but obligations are expressed over local symbols. If `return_expr`
/// is a bare variable that is Bool-hinted by other postconditions, forcing
/// `result = return_expr` can create an Int=Bool sort mismatch.
#[test]
#[timeout(30000)]
fn test_verify_unused_result_bridge_skipped_for_bool_hinted_alias() {
    // Bare alias defaults to Int by syntax.
    let body = var("call_0");
    // Bool context for call_0, but no `result` usage in postconditions.
    let ens = var("call_0");

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Unused result bridge should be skipped; this should fail normally without sort panic: {result:?}"
    );
}

/// Regression: equality against `seq![...]` literals should not trigger
/// sort-mismatch panics during postcondition encoding.
#[test]
#[timeout(30000)]
fn test_verify_seq_literal_postcondition_no_sort_panic() {
    let req = eq(
        view(var("a")),
        logic_fn_call("seq", vec![int(0), int(0), int(0), int(0)]),
    );

    let ens = eq(
        view(final_expr(var("a"))),
        logic_fn_call("seq", vec![int(0), int(1), int(1), int(0)]),
    );

    let mut encoder = crate::encoder::AYEncoder::new();
    encoder.register_sort_hints(&[req.clone(), ens.clone()]);
    for expr in [&req, &ens] {
        let term = encoder
            .encode_pure(expr)
            .expect("Seq-literal equality should encode structurally");
        assert_eq!(
            encoder.solver().get_sort(term),
            ay_dpll::api::Sort::Bool,
            "Seq-literal equality must remain Bool-sorted"
        );
    }

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).timeout(Some(std::time::Duration::from_secs(5))),
    );
    assert!(
        result.is_ok(),
        "Seq literal postcondition should encode without sort panic: {result:?}"
    );
    // No body provided, so final(a)@ == seq(0,1,1,0) is unconstrained.
    let vr = result.unwrap();
    assert!(
        matches!(
            vr,
            VerificationResult::Failed(_)
                | VerificationResult::Unknown(crate::verify::UnknownReason::Timeout)
        ),
        "unconstrained Seq-literal postcondition must remain a non-proof: {vr:?}"
    );
}

/// Regression for #2230: even though Seq receiver `index_logic` now records the
/// LOW-risk method-call fallback, a Bool-postcondition path must never silently
/// produce `Verified`. trust-wp's Seq backend is still Int-valued, so this case
/// should fail or go Unknown until Bool-element sequences are modeled explicitly.
#[test]
#[timeout(30000)]
fn test_verify_seq_index_logic_bool_postcondition_not_verified_2230() {
    let body = method_call(view(var("s")), "index_logic", vec![int(0)]);
    let ens = var("result");

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)));
    assert!(
        result.is_ok(),
        "Seq index_logic Bool postcondition should not hard-error: {result:?}"
    );

    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Failed(_)),
        "Seq index_logic Bool postcondition must fail, not silently verify: {vr:?}"
    );
}
