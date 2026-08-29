// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure verification regression tests (#568).
//!
//! Extracted from `verification.rs` to reduce file size and ownership collisions (#772).
//! These tests simulate the PureExpr contracts that the driver generates for
//! closure verification, exercising the full verify_function/verify_mut_borrow_function
//! path at the ay level without needing the slow e2e pipeline.

use std::collections::HashMap;

use ntest::timeout;

use super::{super::*, helpers::*};

// ============================================================================
// Closure verification regression tests (#568)
//
// These tests simulate the PureExpr contracts that the driver generates for
// closure verification, exercising the full verify_function/verify_mut_borrow_function
// path at the ay level without needing the slow e2e pipeline.
// ============================================================================

/// Regression: closure `move_closure_positive` — `result == y` on `move || y`.
///
/// The driver generates:
///   ensures: Eq(Var("result"), Var("y"))
///   `return_expr`: Var("y")
///
/// This is the simplest possible closure contract and should verify instantly.
/// Timeout here indicates a fundamental encoder regression. (#568)
#[test]
#[timeout(5000)]
fn test_closure_move_positive_no_timeout() {
    let ens = eq(var("result"), var("y"));
    let body = var("y");

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)));
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Simple closure result == y should verify: {result:?}"
    );
}

/// Regression: closure `Fn::call` postcondition through `verify_function`.
///
/// Simulates `call_fn_twice_verified`:
///   requires: (*f).precondition(x)  — `MethodCall`
///   ensures: (*f).postcondition(x, result)  — `MethodCall`
///   `call_assumptions`: `(*f).postcondition(x, _call_0)`, `(*f).postcondition(x, _call_1)`
///   `return_expr`: `Var("_call_1")`
///
/// The `call_assumptions` become additional requires. Synthesized identity
/// final values route this through `verify_mut_borrow_function`. (#568)
#[test]
#[timeout(30000)]
fn test_closure_fn_call_twice_no_timeout() {
    let deref_f = deref(var("f"));

    // User requires: (*f).precondition(x)
    let user_req = method_call(deref_f.clone(), "precondition", vec![var("x")]);

    // Call assumptions from two Fn::call invocations
    let assumption_0 = method_call(
        deref_f.clone(),
        "postcondition",
        vec![var("x"), var("_call_0")],
    );
    let assumption_1 = method_call(
        deref_f.clone(),
        "postcondition",
        vec![var("x"), var("_call_1")],
    );

    // effective_requires = user_req + assumptions + bridged assumptions (result = _call_1)
    let bridged_assumption = method_call(
        deref_f.clone(),
        "postcondition",
        vec![var("x"), var("result")],
    );
    let all_requires = vec![user_req, assumption_0, assumption_1, bridged_assumption];

    // User ensures: (*f).postcondition(x, result)
    let user_ens = method_call(
        deref_f.clone(),
        "postcondition",
        vec![var("x"), var("result")],
    );

    // Call obligations: precondition(x) for each call
    let obligation_0 = method_call(deref_f, "precondition", vec![var("x")]);
    let all_ensures = vec![user_ens, obligation_0.clone(), obligation_0];

    let body = var("_call_1");

    // Synthesized identity final values for Fn closure: f_final = f
    let mut synth_fv = HashMap::new();
    synth_fv.insert("f".to_string(), var("f"));

    // This goes through verify_mut_borrow_function due to synthesized final values
    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&all_requires, &all_ensures, &synth_fv).return_expr(Some(&body)),
    );
    assert!(
        result.is_ok(),
        "Closure Fn::call twice should not timeout or error: {result:?}"
    );
    // The postcondition is an assumption (it's in requires too), so this should verify
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "Closure Fn::call twice should verify (postcondition is an assumption): {vr:?}"
    );
}

/// Regression: closure Fn→FnMut weakening — exact reproduction from driver output. (#568)
///
/// Reproduces the exact `PureExpr` structures from the driver for `weaken_fn_to_fn_mut`:
///   `requires[0]: MethodCall { receiver: Deref(Var("f")), method: "precondition", args: [Var("x")] }`
///   `requires[1]: MethodCall { receiver: Deref(Var("f")), method: "postcondition", args: [Var("x"), Var("call_0")] }`
///   `requires[2]: MethodCall { receiver: Deref(Var("f")), method: "postcondition", args: [Var("x"), Var("result")] }`
///   `ensures[0]: MethodCall { receiver: Deref(Var("f")), method: "postcondition_mut", args: [Var("x"), Final(Var("f")), Var("result")] }`
///   `ensures[1]: MethodCall { receiver: Deref(Var("f")), method: "precondition", args: [Var("x")] }`
///   `final_values: {"f": Var("f")}`
///   `return_expr: Some(Var("call_0"))`
///
/// The `fn_mut` law axiom connects postcondition to `postcondition_mut`.
/// Timeout here means ay E-matching loop on the closure law axioms.
#[test]
#[timeout(30000)]
fn test_closure_fn_to_fnmut_weakening_no_timeout() {
    let deref_f = deref(var("f"));

    // requires[0]: (*f).precondition(x)
    let req_0 = method_call(deref_f.clone(), "precondition", vec![var("x")]);

    // requires[1]: (*f).postcondition(x, call_0) — Fn::call assumption
    let req_1 = method_call(
        deref_f.clone(),
        "postcondition",
        vec![var("x"), var("call_0")],
    );

    // requires[2]: (*f).postcondition(x, result) — bridged assumption
    let req_2 = method_call(
        deref_f.clone(),
        "postcondition",
        vec![var("x"), var("result")],
    );

    let all_requires = vec![req_0, req_1, req_2];

    // ensures[0]: (*f).postcondition_mut(x, ^f, result)
    let ens_0 = method_call(
        deref_f.clone(),
        "postcondition_mut",
        vec![var("x"), final_expr(var("f")), var("result")],
    );

    // ensures[1]: (*f).precondition(x) — call obligation
    let ens_1 = method_call(deref_f, "precondition", vec![var("x")]);

    let all_ensures = vec![ens_0, ens_1];

    let body = var("call_0");

    // Synthesized identity final values: f -> Var("f")
    let mut final_values = HashMap::new();
    final_values.insert("f".to_string(), var("f"));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&all_requires, &all_ensures, &final_values).return_expr(Some(&body)),
    );
    assert!(
        result.is_ok(),
        "Fn→FnMut weakening should not timeout or error: {result:?}"
    );
    // Strengthened from is_ok() per Prover P11 audit: the bridged assumption makes
    // this trivially UNSAT, so the result must be Verified, not just Ok.
    assert!(
        matches!(result.as_ref().unwrap(), VerificationResult::Verified(_)),
        "Trivially-UNSAT closure should be Verified, not just Ok: {result:?}"
    );
}

/// Non-trivial UNSAT closure regression for #568.
///
/// Unlike the simpler weakening tests, this one does NOT include a bridged
/// assumption `postcondition(f, x, result)` in requires. The solver must use:
/// 1) body aliasing (`result = call_0`)
/// 2) the Fn law assumption `postcondition(f, x, call_0)`
/// 3) synthesized identity final values (`^f = f`)
/// 4) the `fn_mut` law axiom
///
/// to prove `postcondition_mut(f, x, ^f, result)`. This keeps the VC UNSAT for
/// a non-trivial reason and catches closure-law E-matching regressions.
#[test]
#[timeout(30000)]
fn test_closure_fn_to_fnmut_nontrivial_unsat_no_timeout() {
    let deref_f = deref(var("f"));

    // requires[0]: (*f).precondition(x)
    let req_0 = method_call(deref_f.clone(), "precondition", vec![var("x")]);

    // requires[1]: (*f).postcondition(x, call_0) — only call-site assumption.
    // Intentionally no bridged `postcondition(x, result)` requirement.
    let req_1 = method_call(
        deref_f.clone(),
        "postcondition",
        vec![var("x"), var("call_0")],
    );
    let all_requires = vec![req_0, req_1];

    // ensures[0]: (*f).postcondition_mut(x, ^f, result)
    let ens_0 = method_call(
        deref_f.clone(),
        "postcondition_mut",
        vec![var("x"), final_expr(var("f")), var("result")],
    );

    // ensures[1]: (*f).precondition(x) — call obligation
    let ens_1 = method_call(deref_f, "precondition", vec![var("x")]);
    let all_ensures = vec![ens_0, ens_1];

    // return expression from the closure call path
    let body = var("call_0");

    // Synthesized identity final values for Fn closure: f_final = f
    let mut final_values = HashMap::new();
    final_values.insert("f".to_string(), var("f"));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&all_requires, &all_ensures, &final_values).return_expr(Some(&body)),
    );
    assert!(
        result.is_ok(),
        "Non-trivial Fn→FnMut weakening should not timeout or error: {result:?}"
    );
    assert!(
        matches!(result.as_ref().unwrap(), VerificationResult::Verified(_)),
        "Expected verification via body alias + fn_mut law, not bridged assumption: {result:?}"
    );
}

/// Diagnostic: same as `test_closure_fn_to_fnmut_weakening` but through `verify_function`
/// with explicit f == `f_final` requirement (like the passing `test_fn_to_fnmut_weakening`).
/// Tests whether the issue is `verify_mut_borrow_function` vs `verify_function` path.
#[test]
#[timeout(30000)]
fn test_closure_fnmut_weakening_via_verify_function() {
    let deref_f = deref(var("f"));

    // Same contracts as the failing test, but expressed through verify_function.
    // requires: precondition(f, x), postcondition(f, x, call_0), postcondition(f, x, result)
    let req_0 = method_call(deref_f.clone(), "precondition", vec![var("x")]);
    let req_1 = method_call(
        deref_f.clone(),
        "postcondition",
        vec![var("x"), var("call_0")],
    );
    let req_2 = method_call(
        deref_f.clone(),
        "postcondition",
        vec![var("x"), var("result")],
    );
    // Also add f == f_final and result == call_0 as explicit requirements
    let req_eq_final = eq(var("f"), var("f_final"));

    let all_requires = vec![req_0, req_1, req_2, req_eq_final];

    // ensures: postcondition_mut(f, x, f_final, result), precondition(f, x)
    let ens_0 = method_call(
        deref_f.clone(),
        "postcondition_mut",
        vec![var("x"), var("f_final"), var("result")],
    );
    let ens_1 = method_call(deref_f, "precondition", vec![var("x")]);

    let all_ensures = vec![ens_0, ens_1];

    // body: call_0 (same as the failing test)
    let body = var("call_0");

    let result = verify_function_with_modes(
        VerificationRequest::new(&all_requires, &all_ensures).return_expr(Some(&body)),
    );
    assert!(
        result.is_ok(),
        "Fn→FnMut weakening via verify_function should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "Should verify via verify_function path: {vr:?}"
    );
}

/// Simulate `call_fn_twice_verified`: Fn closure called twice.
///
/// Effective requires:
///   f.precondition(x)                      — user requires
///   `f.postcondition(x, _call_0)`            — call-site assumption from first `Fn::call`
///   f.postcondition(x, result)             — call-site assumption (bridged) from second `Fn::call`
///
/// Effective ensures:
///   f.postcondition(x, result)             — user ensures
///   f.precondition(x)                      — call-site obligation (from both calls)
///
/// Body result: `Var("_call_1")` — aliased to result via bridging.
///
/// This is trivially UNSAT (assumption matches negated goal), should solve instantly.
/// If this times out, the issue is in the encoder/solver, not the driver.
/// Regression test for #568.
#[test]
#[timeout(30000)]
fn test_verify_fn_call_twice_closure_regression() {
    // User requires: f.precondition(x)
    let user_req = method_call(var("f"), "precondition", vec![var("x")]);

    // Call-site assumption 1: f.postcondition(x, _call_0)
    let call_assumption_1 = method_call(var("f"), "postcondition", vec![var("x"), var("_call_0")]);

    // Call-site assumption 2 (bridged): f.postcondition(x, result)
    let call_assumption_2 = method_call(var("f"), "postcondition", vec![var("x"), var("result")]);

    // User ensures: f.postcondition(x, result)
    let user_ens = method_call(var("f"), "postcondition", vec![var("x"), var("result")]);

    // Call-site obligation: f.precondition(x)
    let call_obligation = method_call(var("f"), "precondition", vec![var("x")]);

    let effective_requires = vec![user_req, call_assumption_1, call_assumption_2];
    let effective_ensures = vec![user_ens, call_obligation];

    // Body result is _call_1 (second call), which is aliased to result
    let body = var("_call_1");

    let result = verify_function_with_modes(
        VerificationRequest::new(&effective_requires, &effective_ensures).return_expr(Some(&body)),
    );
    assert!(result.is_ok(), "Should not error: {result:?}");
    assert!(
        matches!(result.as_ref().unwrap(), VerificationResult::Verified(_)),
        "Fn called twice should verify trivially (assumption = goal): {result:?}"
    );
}

/// Diagnostic: simplified existential postcondition — no axioms needed.
///
/// Given: postcondition_mut(f, a, 42, result) as an assumption
/// Prove: exists<f2> postcondition_mut(f, a, f2, result)
///
/// This tests whether ay can refute `NOT(exists f2. P(f, a, f2, result))`
/// when a ground instance `P(f, a, 42, result)` is available. If this fails,
/// the issue is in ay's existential handling, not in the axiom system.
#[test]
#[timeout(30000)]
fn test_closure_existential_postcondition_ground() {
    // Give the solver a ground postcondition_mut fact as a precondition
    let ground_fact = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), int(42), var("result")],
    );
    let all_requires = vec![ground_fact];

    // Postcondition: exists<f2> f.postcondition_mut(a, f2, result)
    let user_ens = exists(
        "f2",
        method_call(
            var("f"),
            "postcondition_mut",
            vec![var("a"), var("f2"), var("result")],
        ),
    );
    let all_ensures = vec![user_ens];

    let body = var("result");

    let result = verify_function_with_modes(
        VerificationRequest::new(&all_requires, &all_ensures).return_expr(Some(&body)),
    );
    assert!(
        result.is_ok(),
        "Ground existential postcondition should not error: {result:?}"
    );
    let vr = result.unwrap();
    // Vacuity guard (#2414): ground existential preconditions are over-constrained.
    assert_verified_or_vacuous(
        &vr,
        "Existential should be satisfiable from ground instance",
    );
}

/// Diagnostic: existential postcondition via fn_mut_once axiom, no resolve.
///
/// Given: postcondition_once(f, a, result) as assumption
/// Prove: exists<f2> postcondition_mut(f, a, f2, result)
///
/// This tests the axiom chain without the resolve complication. The reverse
/// fn_mut_once law should provide a witness for the existential.
#[test]
#[timeout(30000)]
fn test_closure_existential_via_axiom_no_resolve() {
    // Assumption: postcondition_once(f, a, result) — from call site
    let assumption = method_call(
        var("f"),
        "postcondition_once",
        vec![var("a"), var("result")],
    );
    let all_requires = vec![assumption];

    // Postcondition: exists<f2> postcondition_mut(f, a, f2, result)
    let user_ens = exists(
        "f2",
        method_call(
            var("f"),
            "postcondition_mut",
            vec![var("a"), var("f2"), var("result")],
        ),
    );
    let all_ensures = vec![user_ens];

    let body = var("result");

    let result = verify_function_with_modes(
        VerificationRequest::new(&all_requires, &all_ensures).return_expr(Some(&body)),
    );
    assert!(
        result.is_ok(),
        "Existential via axiom should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "postcondition_once assumption + reverse axiom should prove existential: {vr:?}"
    );
}

/// Regression: `weaken_2_std` — FnMut postcondition with existential witness.
///
/// Reproduces the exact failing test from `closures/06_fn_specs.rs:weaken_2_std`:
///   requires: f.precondition(a)
///   call-site assumption: f.postcondition_once(a, call_0), f.postcondition_once(a, result) [bridged]
///   ensures: exists<f2: F> f.postcondition_mut(a, f2, result) && resolve(f2)
///   call obligation: f.precondition(a)
///   return_expr: call_0
///
/// The proof requires:
/// 1. The reverse fn_mut_once law fires on postcondition_once(f, a, result), giving
///    postcondition_mut(f, a, witness(f, a, result), result)
/// 2. The existential in the postcondition is instantiated with f2 = witness(...)
/// 3. resolve(f2) on a quantifier-bound variable collapses to true
///
/// Part of #970 (closure specification encoding, Step 2).
#[test]
#[timeout(30000)]
fn test_closure_fnmut_existential_postcondition() {
    let deref_f = deref(var("f"));

    // User requires: f.precondition(a)
    let user_req = method_call(deref_f.clone(), "precondition", vec![var("a")]);

    // Call-site assumptions from calling weaken_3_std which ensures postcondition_once
    let call_assumption_raw = method_call(
        var("f"),
        "postcondition_once",
        vec![var("a"), var("call_0")],
    );
    let call_assumption_bridged = method_call(
        var("f"),
        "postcondition_once",
        vec![var("a"), var("result")],
    );
    let all_requires = vec![user_req, call_assumption_raw, call_assumption_bridged];

    // User ensures: exists<f2> f.postcondition_mut(a, f2, result) && resolve(f2)
    let user_ens = exists(
        "f2",
        and(
            method_call(
                var("f"),
                "postcondition_mut",
                vec![var("a"), var("f2"), var("result")],
            ),
            resolve_call(var("f2")),
        ),
    );
    // Call obligation: f.precondition(a) (from weaken_3_std's requires)
    let call_obligation = method_call(deref_f, "precondition", vec![var("a")]);
    let all_ensures = vec![user_ens, call_obligation];

    let body = var("call_0");

    let result = verify_function_with_modes(
        VerificationRequest::new(&all_requires, &all_ensures).return_expr(Some(&body)),
    );
    assert!(
        result.is_ok(),
        "FnMut existential postcondition should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "weaken_2_std should verify via fn_mut_once law + existential: {vr:?}"
    );
}

/// Reproduces the `closures/06_fn_specs.rs:weaken_std` scenario:
///   requires: f.precondition(a)
///   call-site assumption: exists<f2> f.postcondition_mut(a, f2, result) && resolve(f2)
///     (from calling weaken_2_std which ensures this existential)
///   ensures: f.postcondition(a, result)
///
/// The proof requires:
/// 1. Skolemize the existential assumption to get a ground
///    postcondition_mut(f, a, sk_f2, result) term.
/// 2. The fn_mut law fires on postcondition_mut(...), giving
///    postcondition(f, a, result) && f == sk_f2.
/// 3. postcondition(f, a, result) follows directly.
///
/// ay-dpll cannot Skolemize existentials (ay#813), so trust-wp-level
/// eager Skolemization is required (#970).
///
/// Part of #970 (closure specification encoding, Step 2).
#[test]
#[timeout(30000)]
fn test_closure_fn_postcondition_from_existential_assumption() {
    let deref_f = deref(var("f"));

    // User requires: f.precondition(a)
    let user_req = method_call(deref_f, "precondition", vec![var("a")]);

    // Call-site assumption from weaken_2_std's postcondition:
    // exists<f2> f.postcondition_mut(a, f2, result) && resolve(f2)
    let existential_assumption = exists(
        "f2",
        and(
            method_call(
                var("f"),
                "postcondition_mut",
                vec![var("a"), var("f2"), var("result")],
            ),
            resolve_call(var("f2")),
        ),
    );

    let all_requires = vec![user_req, existential_assumption];

    // User ensures: f.postcondition(a, result)
    let user_ens = method_call(var("f"), "postcondition", vec![var("a"), var("result")]);
    let all_ensures = vec![user_ens];

    let body = var("call_0");

    let result = verify_function_with_modes(
        VerificationRequest::new(&all_requires, &all_ensures).return_expr(Some(&body)),
    );
    assert!(
        result.is_ok(),
        "Fn postcondition from existential assumption should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "weaken_std should verify via eager Skolemization + fn_mut law: {vr:?}"
    );
}

/// Regression: body-originated existential call assumptions must be
/// Skolemized before closure axioms run.
///
/// This matches the real `weaken_std` pipeline shape more closely than the
/// precondition-only regression above: the existential arrives from a callee
/// ensures clause wrapped in `LetAssume`, not directly in `requires`.
#[test]
#[timeout(30000)]
fn test_closure_fn_postcondition_from_body_existential_assumption() {
    let deref_f = deref(var("f"));

    // User requires: f.precondition(a)
    let user_req = method_call(deref_f, "precondition", vec![var("a")]);

    // Body-local call assumption from weaken_2_std's ensures:
    // exists<f2> f.postcondition_mut(a, f2, call_0) && resolve(f2)
    let existential_assumption = exists(
        "f2",
        and(
            method_call(
                var("f"),
                "postcondition_mut",
                vec![var("a"), var("f2"), var("call_0")],
            ),
            resolve_call(var("f2")),
        ),
    );
    let body = PureExpr::LetAssume {
        assumption: std::sync::Arc::new(existential_assumption),
        body: std::sync::Arc::new(var("call_0")),
    };

    // User ensures: f.postcondition(a, result)
    let user_ens = method_call(var("f"), "postcondition", vec![var("a"), var("result")]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[user_req], &[user_ens]).return_expr(Some(&body)),
    );
    assert!(
        result.is_ok(),
        "Fn postcondition from body existential assumption should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "weaken_std LetAssume existential should verify via eager body Skolemization + fn_mut law: {vr:?}"
    );
}

/// Shared setup for Layer-1 closure sort tests: register a closure struct sort
/// with two captures (Int, Bool) and return the sort and encoder.
fn setup_closure_struct_encoder() -> (AYEncoder, Sort) {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: "crate::closure::mutable_counter#0".to_string(),
                captures: vec![
                    crate::CaptureField::new(
                        "capture_0",
                        crate::ExprSort::Int,
                        CaptureKind::ByValue,
                    ),
                    crate::CaptureField::new(
                        "capture_1",
                        crate::ExprSort::Bool,
                        CaptureKind::ByValue,
                    ),
                ],
            },
        )
        .unwrap();
    (encoder, closure_sort)
}

/// Layer-1: closure sort registration declares constructor and accessor UFs.
/// Re: #1479.
#[test]
#[timeout(30000)]
fn test_closure_struct_sort_declares_ctor_and_accessors() {
    let (mut encoder, closure_sort) = setup_closure_struct_encoder();

    // With native datatypes (#2151), constructor/selectors are declared via
    // try_declare_datatype, not as UF entries in logic_funcs. Verify they
    // work by building a constructor term and extracting fields.
    let x = encoder.solver_mut().int_const(42);
    let b = encoder.solver_mut().bool_const(true);
    let registered = encoder
        .sort_resolver_for_test()
        .closure_struct_sorts_iter()
        .find(|e| e.sort == closure_sort)
        .cloned()
        .expect("closure sort should be registered");
    let ctor_name = format!(
        "mk_closure_env_{}",
        registered
            .datatype
            .name
            .strip_prefix("ClosureEnv_")
            .unwrap()
    );
    let env = encoder
        .solver_mut()
        .try_datatype_constructor(&registered.datatype, &ctor_name, &[x, b])
        .expect("constructor should work");
    let field0 = encoder
        .solver_mut()
        .try_datatype_selector(
            &registered.datatype.constructors[0].fields[0].name,
            env,
            Sort::Int,
        )
        .expect("selector 0 should work");
    let field1 = encoder
        .solver_mut()
        .try_datatype_selector(
            &registered.datatype.constructors[0].fields[1].name,
            env,
            Sort::Bool,
        )
        .expect("selector 1 should work");
    // Verify types are correct (no panic = success).
    assert_eq!(encoder.solver_mut().get_sort(field0), Sort::Int);
    assert_eq!(encoder.solver_mut().get_sort(field1), Sort::Bool);
}

/// Layer-1: postcondition_mut on closure-sorted receiver uses concrete sort
/// tags in SMT symbol name (not generic "i"). Re: #1479.
#[test]
#[timeout(30000)]
fn test_closure_struct_sort_in_spec_symbol_name() {
    let (mut encoder, closure_sort) = setup_closure_struct_encoder();

    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare f with closure sort");
    encoder
        .get_or_declare_var("f2", closure_sort)
        .expect("declare f2 with closure sort");

    let post_mut = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("arg"), var("f2"), var("result")],
    );
    encoder
        .encode_pure(&post_mut)
        .expect("postcondition_mut should encode with closure sort");

    let symbols: Vec<String> = encoder
        .decls()
        .logic_func_names()
        .filter(|n| n.starts_with("closure_postcondition_mut_4_"))
        .cloned()
        .collect();
    assert_eq!(symbols.len(), 1, "expected one postcondition_mut symbol");
    assert!(
        symbols[0].contains("_c"),
        "symbol should contain concrete closure sort tag 'c', got: {}",
        symbols[0]
    );
}

/// Layer-1: constructor/accessor round-trip axioms are UNSAT. Re: #1479.
#[test]
#[timeout(30000)]
fn test_closure_struct_round_trip_axioms() {
    let (mut encoder, closure_sort) = setup_closure_struct_encoder();

    // With native datatypes (#2151), round-trip semantics are built into the
    // datatype definition. Verify selector(constructor(x, b)) == x/b.
    let registered = encoder
        .sort_resolver_for_test()
        .closure_struct_sorts_iter()
        .find(|e| e.sort == closure_sort)
        .cloned()
        .expect("registered");
    let dt = &registered.datatype;
    let ctor_name = &dt.constructors[0].name;
    let sel0 = &dt.constructors[0].fields[0].name;
    let sel1 = &dt.constructors[0].fields[1].name;

    let x = encoder.solver_mut().int_const(41);
    let b = encoder.solver_mut().bool_const(true);
    let env = encoder
        .solver_mut()
        .try_datatype_constructor(dt, ctor_name, &[x, b])
        .expect("ctor");
    let got_x = encoder
        .solver_mut()
        .try_datatype_selector(sel0, env, Sort::Int)
        .expect("sel0");
    let got_b = encoder
        .solver_mut()
        .try_datatype_selector(sel1, env, Sort::Bool)
        .expect("sel1");

    // capture_0(mk_closure_env(x, b)) == x
    let eq_x = encoder.eq_or_iff(got_x, x, &Sort::Int);
    let neq_x = encoder.solver_mut().not(eq_x);
    encoder.solver_mut().push();
    encoder.assert_term(neq_x);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "round-trip capture_0"
    );
    encoder.solver_mut().pop();

    // capture_1(mk_closure_env(x, b)) == b
    let eq_b = encoder.eq_or_iff(got_b, b, &Sort::Bool);
    let neq_b = encoder.solver_mut().not(eq_b);
    encoder.solver_mut().push();
    encoder.assert_term(neq_b);
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "round-trip capture_1"
    );
    encoder.solver_mut().pop();
}

/// Layer-1: re-registering same closure sort is idempotent. Re: #1479.
#[test]
#[timeout(30000)]
fn test_closure_struct_sort_idempotent_registration() {
    let (mut encoder, first_sort) = setup_closure_struct_encoder();
    let decl_count_before = encoder.decls().logic_func_count();

    let second_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: "crate::closure::mutable_counter#0".to_string(),
                captures: vec![
                    crate::CaptureField::new(
                        "capture_0",
                        crate::ExprSort::Int,
                        CaptureKind::ByValue,
                    ),
                    crate::CaptureField::new(
                        "capture_1",
                        crate::ExprSort::Bool,
                        CaptureKind::ByValue,
                    ),
                ],
            },
        )
        .unwrap();
    assert_eq!(second_sort, first_sort, "sort should be identical");
    assert_eq!(
        encoder.decls().logic_func_count(),
        decl_count_before,
        "idempotent registration must not redeclare symbols"
    );
}
