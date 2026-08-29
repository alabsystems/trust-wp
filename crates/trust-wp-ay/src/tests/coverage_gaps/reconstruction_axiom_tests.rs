// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Reconstruction axiom: forall x. is_some(x) ==> Some(unwrap(x)) = x
///
/// Test: declare a variable `opt`, assert is_some(opt) and
/// Some(unwrap(opt)) != opt. Should be UNSAT after axioms.
#[test]
#[timeout(30000)]
fn test_option_some_reconstruction() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Encode is_some(opt)
    let is_some_opt = method_call(var("opt"), "is_some", vec![]);
    let is_some_term = encoder
        .encode_pure(&is_some_opt)
        .expect("opt.is_some() should encode");

    // Encode unwrap(opt) — populates spec_functions for axioms
    let unwrap_opt = method_call(var("opt"), "unwrap", vec![]);
    encoder
        .encode_pure(&unwrap_opt)
        .expect("opt.unwrap() should encode");

    // Encode Some(unwrap(opt))
    let some_of_unwrap = logic_fn_call("Some", vec![unwrap_opt.clone()]);
    let some_unwrap_term = encoder
        .encode_pure(&some_of_unwrap)
        .expect("Some(opt.unwrap()) should encode");

    // Encode opt as a term
    let opt_term = encoder.encode_pure(&var("opt")).unwrap();

    encoder.assert_option_result_axioms();

    // Assert: is_some(opt) AND Some(unwrap(opt)) != opt
    // Use encoder.eq_term (not solver.eq) to get sort coercion between
    // the OptionInt-sorted Some(unwrap(opt)) and Int-sorted opt. (#994)
    let eq = encoder.eq_term(some_unwrap_term, opt_term);
    let reconstruction_fails = {
        let solver = encoder.solver_mut();
        let neq = solver.not(eq);
        solver.and(is_some_term, neq)
    };
    encoder.assert_term(reconstruction_fails);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_some(opt) => Some(unwrap(opt)) == opt must hold (reconstruction axiom)"
    );
}

/// Edge case: nested Option<Option<T>> should compose unwrap axioms correctly.
///
/// Checks both:
/// 1) unwrap(Some(Some(7))) = Some(7)
/// 2) unwrap(unwrap(Some(Some(7)))) = 7
#[test]
#[timeout(30000)]
fn test_option_nested_some_double_unwrap() {
    // Outer unwrap: Some(Some(7)).unwrap() == Some(7)
    {
        let mut encoder = AYEncoder::new_with_quantifiers();

        let nested_some = logic_fn_call("Some", vec![logic_fn_call("Some", vec![int(7)])]);
        let outer_unwrap = method_call(nested_some, "unwrap", vec![]);
        let outer_term = encoder
            .encode_pure(&outer_unwrap)
            .expect("outer unwrap on nested Some should encode");
        let some_seven = encoder
            .encode_pure(&logic_fn_call("Some", vec![int(7)]))
            .expect("Some(7) should encode");

        encoder.assert_option_result_axioms();

        // Use encoder.eq_term for sort coercion (OptionInt vs Int). (#994)
        let eq = encoder.eq_term(outer_term, some_seven);
        let neq = encoder.solver_mut().not(eq);
        encoder.assert_term(neq);

        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "unwrap(Some(Some(7))) must equal Some(7)"
        );
    }

    // Inner unwrap: Some(Some(7)).unwrap().unwrap() == 7
    {
        let mut encoder = AYEncoder::new_with_quantifiers();

        let nested_some = logic_fn_call("Some", vec![logic_fn_call("Some", vec![int(7)])]);
        let outer_unwrap = method_call(nested_some, "unwrap", vec![]);
        let inner_unwrap = method_call(outer_unwrap, "unwrap", vec![]);
        let inner_term = encoder
            .encode_pure(&inner_unwrap)
            .expect("double unwrap on nested Some should encode");
        let seven = encoder.encode_pure(&int(7)).unwrap();

        encoder.assert_option_result_axioms();

        // Use encoder.eq_term for sort coercion. (#994)
        let eq = encoder.eq_term(inner_term, seven);
        let neq = encoder.solver_mut().not(eq);
        encoder.assert_term(neq);

        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "unwrap(unwrap(Some(Some(7)))) must equal 7"
        );
    }
}

/// Reconstruction axiom: forall x. is_ok(x) ==> Ok(unwrap(x)) = x
#[test]
#[timeout(30000)]
fn test_result_ok_reconstruction() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let is_ok_res = method_call(var("res"), "is_ok", vec![]);
    let is_ok_term = encoder
        .encode_pure(&is_ok_res)
        .expect("res.is_ok() should encode");

    let unwrap_res = method_call(var("res"), "unwrap", vec![]);
    let _unwrap_term = encoder
        .encode_pure(&unwrap_res)
        .expect("res.unwrap() should encode");

    let ok_of_unwrap = logic_fn_call("Ok", vec![unwrap_res.clone()]);
    let ok_unwrap_term = encoder
        .encode_pure(&ok_of_unwrap)
        .expect("Ok(res.unwrap()) should encode");

    let res_term = encoder.encode_pure(&var("res")).unwrap();

    encoder.assert_option_result_axioms();

    let reconstruction_fails = {
        let solver = encoder.solver_mut();
        let eq_term = solver.eq(ok_unwrap_term, res_term);
        let neq = solver.not(eq_term);
        solver.and(is_ok_term, neq)
    };
    encoder.assert_term(reconstruction_fails);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "is_ok(res) => Ok(unwrap(res)) == res must hold (reconstruction axiom)"
    );
}

/// Reconstruction axiom: forall x. !is_ok(x) ==> Err(err_error(x)) = x
#[test]
#[timeout(30000)]
fn test_result_err_reconstruction() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let is_ok_res = method_call(var("res"), "is_ok", vec![]);
    let is_ok_term = encoder
        .encode_pure(&is_ok_res)
        .expect("res.is_ok() should encode");

    let unwrap_err_res = method_call(var("res"), "unwrap_err", vec![]);
    let _unwrap_err_term = encoder
        .encode_pure(&unwrap_err_res)
        .expect("res.unwrap_err() should encode");

    let err_of_unwrap_err = logic_fn_call("Err", vec![unwrap_err_res.clone()]);
    let err_unwrap_term = encoder
        .encode_pure(&err_of_unwrap_err)
        .expect("Err(res.unwrap_err()) should encode");

    let res_term = encoder.encode_pure(&var("res")).unwrap();

    encoder.assert_option_result_axioms();

    // Assert: !is_ok(res) AND Err(unwrap_err(res)) != res
    let reconstruction_fails = {
        let solver = encoder.solver_mut();
        let not_is_ok = solver.not(is_ok_term);
        let eq_term = solver.eq(err_unwrap_term, res_term);
        let neq = solver.not(eq_term);
        solver.and(not_is_ok, neq)
    };
    encoder.assert_term(reconstruction_fails);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "!is_ok(res) => Err(unwrap_err(res)) == res must hold (reconstruction axiom)"
    );
}

/// End-to-end pipeline test for the try-operator reconstruction optimization.
///
/// Models `pub fn try_option<T>(x: Option<T>) -> Option<T> { Some(x?) }`
/// after the driver's reconstruction optimization simplifies
/// `Ite(is_some(x), Some(unwrap(x)), x)` to just `x`. (#2675)
///
/// Body: `x` (reconstruction simplified)
/// Ensures: `result == x`
///
/// This MUST verify: the body is literally the variable `x`, so
/// `result == x` with `result = x` is trivially true.
#[test]
#[timeout(30000)]
fn test_try_option_reconstruction_simplified_pipeline() {
    // After reconstruction optimization, body is just `x`.
    let body = var("x");
    let ensures = eq(var("result"), var("x"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "try_option with reconstruction-simplified body should verify: {result:?}"
    );
}

/// End-to-end pipeline test: try_result reconstruction simplified.
///
/// Models `pub fn try_result<T, E>(x: Result<T, E>) -> Result<T, E> { Ok(x?) }`
/// after reconstruction optimization simplifies `Ite(is_ok(x), Ok(unwrap(x)), x)`
/// to just `x`. (#2675)
#[test]
#[timeout(30000)]
fn test_try_result_reconstruction_simplified_pipeline() {
    let body = var("x");
    let ensures = eq(var("result"), var("x"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "try_result with reconstruction-simplified body should verify: {result:?}"
    );
}
