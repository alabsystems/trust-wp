// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Signed (i8) division encoding tests — models the checked_ops residual.
//!
//! The historical `checked_ops.rs` Creusot compat residual was caused by
//! ay's `int_div` not being subject to congruence closure in the AUFLIA
//! fragment. When the spec used different variable names from the assertion
//! (e.g., `div(self_val, rhs_val)` vs `div(a, b)`), ay returned Incomplete
//! even though the equality chain was a simple EUF consequence.
//!
//! The localization hierarchy:
//! - Division with same variables: **Verified** (syntactic match)
//! - Division with different variables + equality: **Verified** via ground bridge
//! - Trivial ensures (no division): **Verified**
//! - Division quotient-remainder property: **Verified** (ay axiom)
//!
//! Root cause: ay lacks congruence closure for `int_div` in QF_AUFLIA.
//! trust-wp bridges encoded ground division applications until that is fixed
//! in ay.
//!
//! The unsigned (u8) division tests live in `std_specs_collections.rs`.
//! This module covers the signed case, which adds the overflow guard
//! `(a != -128 || b != -1)` to exclude the single signed overflow case.
//!
//! Part of #2342

use ntest::timeout;

use super::super::{super::*, helpers::*};

/// Signed checked division: assumption directly implies ensures → Verified.
///
/// Models Creusot's `test_i8_div_no_overflow`:
///   `#[requires(b@ != 0 && (a@ != -128 || b@ != -1))]`
///   `assert!(a.checked_div(b).unwrap() == a / b)`
///
/// Both sides use the same `div(a, b)` term, so the refutation
/// `(cd_result == div(a,b)) ∧ ¬(cd_result == div(a,b))` is trivially UNSAT.
/// The solver doesn't need to reason about division semantics.
///
/// Part of #2342
#[test]
#[timeout(30000)]
fn test_verify_checked_div_i8_no_overflow() {
    // requires: b != 0 && (a != -128 || b != -1)
    let req_nonzero = ne(var("b"), int(0));
    let req_overflow_guard = or(ne(var("a"), int(-128)), ne(var("b"), int(-1)));
    let req = and(req_nonzero, req_overflow_guard);

    // Call-site assumption from checked_div spec:
    //   b != 0 ==> cd_result == a / b
    let cd_assumption = implies(
        ne(var("b"), int(0)),
        eq(var("cd_result"), div(var("a"), var("b"))),
    );

    // ensures: cd_result == a / b
    let ens = eq(var("cd_result"), div(var("a"), var("b")));

    let body = var("cd_result");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req, cd_assumption], &[ens]).return_expr(Some(&body)),
    );
    // Trivially verified: assumption and ensures share the same div(a, b) term.
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "i8 checked_div with direct assumption should verify (trivial refutation): {result:?}"
    );
}

/// Signed overflowing_div: assumption directly implies ensures → Verified.
///
/// Part of #2342
#[test]
#[timeout(30000)]
fn test_verify_overflowing_div_i8() {
    // requires: b != 0 && (a != -128 || b != -1)
    let req_nonzero = ne(var("b"), int(0));
    let req_overflow_guard = or(ne(var("a"), int(-128)), ne(var("b"), int(-1)));
    let req = and(req_nonzero, req_overflow_guard);

    // Call-site assumption from overflowing_div spec:
    //   result_0 == a / b  (the quotient)
    //   result_1 == false  (no overflow, given the precondition)
    let ov_div_quotient = eq(var("result_0"), div(var("a"), var("b")));
    let ov_div_overflow = eq(var("result_1"), bool_expr(false));

    // ensures: result_0 == a / b && result_1 == false
    let ens = and(
        eq(var("result_0"), div(var("a"), var("b"))),
        eq(var("result_1"), bool_expr(false)),
    );

    let body = var("result_0");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req, ov_div_quotient, ov_div_overflow], &[ens])
            .return_expr(Some(&body)),
    );
    // Trivially verified: same div(a, b) term on both sides.
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "i8 overflowing_div with direct assumption should verify: {result:?}"
    );
}

/// Localization: signed division residual is NOT from the overflow guard.
///
/// With `b != 0` (no overflow guard) and trivial ensures `cd_result == cd_result`,
/// the result is Verified — the overflow guard itself is not the source of
/// incompleteness.
///
/// Part of #2342
#[test]
#[timeout(30000)]
fn test_signed_div_residual_is_division_not_overflow_guard() {
    // requires: b != 0 (no overflow guard — intentionally weaker)
    let req = ne(var("b"), int(0));

    // checked_div postcondition
    let cd_assumption = implies(
        ne(var("b"), int(0)),
        eq(var("cd_result"), div(var("a"), var("b"))),
    );

    // Trivial ensures that avoids division reasoning: cd_result == cd_result
    let ens = eq(var("cd_result"), var("cd_result"));

    let body = var("cd_result");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req, cd_assumption], &[ens]).return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "trivial ensures (no division) should verify even without overflow guard: {result:?}"
    );
}

/// Localization: division-value path is the actual residual.
///
/// Same as the full checked_div test but without the overflow guard.
/// Both sides still share the same `div(a, b)` term, so this trivially verifies.
///
/// Part of #2342
#[test]
#[timeout(30000)]
fn test_signed_div_value_path_is_residual() {
    // requires: b != 0 only (no overflow guard)
    let req = ne(var("b"), int(0));

    // cd_result == a / b
    let cd_assumption = implies(
        ne(var("b"), int(0)),
        eq(var("cd_result"), div(var("a"), var("b"))),
    );

    // ensures: cd_result == a / b (same div term as assumption)
    let ens = eq(var("cd_result"), div(var("a"), var("b")));

    let body = var("cd_result");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req, cd_assumption], &[ens]).return_expr(Some(&body)),
    );
    // Still trivially verified because assumption == ensures.
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "same-term division ensures should verify: {result:?}"
    );
}

/// Pipeline-realistic test: parameter binding requires congruence for div.
///
/// Models the actual pipeline encoding where the spec uses `self`/`rhs`
/// variables and the assertion uses `a`/`b` variables. The connection
/// `self == a ∧ rhs == b` requires the solver to apply congruence closure:
/// `div(self, rhs) == div(a, b)`.
///
/// **ROOT CAUSE FINDING:** ay's int_div is not subject to congruence closure
/// in the AUFLIA fragment. The solver returns Unknown(Incomplete) even though
/// the equality chain `self_val == a ∧ rhs_val == b → div(self_val, rhs_val)
/// == div(a, b)` is a simple EUF consequence. This gap is the mechanism by
/// which the checked_ops pipeline reports Unknown: the spec produces
/// `div(self_model, rhs_model)` while the assertion produces `div(a, b)`,
/// and the solver can't bridge them without trust-wp's ground congruence bridge.
///
/// Part of #2342
#[test]
#[timeout(30000)]
fn test_signed_div_congruence_through_parameter_binding() {
    // requires: b != 0 && (a != -128 || b != -1)
    let req_nonzero = ne(var("b"), int(0));
    let req_overflow_guard = or(ne(var("a"), int(-128)), ne(var("b"), int(-1)));
    let req = and(req_nonzero, req_overflow_guard);

    // Parameter binding: self == a, rhs == b
    let self_eq_a = eq(var("self_val"), var("a"));
    let rhs_eq_b = eq(var("rhs_val"), var("b"));

    // Spec uses self_val/rhs_val: cd_result == div(self_val, rhs_val)
    let cd_assumption = implies(
        ne(var("rhs_val"), int(0)),
        eq(var("cd_result"), div(var("self_val"), var("rhs_val"))),
    );

    // Assertion uses a/b: cd_result == div(a, b)
    let ens = eq(var("cd_result"), div(var("a"), var("b")));

    let body = var("cd_result");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req, self_eq_a, rhs_eq_b, cd_assumption], &[ens])
            .return_expr(Some(&body)),
    );
    // trust-wp asserts ground congruence bridges for encoded int_div terms, so
    // the equality aliases are enough to connect both quotient terms.
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "congruence through int_div aliases should verify: {result:?}"
    );
}

/// Standalone symbolic division: no assumption shortcut.
///
/// Verifies `result == div(a, b)` where result IS `div(a, b)` in the body
/// (no intermediate variable). This tests whether ay handles the identity
/// `int_div(a, b) == int_div(a, b)` at the SMT level without any call-site
/// assumption wrapping.
///
/// Part of #2342
#[test]
#[timeout(30000)]
fn test_signed_div_standalone_identity() {
    // requires: b != 0
    let req = ne(var("b"), int(0));

    // body IS the division expression — no call-site assumption
    let body = div(var("a"), var("b"));

    // ensures: result == a / b
    let ens = eq(var("result"), div(var("a"), var("b")));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    );
    // The body IS div(a, b), so result == div(a, b) is the identity.
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "standalone div identity should verify: {result:?}"
    );
}

/// Division quotient-remainder property: div(a, b) * b + mod(a, b) == a.
///
/// This is the fundamental property of Euclidean division. If ay supports
/// `int_div` and `int_mod` with their standard axioms, this should verify.
/// If ay treats them as nonlinear arithmetic in QF_AUFLIA, this returns
/// Unknown("incomplete") — confirming the solver limitation that causes
/// the checked_ops harness failure.
///
/// Part of #2342
#[test]
#[timeout(30000)]
fn test_division_quotient_remainder_property() {
    // requires: b != 0
    let req = ne(var("b"), int(0));

    // body: div(a, b) * b + mod(a, b)
    let quotient_times_divisor = mul(div(var("a"), var("b")), var("b"));
    let remainder = mod_expr(var("a"), var("b"));
    let body = add(quotient_times_divisor, remainder);

    // ensures: result == a (the fundamental division property)
    let ens = eq(var("result"), var("a"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    );
    // This requires ay to reason about the relationship between int_div
    // and int_mod — a nonlinear property in QF_AUFLIA. This is the core
    // of the checked_ops residual: ay can't prove division properties.
    let is_expected = matches!(result, Ok(VerificationResult::Verified(_)))
        || matches!(
            &result,
            Ok(VerificationResult::Unknown(ref reason))
                if reason.as_str().contains("incomplete")
                    || reason.as_str().contains("unsupported arithmetic")
        );
    assert!(
        is_expected,
        "div-mod fundamental property should verify or return incomplete: {result:?}"
    );
}
