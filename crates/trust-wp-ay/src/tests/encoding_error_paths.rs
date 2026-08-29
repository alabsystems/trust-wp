// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Error-path coverage tests for pure expression encoding.
//!
//! Covers the distinct error-handling strategies in `pure_encoding.rs`:
//! - **LetAssume**: Err propagation — unencodable assumptions fail closed
//!   after incrementing the LetAssumeDropped unsoundness counter.
//! - **LetObligation** (line 728): Err propagation — unencodable obligation
//!   must propagate to prevent unsound Verified result.

use ntest::timeout;
use trust_wp_core::formula::FloatBits;

use super::{super::*, helpers::*};

/// Returns a `PureExpr` that is guaranteed to fail encoding.
///
/// Uses `Float(NaN)` because `try_real_const` rejects NaN/Inf values.
/// Previously used `PureExpr::Closure` with params, but closures now
/// encode conservatively as fresh unconstrained constants (#985).
fn unencodable_expr() -> PureExpr {
    PureExpr::Float(FloatBits::from_f64(f64::NAN))
}

/// LetAssume propagates unencodable assumptions after recording LetAssumeDropped.
#[test]
#[timeout(30000)]
fn let_assume_unencodable_assumption_propagates_error() {
    let body = let_assume(unencodable_expr(), bool_expr(true));
    let ensures = eq(var("result"), bool_expr(true));
    let r = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    );
    assert!(
        r.is_err(),
        "unencodable LetAssume assumption should propagate as an error: {r:?}"
    );
    let msg = format!("{}", r.unwrap_err());
    assert!(msg.contains("float"), "error should mention float: {msg}");
}

/// Propagated LetAssume errors prevent vacuous strengthening.
#[test]
#[timeout(30000)]
fn let_assume_unencodable_assumption_does_not_verify_false_body() {
    let body = let_assume(unencodable_expr(), bool_expr(false));
    let ensures = eq(var("result"), bool_expr(true));
    let r = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    );
    assert!(
        r.is_err(),
        "unencodable LetAssume assumption should fail before proving false body: {r:?}"
    );
    let msg = format!("{}", r.unwrap_err());
    assert!(msg.contains("float"), "error should mention float: {msg}");
}

/// LetObligation must propagate encoding error (unsound to drop conjunction conjunct).
#[test]
#[timeout(30000)]
fn let_obligation_unencodable_obligation_propagates_error() {
    let body = let_obligation(unencodable_expr(), bool_expr(true));
    let ensures = eq(var("result"), bool_expr(true));
    let r = verify_function_with_modes(
        VerificationRequest::new(&[], &[ensures]).return_expr(Some(&body)),
    );
    assert!(
        r.is_err(),
        "must return Err to prevent unsound Verified: {r:?}"
    );
    let msg = format!("{}", r.unwrap_err());
    assert!(msg.contains("float"), "error should mention float: {msg}");
}
