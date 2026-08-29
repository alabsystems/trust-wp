// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end tests for closure capture type invariant injection (#2257).
//!
//! When verifying a function that receives a closure, the driver injects
//! type invariant assumptions for each captured variable as regular
//! `requires` clauses (via `build_closure_capture_invariant_requires` in
//! `type_invariants/clauses.rs`). These tests verify that:
//!
//! 1. The injected invariant assumptions are usable by the solver
//! 2. Postconditions that depend on capture invariant properties verify
//! 3. Without the invariant injection, the same postconditions fail
//! 4. The invariant axiom definition connects to the method-call encoding
//!
//! The "self-projection" tests simulate closure *body* verification, where
//! the driver produces `inv_T(self.0)` style requires via
//! `build_current_closure_self_invariant_requires`. In this scenario,
//! captures are named `self.0`, `self.1`, etc. rather than their outer
//! variable names.

use ntest::timeout;
use trust_wp_core::{
    closure::{CaptureField, CaptureKind, ClosureCaptureInfo},
    formula::{intern_sort_name, ExprSort},
    logic::type_invariant_method_name,
};

use super::{super::*, helpers::*};

/// Helper: create a NonZero invariant def with body `self > 0`.
fn nonzero_invariant() -> trust_wp_core::logic::TypeInvariantDef {
    trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    }
}

/// Helper: build an invariant method call `inv_NonZero(receiver)`.
fn nonzero_inv_call(receiver: PureExpr) -> PureExpr {
    method_call(receiver, &type_invariant_method_name("NonZero"), vec![])
}

/// Helper: create a ClosureCaptureInfo with a single NonZero-typed capture.
fn nonzero_capture_info(field_name: &str) -> ClosureCaptureInfo {
    let sort_id = intern_sort_name("NonZero");
    let capture = CaptureField::new(
        field_name,
        ExprSort::Datatype(sort_id),
        CaptureKind::ByValue,
    );
    ClosureCaptureInfo::new("test::closure#0".to_string(), vec![capture])
}

/// Helper: create a ClosureCaptureInfo for closure body verification.
///
/// When verifying a closure's own body, the capture info uses `param_name = "self"`
/// and captures reference outer variable names (the driver maps these to `self.N`
/// projections in the requires clauses).
fn self_capture_info(captures: Vec<CaptureField>) -> ClosureCaptureInfo {
    ClosureCaptureInfo::new("test::self_closure#0".to_string(), captures)
        .with_param_name(Some("self".to_string()))
}

// ============================================================================
// Positive: invariant injection enables postcondition proof
// ============================================================================

/// When a closure captures `x: NonZero` and the invariant `x > 0` is injected
/// as a precondition, the postcondition `result > 0` on `return x` should verify.
///
/// This simulates:
/// ```rust
/// #[invariant(self.0 > 0)]
/// struct NonZero(i32);
///
/// fn use_closure(c: impl Fn() -> i32) -> i32 {
///     c()
/// }
///
/// // Closure captures `x: NonZero`; body returns `x`
/// let x = NonZero(42);
/// use_closure(move || x.0)
/// ```
///
/// The driver injects `inv_NonZero(x)` as a requires clause, which combined
/// with the defining axiom `inv_NonZero(self) <=> self > 0` allows the solver
/// to derive `x > 0` and verify `result > 0`.
#[test]
#[timeout(30000)]
fn test_closure_capture_invariant_enables_postcondition_proof() {
    let inv_def = nonzero_invariant();

    // Driver injects: requires inv_NonZero(x)
    let req = nonzero_inv_call(var("x"));

    // ensures: result > 0
    let ens = gt(var("result"), int(0));

    // body: result = x
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def]))
            .closure_captures(Some(&[nonzero_capture_info("x")])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "closure capture with NonZero invariant should enable result > 0 proof: got {result:?}"
    );
}

/// Negative test: without the invariant injection (no requires), the same
/// postcondition fails because x is unconstrained.
#[test]
#[timeout(30000)]
fn test_closure_capture_without_invariant_injection_fails() {
    let inv_def = nonzero_invariant();

    // NO requires -- invariant not injected
    // ensures: result > 0
    let ens = gt(var("result"), int(0));

    // body: result = x
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def]))
            .closure_captures(Some(&[nonzero_capture_info("x")])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "without invariant injection, result > 0 should fail (x unconstrained): got {result:?}"
    );
}

/// Negative test: without the type invariant *definition* (axiom), even with
/// the method call in requires, the solver cannot connect inv_NonZero(x) to
/// `x > 0`, so the postcondition should fail.
#[test]
#[timeout(30000)]
fn test_closure_capture_without_invariant_def_fails() {
    // requires: inv_NonZero(x) — but no axiom defining what this means
    let req = nonzero_inv_call(var("x"));

    // ensures: result > 0
    let ens = gt(var("result"), int(0));

    // body: result = x
    let body = var("x");

    // No type_invariants — inv_NonZero is an uninterpreted function
    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .closure_captures(Some(&[nonzero_capture_info("x")])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "without invariant definition, inv_NonZero(x) is opaque and result > 0 should fail: got {result:?}"
    );
}

// ============================================================================
// Arithmetic with captured invariant variables
// ============================================================================

/// Closure captures `x: NonZero`, body returns `x + 1`. Postcondition `result > 1`
/// should verify because `x > 0` (from invariant) implies `x + 1 > 1`.
#[test]
#[timeout(30000)]
fn test_closure_capture_invariant_arithmetic() {
    let inv_def = nonzero_invariant();

    // Driver injects: requires inv_NonZero(x)
    let req = nonzero_inv_call(var("x"));

    // ensures: result > 1
    let ens = gt(var("result"), int(1));

    // body: result = x + 1
    let body = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def]))
            .closure_captures(Some(&[nonzero_capture_info("x")])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x > 0 from invariant should prove x + 1 > 1: got {result:?}"
    );
}

/// Negative: closure captures `x: NonZero`, body returns `x - 1`. Postcondition
/// `result > 0` should fail because `x > 0` only gives `x - 1 >= 0`,
/// not `x - 1 > 0` (counterexample: x = 1, result = 0).
#[test]
#[timeout(30000)]
fn test_closure_capture_invariant_arithmetic_insufficient() {
    let inv_def = nonzero_invariant();

    // Driver injects: requires inv_NonZero(x)
    let req = nonzero_inv_call(var("x"));

    // ensures: result > 0
    let ens = gt(var("result"), int(0));

    // body: result = x - 1
    let body = sub(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def]))
            .closure_captures(Some(&[nonzero_capture_info("x")])),
    )
    .expect("encoding should succeed");

    // x=1, result=0 is a valid counterexample: inv_NonZero(1)=true but 0 > 0 = false
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "x - 1 > 0 should fail from x > 0 alone (counterexample: x=1): got {result:?}"
    );
}

// ============================================================================
// Multiple captures with invariants
// ============================================================================

/// Closure captures `x: NonZero` and `y: NonZero`. The postcondition
/// `result > 1` on body `x + y` should verify because both are > 0.
#[test]
#[timeout(30000)]
fn test_closure_capture_multiple_invariants() {
    let inv_def = nonzero_invariant();

    let sort_id = intern_sort_name("NonZero");
    let cap_x = CaptureField::new("x", ExprSort::Datatype(sort_id), CaptureKind::ByValue);
    let cap_y = CaptureField::new("y", ExprSort::Datatype(sort_id), CaptureKind::ByValue);
    let capture_info =
        ClosureCaptureInfo::new("test::multi_closure#0".to_string(), vec![cap_x, cap_y]);

    // Driver injects: requires inv_NonZero(x) && inv_NonZero(y)
    let req_x = nonzero_inv_call(var("x"));
    let req_y = nonzero_inv_call(var("y"));

    // ensures: result > 1
    let ens = gt(var("result"), int(1));

    // body: result = x + y
    let body = add(var("x"), var("y"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_x, req_y], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def]))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x > 0 && y > 0 should prove x + y > 1: got {result:?}"
    );
}

/// With only ONE invariant injected (for x but not y), `x + y > 1` should
/// fail because y is unconstrained.
#[test]
#[timeout(30000)]
fn test_closure_capture_partial_invariant_injection_fails() {
    let inv_def = nonzero_invariant();

    let sort_id = intern_sort_name("NonZero");
    let cap_x = CaptureField::new("x", ExprSort::Datatype(sort_id), CaptureKind::ByValue);
    let cap_y = CaptureField::new("y", ExprSort::Datatype(sort_id), CaptureKind::ByValue);
    let capture_info =
        ClosureCaptureInfo::new("test::multi_closure#0".to_string(), vec![cap_x, cap_y]);

    // Only inject invariant for x, not y
    let req_x = nonzero_inv_call(var("x"));

    // ensures: result > 1
    let ens = gt(var("result"), int(1));

    // body: result = x + y
    let body = add(var("x"), var("y"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_x], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def]))
            .closure_captures(Some(&[capture_info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "partial invariant injection (only x) should fail to prove x + y > 1: got {result:?}"
    );
}

// ============================================================================
// Self-projection: closure body verification with `self.N` receivers
// ============================================================================
//
// As of Wave 16A (#2257), `self.N` references inside a closure body route
// through the registered closure environment's native datatype selectors
// (`closure_capture_<suffix>_N`) via `try_datatype_selector` rather than
// decaying into free uninterpreted variables. The selector returns a term
// whose sort matches the capture-field sort. For these unit tests to drive
// the invariant body's arithmetic (`self > 0`, `self + 1`, …) directly, the
// captures are typed `ExprSort::Int` — the simplest sort that flows through
// the invariant axiom without requiring a Datatype-to-Int coercion bridge.
//
// The end-to-end harness `closures/10_tyinv` exercises Datatype-typed
// closure captures against the full driver pipeline.

/// Helper: create a ClosureCaptureInfo with Int-sorted self-projection
/// captures for closure-body verification tests. See module-level comment
/// for rationale on the sort choice.
fn self_int_capture_info(field_names: &[&str]) -> ClosureCaptureInfo {
    let captures: Vec<CaptureField> = field_names
        .iter()
        .map(|name| CaptureField::new(*name, ExprSort::Int, CaptureKind::ByValue))
        .collect();
    self_capture_info(captures)
}

/// When verifying the closure body itself, the driver produces
/// `inv_NonZero(self.0)` as a requires clause. The body references `self.0`
/// instead of the outer variable name. This simulates:
///
/// ```rust
/// #[invariant(self.0 > 0)]
/// struct NonZero(i32);
///
/// // When verifying this closure's body:
/// let x = NonZero(42);
/// let closure = move || x.0;
/// //   requires: inv_NonZero(self.0)
/// //   body: result = self.0
/// //   ensures: result > 0
/// ```
///
/// Wave 16A: `self.0` is encoded via the closure-env native selector
/// (`closure_capture_<suffix>_0(self)`), so the capture sort flows through
/// to the invariant call. We use `ExprSort::Int` captures here to keep the
/// invariant body's arithmetic comparison sort-aligned without invoking a
/// datatype coercion. See module-level comment.
#[test]
#[timeout(30000)]
fn test_self_projection_invariant_enables_proof() {
    let inv_def = nonzero_invariant();
    let info = self_int_capture_info(&["x"]);

    // Driver produces: requires inv_NonZero(self.0)
    let req = nonzero_inv_call(var("self.0"));

    // ensures: result > 0
    let ens = gt(var("result"), int(0));

    // body: result = self.0
    let body = var("self.0");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def]))
            .closure_captures(Some(&[info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "self.0 > 0 from invariant should enable result > 0 proof: got {result:?}"
    );
}

/// Negative: without invariant injection on self.0, postcondition fails.
#[test]
#[timeout(30000)]
fn test_self_projection_without_injection_fails() {
    let inv_def = nonzero_invariant();
    let info = self_int_capture_info(&["x"]);

    // NO requires — invariant not injected
    let ens = gt(var("result"), int(0));
    let body = var("self.0");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def]))
            .closure_captures(Some(&[info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "without invariant injection, self.0 is unconstrained and should fail: got {result:?}"
    );
}

/// Multiple captures with self-projection: closure captures two NonZero fields.
/// Driver produces `inv_NonZero(self.0)` and `inv_NonZero(self.1)`.
/// Body returns `self.0 + self.1`; postcondition `result > 1` should verify.
#[test]
#[timeout(30000)]
fn test_self_projection_multiple_captures() {
    let inv_def = nonzero_invariant();
    let info = self_int_capture_info(&["x", "y"]);

    // Driver produces: requires inv_NonZero(self.0), inv_NonZero(self.1)
    let req_0 = nonzero_inv_call(var("self.0"));
    let req_1 = nonzero_inv_call(var("self.1"));

    // ensures: result > 1
    let ens = gt(var("result"), int(1));

    // body: result = self.0 + self.1
    let body = add(var("self.0"), var("self.1"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_0, req_1], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def]))
            .closure_captures(Some(&[info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "self.0 > 0 && self.1 > 0 should prove self.0 + self.1 > 1: got {result:?}"
    );
}

/// Self-projection arithmetic: body is `self.0 + 1`, postcondition `result > 1`.
#[test]
#[timeout(30000)]
fn test_self_projection_arithmetic() {
    let inv_def = nonzero_invariant();
    let info = self_int_capture_info(&["x"]);

    let req = nonzero_inv_call(var("self.0"));
    let ens = gt(var("result"), int(1));
    let body = add(var("self.0"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def]))
            .closure_captures(Some(&[info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "self.0 > 0 should prove self.0 + 1 > 1: got {result:?}"
    );
}

/// Negative self-projection arithmetic: `self.0 - 1 > 0` is unprovable from `self.0 > 0`.
#[test]
#[timeout(30000)]
fn test_self_projection_arithmetic_insufficient() {
    let inv_def = nonzero_invariant();
    let info = self_int_capture_info(&["x"]);

    let req = nonzero_inv_call(var("self.0"));
    let ens = gt(var("result"), int(0));
    let body = sub(var("self.0"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def]))
            .closure_captures(Some(&[info])),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "self.0 - 1 > 0 should fail from self.0 > 0 (counterexample: self.0=1): got {result:?}"
    );
}
