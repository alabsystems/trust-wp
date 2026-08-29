// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Comprehensive type invariant tests for the NON-LOOP (regular function)
//! verification path (#2669).
//!
//! The loop-specific type invariant maintenance tests live in
//! `crates/trust-wp-ay/src/verify/loops/tests/type_invariant_maintenance.rs`.
//! These tests exercise type invariants through `verify_function_with_modes`
//! and `VerificationRequest` — the regular function pipeline.
//!
//! Test scenarios:
//! 1. Function with `requires(x.invariant())` and `ensures(result > 0)`
//!    where body returns `x` — should verify.
//! 2. Postcondition contradicting the invariant — should fail.
//! 3. Two parameters with different type invariants — both usable in postcondition.
//! 4. Type invariant through Deref (`(*x).invariant()`) — by-reference parameter.
//! 5. Type invariant combined with explicit requires — both available.

use super::*;

// ============================================================================
// Test 1: requires(x.invariant()) + ensures(result > 0) + body = x → verifies
// ============================================================================

/// Function with type invariant precondition and compatible postcondition.
///
/// Models:
/// ```rust
/// #[invariant(self.0 > 0)]
/// struct Positive(i32);
///
/// #[requires(x.invariant())]
/// #[ensures(result > 0)]
/// fn return_positive(x: Positive) -> i32 {
///     x.0
/// }
/// ```
///
/// The invariant `x > 0` is assumed from the precondition. Since
/// `result = x` and `x > 0`, the postcondition `result > 0` follows.
#[test]
#[timeout(30000)]
fn test_invariant_precondition_implies_positive_postcondition() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Positive");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Positive".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant()  (expands to x > 0)
    let req = method_call(var("x"), &inv_method, vec![]);

    // ensures: result > 0
    let ens = gt(var("result"), int(0));

    // body: result = x
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "requires(x.invariant()) with body=x should verify result > 0: got {result:?}"
    );
}

// ============================================================================
// Test 2: Postcondition contradicts invariant → should fail
// ============================================================================

/// Function where the postcondition contradicts what the invariant provides.
///
/// Models:
/// ```rust
/// #[invariant(self.0 > 0)]
/// struct Positive(i32);
///
/// #[requires(x.invariant())]
/// #[ensures(result < 0)]
/// fn negate_positive(x: Positive) -> i32 {
///     x.0 // x > 0, so result = x > 0, but postcondition wants result < 0
/// }
/// ```
///
/// The invariant gives `x > 0`, the body returns `x`, so `result > 0`.
/// The postcondition `result < 0` contradicts this — verification should fail.
#[test]
#[timeout(30000)]
fn test_postcondition_contradicts_invariant_fails() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Positive");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Positive".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant()  (x > 0)
    let req = method_call(var("x"), &inv_method, vec![]);

    // ensures: result < 0 — contradicts invariant since body returns x > 0
    let ens = lt(var("result"), int(0));

    // body: result = x
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "postcondition result < 0 contradicts invariant x > 0: should fail, got {result:?}"
    );
}

// ============================================================================
// Test 3: Two parameters with different type invariants
// ============================================================================

/// Two parameters with different type invariants, both usable in postcondition.
///
/// Models:
/// ```rust
/// #[invariant(self.0 > 0)]
/// struct Positive(i32);
///
/// #[invariant(self.0 >= 10 && self.0 <= 100)]
/// struct Bounded(i32);
///
/// #[requires(x.invariant())]
/// #[requires(y.invariant())]
/// #[ensures(result > 10)]
/// fn add_positive_bounded(x: Positive, y: Bounded) -> i32 {
///     x.0 + y.0 // x > 0, y >= 10, so x + y > 10
/// }
/// ```
///
/// With Positive invariant (x > 0) and Bounded invariant (y >= 10 && y <= 100),
/// the sum x + y > 10 follows from x > 0 and y >= 10. Both invariants must
/// be independently resolved and usable.
#[test]
#[timeout(30000)]
fn test_two_parameters_different_type_invariants() {
    let inv_positive = trust_wp_core::logic::type_invariant_method_name("Positive");
    let inv_bounded = trust_wp_core::logic::type_invariant_method_name("Bounded");

    let positive_def = trust_wp_core::type_invariant_def! {
        type_name: "Positive".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    let bounded_def = trust_wp_core::type_invariant_def! {
        type_name: "Bounded".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: and(ge(var("self"), int(10)), le(var("self"), int(100))),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant() && y.invariant()
    let req_x = method_call(var("x"), &inv_positive, vec![]);
    let req_y = method_call(var("y"), &inv_bounded, vec![]);

    // ensures: result > 10 (x > 0 and y >= 10 implies x + y > 10)
    let ens = gt(var("result"), int(10));

    // body: result = x + y
    let body = add(var("x"), var("y"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_x, req_y], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[positive_def, bounded_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x > 0 + y >= 10 => result > 10 should verify: got {result:?}"
    );
}

/// Negative test: postcondition too strong for the combined invariants.
///
/// With Positive (x > 0) and Bounded (y in [10, 100]), the sum x + y
/// is at least 11 but cannot exceed 101 + epsilon. The postcondition
/// `result > 200` is too strong: x could be 1 and y could be 10,
/// giving result = 11 which violates result > 200.
#[test]
#[timeout(30000)]
fn test_two_parameters_postcondition_too_strong_fails() {
    let inv_positive = trust_wp_core::logic::type_invariant_method_name("Positive");
    let inv_bounded = trust_wp_core::logic::type_invariant_method_name("Bounded");

    let positive_def = trust_wp_core::type_invariant_def! {
        type_name: "Positive".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    let bounded_def = trust_wp_core::type_invariant_def! {
        type_name: "Bounded".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: and(ge(var("self"), int(10)), le(var("self"), int(100))),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant() && y.invariant()
    let req_x = method_call(var("x"), &inv_positive, vec![]);
    let req_y = method_call(var("y"), &inv_bounded, vec![]);

    // ensures: result > 200 — too strong (x=1, y=10 gives result=11)
    let ens = gt(var("result"), int(200));

    // body: result = x + y
    let body = add(var("x"), var("y"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_x, req_y], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[positive_def, bounded_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "result > 200 is too strong for x > 0, y in [10, 100]: should fail, got {result:?}"
    );
}

// ============================================================================
// Test 4: Type invariant through Deref — by-reference parameter
// ============================================================================

/// Type invariant accessed through Deref for a by-reference parameter.
///
/// Models:
/// ```rust
/// #[invariant(self.0 > 0)]
/// struct Positive(i32);
///
/// #[requires((*x).invariant())]
/// #[ensures(result > 0)]
/// fn deref_positive(x: &Positive) -> i32 {
///     x.0 // (*x) > 0, body returns (*x), so result > 0
/// }
/// ```
///
/// The `Deref(Var("x"))` pattern models by-reference parameter access.
/// The invariant is applied to the dereferenced value, and the body
/// returns the dereferenced value, so the postcondition holds.
#[test]
#[timeout(30000)]
fn test_type_invariant_through_deref() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Positive");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Positive".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: (*x).invariant()  — deref pattern for &Positive
    let req = method_call(deref(var("x")), &inv_method, vec![]);

    // ensures: result > 0
    let ens = gt(var("result"), int(0));

    // body: result = *x (dereferenced value)
    let body = deref(var("x"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "(*x).invariant() with body=*x should verify result > 0: got {result:?}"
    );
}

/// Negative test: Deref invariant does not hold when body produces a different value.
///
/// Models:
/// ```rust
/// #[requires((*x).invariant())] // *x > 0
/// #[ensures(result > 0)]
/// fn deref_negate(x: &Positive) -> i32 {
///     -(*x) // negation makes result <= 0
/// }
/// ```
///
/// The invariant gives `*x > 0`, but the body computes `-(*x)` which is
/// negative. The postcondition `result > 0` should fail.
#[test]
#[timeout(30000)]
fn test_type_invariant_through_deref_negation_fails() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Positive");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Positive".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: (*x).invariant()
    let req = method_call(deref(var("x")), &inv_method, vec![]);

    // ensures: result > 0
    let ens = gt(var("result"), int(0));

    // body: result = -(*x) — negation of positive value
    let body = neg(deref(var("x")));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "neg(*x) where *x > 0 gives result < 0, should fail result > 0: got {result:?}"
    );
}

// ============================================================================
// Test 5: Type invariant combined with explicit requires
// ============================================================================

/// Type invariant combined with an explicit user precondition.
///
/// Models:
/// ```rust
/// #[invariant(self.0 > 0)]
/// struct Positive(i32);
///
/// #[requires(x.invariant())]
/// #[requires(x < 100)]
/// #[ensures(result > 0 && result < 101)]
/// fn bounded_increment(x: Positive) -> i32 {
///     x.0 + 1 // x > 0 && x < 100 => x + 1 in (1, 100], so > 0 && < 101
/// }
/// ```
///
/// Both the type invariant (x > 0) and the explicit requires (x < 100)
/// must be available to prove the postcondition. The invariant alone
/// cannot establish `result < 101`, and the explicit requires alone
/// cannot establish `result > 0` (x could be 0 without the invariant).
#[test]
#[timeout(30000)]
fn test_invariant_combined_with_explicit_requires() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Positive");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Positive".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant() (x > 0)
    let req_inv = method_call(var("x"), &inv_method, vec![]);
    // requires: x < 100 (explicit user precondition)
    let req_bound = lt(var("x"), int(100));

    // ensures: result > 0 && result < 101
    let ens = and(gt(var("result"), int(0)), lt(var("result"), int(101)));

    // body: result = x + 1
    let body = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_inv, req_bound], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "invariant(x > 0) + requires(x < 100) + body(x+1) => result in (0, 101): got {result:?}"
    );
}

/// Negative test: without the explicit requires, postcondition is too strong.
///
/// With only the invariant (x > 0) but no upper bound on x, the body
/// x + 1 could produce any value > 1. The postcondition `result < 101`
/// cannot be proved because x could be 100, making result = 101.
#[test]
#[timeout(30000)]
fn test_invariant_without_explicit_bound_postcondition_too_strong() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Positive");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Positive".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: ONLY x.invariant() — no upper bound
    let req_inv = method_call(var("x"), &inv_method, vec![]);

    // ensures: result > 0 && result < 101 — upper bound unprovable without x < 100
    let ens = and(gt(var("result"), int(0)), lt(var("result"), int(101)));

    // body: result = x + 1
    let body = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_inv], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "invariant alone cannot prove result < 101 (x could be 100): should fail, got {result:?}"
    );
}

/// Without the invariant, explicit requires alone cannot establish positivity.
///
/// With only `x < 100` but no invariant (x > 0), x could be -1000.
/// The postcondition `result > 0` fails because x + 1 could be negative.
#[test]
#[timeout(30000)]
fn test_explicit_requires_without_invariant_positivity_fails() {
    // No type invariant definition — just the explicit requires
    let req_bound = lt(var("x"), int(100));

    // ensures: result > 0 — cannot prove without invariant guaranteeing x > 0
    let ens = gt(var("result"), int(0));

    // body: result = x + 1
    let body = add(var("x"), int(1));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_bound], &[ens]).return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "x < 100 alone cannot prove result > 0 (x could be negative): should fail, got {result:?}"
    );
}
