// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for type invariant preservation through arithmetic
//! operations (#2669, AC3 + AC4).
//!
//! These tests verify that the NonZero invariant pattern (`self > 0`)
//! is correctly propagated through multiplication, division, and other
//! arithmetic operations beyond the basic add/sub patterns tested in
//! `nonzero_quantified_invariants.rs`.
//!
//! Test scenarios:
//! 1. Multiplication preserves NonZero: x > 0 && y > 0 => x * y > 0
//! 2. Division preserves NonZero with appropriate precondition
//! 3. Multiple distinct NonZero types (U32, U64) in the same context
//! 4. NonZero invariant with `ne` shape (self != 0) vs `gt` (self > 0)
//! 5. Open inv result suppression: no result invariant postcondition
//! 6. Invariant through chained arithmetic (a + b) * c > 0

use super::*;

// ============================================================================
// Test 1: Multiplication preserves NonZero invariant
// ============================================================================

/// NonZero multiplication: x > 0 && y > 0 => x * y > 0.
///
/// Models:
/// ```rust
/// #[invariant(self.0@ > 0)]
/// struct NonZero(u32);
///
/// fn mul(self, rhs: Self) -> Self {
///     Self(self.0 * rhs.0)
/// }
/// ```
///
/// With unbounded integers (SMT-LIB Int sort), multiplication of two
/// positive values always yields a positive value. This verifies the
/// invariant transfer through the `*` operator.
#[test]
#[timeout(30000)]
fn test_nonzero_mul_preserves_invariant() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: self.invariant() && rhs.invariant()
    let req_self = method_call(var("self_"), &inv_method, vec![]);
    let req_rhs = method_call(var("rhs"), &inv_method, vec![]);

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = self * rhs
    let body = mul(var("self_"), var("rhs"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_self, req_rhs], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "NonZero mul: self>0 * rhs>0 should preserve invariant result>0: got {result:?}"
    );
}

/// Negative test: multiplication by a potentially negative value can violate
/// the NonZero invariant.
///
/// If `y` has no invariant constraint, `x > 0` and `y = -1` gives `x * y < 0`.
#[test]
#[timeout(30000)]
fn test_nonzero_mul_unconstrained_rhs_fails() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: ONLY self.invariant() (rhs unconstrained)
    let req_self = method_call(var("self_"), &inv_method, vec![]);

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = self * y (y is unconstrained, could be negative)
    let body = mul(var("self_"), var("y"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_self], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "NonZero mul with unconstrained rhs should fail (y=-1 is counterexample): got {result:?}"
    );
}

// ============================================================================
// Test 2: Division preserves NonZero with appropriate precondition
// ============================================================================

/// NonZero division with precondition: x > 0 && d > 0 && x >= d => x / d > 0.
///
/// Models integer division where x >= d > 0 ensures x / d >= 1 > 0.
#[test]
#[timeout(30000)]
fn test_nonzero_div_with_divisibility_precondition() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: self.invariant() && d.invariant() && self >= d
    let req_self = method_call(var("self_"), &inv_method, vec![]);
    let req_d = method_call(var("d"), &inv_method, vec![]);
    let req_ge = ge(var("self_"), var("d"));

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = self / d
    let body = div(var("self_"), var("d"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_self, req_d, req_ge], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "NonZero div(self, d) with self>=d>0 should verify: got {result:?}"
    );
}

// ============================================================================
// Test 3: Multiple distinct NonZero types
// ============================================================================

/// Two distinct NonZero types with different invariant shapes.
///
/// Models:
/// ```rust
/// #[invariant(self.0@ > 0)]
/// struct NonZeroU32(u32);
///
/// #[invariant(self.0@ > 0)]
/// struct NonZeroU64(u64);
///
/// fn widen(x: NonZeroU32) -> NonZeroU64 {
///     NonZeroU64(x.0 as u64)
/// }
/// ```
///
/// Both types have `self > 0` invariants, but with different qualified
/// method names. The widening conversion preserves the invariant.
#[test]
#[timeout(30000)]
fn test_two_nonzero_types_widening() {
    let inv_u32 = trust_wp_core::logic::type_invariant_method_name("NonZeroU32");
    let inv_u64 = trust_wp_core::logic::type_invariant_method_name("NonZeroU64");

    let u32_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroU32".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    let u64_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroU64".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant_u32()
    let req = method_call(var("x"), &inv_u32, vec![]);

    // ensures: result.invariant_u64()
    let ens = method_call(var("result"), &inv_u64, vec![]);

    // body: result = x (widening cast is identity in unbounded SMT integers)
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[u32_def, u64_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "NonZeroU32 -> NonZeroU64 widening should preserve invariant: got {result:?}"
    );
}

/// Negative test: cross-type invariant without matching method is unconstrained.
///
/// If x has NonZeroU32 invariant but result requires NonZeroU64 invariant,
/// and body returns -1, the NonZeroU32 invariant on x does not help.
#[test]
#[timeout(30000)]
fn test_two_nonzero_types_unrelated_fails() {
    let inv_u32 = trust_wp_core::logic::type_invariant_method_name("NonZeroU32");
    let inv_u64 = trust_wp_core::logic::type_invariant_method_name("NonZeroU64");

    let u32_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroU32".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    let u64_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroU64".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant_u32()
    let req = method_call(var("x"), &inv_u32, vec![]);

    // ensures: result.invariant_u64()
    let ens = method_call(var("result"), &inv_u64, vec![]);

    // body: result = -1 (violates NonZeroU64 invariant regardless of x)
    let body = int(-1);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[u32_def, u64_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "returning -1 should fail NonZeroU64 invariant: got {result:?}"
    );
}

// ============================================================================
// Test 4: NonZero invariant with `ne` shape (self != 0)
// ============================================================================

/// Type invariant with `ne` (not-equals) shape: `self != 0` — pass-through.
///
/// This is a weaker invariant than `self > 0` — it allows negative values.
/// Tests that the `ne`-shape invariant encoding works for a simple pass-through
/// function (body returns the input unchanged).
///
/// NOTE: The direct multiplication test (`x!=0 && y!=0 => x*y!=0`) is
/// mathematically correct but ay-dpll cannot terminate on this nonlinear
/// problem within any reasonable timeout. The hard timeout interrupt
/// mechanism does not reliably kill ay's internal solver threads for
/// nonlinear arithmetic. We test the `ne` invariant shape with a
/// pass-through body instead, and test multiplication with the `gt`
/// shape (see `test_nonzero_mul_preserves_invariant`).
#[test]
#[timeout(30000)]
fn test_ne_zero_invariant_pass_through() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZeroSigned");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroSigned".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: ne(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant() (x != 0)
    let req_x = method_call(var("x"), &inv_method, vec![]);

    // ensures: result.invariant() (result != 0)
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = x (pass-through preserves ne(0) invariant)
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_x], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x!=0 pass-through should verify result!=0: got {result:?}"
    );
}

/// Type invariant with `ne` (not-equals) shape: negation preserves ne(0).
///
/// If `x != 0`, then `-x != 0` (in unbounded integer arithmetic).
/// This is a linear property that ay can handle, unlike multiplication.
#[test]
#[timeout(30000)]
fn test_ne_zero_invariant_preserved_by_negation() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZeroSigned");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroSigned".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: ne(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant() (x != 0)
    let req_x = method_call(var("x"), &inv_method, vec![]);

    // ensures: result.invariant() (result != 0)
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = -x (negation preserves non-zero)
    let body = neg(var("x"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_x], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x!=0 negation should verify result!=0: got {result:?}"
    );
}

/// Negative: `ne(0)` invariant NOT preserved by addition.
///
/// x != 0 and y != 0 does NOT imply x + y != 0 (counterexample: x=1, y=-1).
#[test]
#[timeout(30000)]
fn test_ne_zero_invariant_not_preserved_by_add() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZeroSigned");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroSigned".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: ne(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant() && y.invariant()
    let req_x = method_call(var("x"), &inv_method, vec![]);
    let req_y = method_call(var("y"), &inv_method, vec![]);

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = x + y
    let body = add(var("x"), var("y"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_x, req_y], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "x!=0 + y!=0 does NOT imply result!=0 (x=1,y=-1 is cex): got {result:?}"
    );
}

// ============================================================================
// Test 5: Open inv result — postcondition suppression
// ============================================================================

/// When the result invariant postcondition is omitted (simulating
/// `#[open_inv_result]`), the function body can return a value that
/// violates the invariant.
///
/// This tests the ay-level semantics: without an ensures clause for
/// the invariant, the solver does not check it on the result.
#[test]
#[timeout(30000)]
fn test_open_inv_result_allows_invariant_violation_on_result() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant() (x > 0)
    let req = method_call(var("x"), &inv_method, vec![]);

    // ensures: result == 0 (intentionally violating the invariant)
    // With open_inv_result, no result.invariant() postcondition is injected,
    // so this should verify (body returns 0, postcondition says result == 0).
    let ens = eq(var("result"), int(0));

    // body: result = 0
    let body = int(0);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Without result invariant postcondition (open_inv_result), returning 0 should verify: got {result:?}"
    );
}

/// Contrast: same function WITH result invariant postcondition fails.
#[test]
#[timeout(30000)]
fn test_closed_inv_result_rejects_invariant_violation() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant()
    let req = method_call(var("x"), &inv_method, vec![]);

    // ensures: result == 0 AND result.invariant()
    // The invariant postcondition (result > 0) contradicts result == 0.
    let ens_eq = eq(var("result"), int(0));
    let ens_inv = method_call(var("result"), &inv_method, vec![]);

    // body: result = 0
    let body = int(0);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens_eq, ens_inv])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "With result invariant postcondition, returning 0 should fail: got {result:?}"
    );
}

// ============================================================================
// Test 6: Chained arithmetic preservation
// ============================================================================

/// Chained arithmetic: (a + b) * c preserves NonZero when all are positive.
///
/// With a > 0, b > 0, c > 0:
/// - a + b > 0 (sum of positives)
/// - (a + b) * c > 0 (product of positives)
///
/// This tests invariant preservation through a compound expression.
#[test]
#[timeout(30000)]
fn test_nonzero_chained_arithmetic() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: a.invariant() && b.invariant() && c.invariant()
    let req_a = method_call(var("a"), &inv_method, vec![]);
    let req_b = method_call(var("b"), &inv_method, vec![]);
    let req_c = method_call(var("c"), &inv_method, vec![]);

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = (a + b) * c
    let body = mul(add(var("a"), var("b")), var("c"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_a, req_b, req_c], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "(a+b)*c with all positive should verify: got {result:?}"
    );
}

/// Linear chained arithmetic: a + b + c preserves NonZero (no multiplication).
///
/// With a > 0, b > 0, c > 0, the sum a + b + c > 0 is purely linear
/// and ay should verify definitively.
#[test]
#[timeout(30000)]
fn test_nonzero_chained_add_preserves_invariant() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: a.invariant() && b.invariant() && c.invariant()
    let req_a = method_call(var("a"), &inv_method, vec![]);
    let req_b = method_call(var("b"), &inv_method, vec![]);
    let req_c = method_call(var("c"), &inv_method, vec![]);

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = a + b + c
    let body = add(add(var("a"), var("b")), var("c"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_a, req_b, req_c], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "a+b+c with all positive should verify result>0: got {result:?}"
    );
}

/// Negative: chained arithmetic (a - b) * c does NOT preserve NonZero
/// without additional precondition.
///
/// Counterexample: a=1, b=2, c=1 gives (1-2)*1 = -1 < 0.
#[test]
#[timeout(30000)]
fn test_nonzero_chained_sub_mul_fails() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: a.invariant() && b.invariant() && c.invariant()
    let req_a = method_call(var("a"), &inv_method, vec![]);
    let req_b = method_call(var("b"), &inv_method, vec![]);
    let req_c = method_call(var("c"), &inv_method, vec![]);

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = (a - b) * c
    let body = mul(sub(var("a"), var("b")), var("c"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_a, req_b, req_c], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "(a-b)*c can be negative when b>a: got {result:?}"
    );
}
