// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
use std::collections::HashMap;

use ntest::timeout;

use super::*;
// --- Type invariant tests through verify_mut_borrow_function (#359) ---
/// Test type invariant preservation through mutable borrow: increment preserves NonZero.
///
/// Models:
/// ```rust
/// #[invariant(self.0 > 0)]
/// struct NonZero(i32);
///
/// #[requires((*x).invariant())]
/// #[ensures((^x).invariant())]
/// fn increment_nonzero(x: &mut NonZero) {
///     x.0 += 1;
/// }
/// ```
///
/// The body axiom `invariant(self) = (self > 0)` lets the solver conclude:
/// - *x > 0 (from precondition + axiom)
/// - ^x = *x + 1 (from body)
/// - ^x > 0 (from *x > 0 and +1)
/// - (^x).invariant() holds (from axiom applied to ^x)
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_type_invariant_preservation() {
    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None, // Int
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: (*x).invariant()
    let req = method_call(
        deref(var("x")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // ensures: (^x).invariant()
    let ens = method_call(
        final_expr(var("x")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // body: x_final = *x + 1
    let body_expr = add(deref(var("x")), int(1));
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), body_expr);

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[req], &[ens], &final_values).type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "increment_nonzero should preserve type invariant through mut borrow: got {result:?}"
    );
}
/// Negative test: mutation breaks type invariant through mutable borrow.
///
/// Models:
/// ```rust
/// #[invariant(self.0 > 0)]
/// struct NonZero(i32);
///
/// #[requires((*x).invariant())]
/// #[ensures((^x).invariant())]
/// fn set_zero(x: &mut NonZero) {
///     x.0 = 0;
/// }
/// ```
///
/// Body sets x_final = 0, so (^x).invariant() fails because 0 is not > 0.
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_type_invariant_violation() {
    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: (*x).invariant()
    let req = method_call(
        deref(var("x")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // ensures: (^x).invariant()
    let ens = method_call(
        final_expr(var("x")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // body: x_final = 0 (violates invariant)
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), int(0));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[req], &[ens], &final_values).type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "set_zero should violate type invariant through mut borrow: got {result:?}"
    );
}
/// Test type invariant without body axiom: invariant is uninterpreted, proof fails.
///
/// Same contract as `test_verify_mut_borrow_type_invariant_preservation` but
/// without passing the TypeInvariantDef. Without the body axiom, the solver
/// has no way to connect (*x).invariant() to (^x).invariant() even though
/// the body is x_final = *x + 1.
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_type_invariant_no_axiom_fails() {
    // requires: (*x).invariant()
    let req = method_call(
        deref(var("x")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // ensures: (^x).invariant()
    let ens = method_call(
        final_expr(var("x")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // body: x_final = *x + 1
    let body_expr = add(deref(var("x")), int(1));
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), body_expr);

    // No type_invariants -- invariant() is uninterpreted
    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[req], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Without body axiom, invariant preservation should produce Failed (invariant() is \
         uninterpreted UF, solver finds counterexample): got {result:?}"
    );
}
/// Test type invariant with return value through mutable borrow.
///
/// Models:
/// ```rust
/// #[invariant(self.0 > 0)]
/// struct NonZero(i32);
///
/// #[requires((*x).invariant())]
/// #[ensures((^x).invariant())]
/// #[ensures(result == old(*x))]
/// fn replace_nonzero(x: &mut NonZero, new_val: NonZero) -> NonZero {
///     let old = *x;
///     *x = new_val;
///     old
/// }
/// ```
///
/// The precondition gives us (*x).invariant() and new_val.invariant()
/// (auto-injected). Body: x_final = new_val, return = *x.
/// Post: (^x).invariant() holds because ^x = new_val and new_val.invariant().
/// result == old(*x) holds because return expression is *x.
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_type_invariant_with_return() {
    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: (*x).invariant() && new_val.invariant() (models auto-injection at call site)
    let req_inv = method_call(
        deref(var("x")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );
    let req_new_val = method_call(
        var("new_val"),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // ensures: (^x).invariant() && result == old(*x)
    let ens_inv = method_call(
        final_expr(var("x")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );
    let ens_result = eq(var("result"), old(deref(var("x"))));

    // body: x_final = new_val
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), var("new_val"));

    // return_expr: *x (the old value)
    let return_expr = deref(var("x"));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(
            &[req_inv, req_new_val],
            &[ens_inv, ens_result],
            &final_values,
        )
        .return_expr(Some(&return_expr))
        .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "replace_nonzero with type invariant and return should verify: got {result:?}"
    );
}
/// Test NonZero addition preserves invariant through mutable borrow (Creusot non_zero.rs).
///
/// Models:
/// ```rust
/// #[invariant(self.0 > 0)]
/// struct NonZero(i32);
///
/// #[requires((*a).invariant())]
/// #[requires((*a) <= i32::MAX - (*b))] // no overflow
/// #[ensures((^a).invariant())]
/// fn add_nonzero(a: &mut NonZero, b: NonZero) {
///     a.0 += b.0;
/// }
/// ```
///
/// With body axiom: *a > 0 (from precondition), b > 0 (from b.invariant()),
/// ^a = *a + b, so ^a > 0. No overflow is guaranteed by precondition.
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_nonzero_add_preserves_invariant() {
    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: (*a).invariant()
    let req_a = method_call(
        deref(var("a")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );
    // requires: b.invariant() (auto-injected for non-primitive parameter)
    let req_b = method_call(
        var("b"),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // ensures: (^a).invariant()
    let ens = method_call(
        final_expr(var("a")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // body: a_final = *a + b
    let body_expr = add(deref(var("a")), var("b"));
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), body_expr);

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[req_a, req_b], &[ens], &final_values)
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "NonZero add should preserve invariant (*a > 0, b > 0 => ^a = *a + b > 0): got {result:?}"
    );
}
/// Negative test: NonZero subtraction may break invariant.
///
/// Models:
/// ```rust
/// #[invariant(self.0 > 0)]
/// struct NonZero(i32);
///
/// #[requires((*a).invariant())]
/// #[ensures((^a).invariant())]
/// fn sub_nonzero(a: &mut NonZero, b: NonZero) {
///     a.0 -= b.0; // WRONG: if b >= a, result <= 0
/// }
/// ```
///
/// Without the additional precondition `*a > b`, the subtraction can produce 0
/// or negative values that violate the invariant.
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_nonzero_sub_breaks_invariant() {
    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: (*a).invariant() && b.invariant()
    let req_a = method_call(
        deref(var("a")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );
    let req_b = method_call(
        var("b"),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // ensures: (^a).invariant()
    let ens = method_call(
        final_expr(var("a")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // body: a_final = *a - b (may be <= 0 when b >= *a)
    let body_expr = sub(deref(var("a")), var("b"));
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), body_expr);

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[req_a, req_b], &[ens], &final_values)
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "NonZero sub without sufficient precondition should fail (counterexample: b >= *a): got {result:?}"
    );
}
/// Test swapping two &mut NonZero values preserves both invariants.
///
/// Models:
/// ```rust
/// #[invariant(self.0 > 0)]
/// struct NonZero(i32);
///
/// #[requires((*a).invariant())]
/// #[requires((*b).invariant())]
/// #[ensures((^a).invariant())]
/// #[ensures((^b).invariant())]
/// fn swap_nonzero(a: &mut NonZero, b: &mut NonZero) {
///     let t = *a;
///     *a = *b;
///     *b = t;
/// }
/// ```
///
/// Both initial values satisfy the invariant. After swap, ^a = *b (invariant)
/// and ^b = *a (invariant). The body axiom connects the final values to the
/// invariant predicate.
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_swap_nonzero_preserves_invariant() {
    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: (*a).invariant() && (*b).invariant()
    let req_a = method_call(
        deref(var("a")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );
    let req_b = method_call(
        deref(var("b")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // ensures: (^a).invariant() && (^b).invariant()
    let ens_a = method_call(
        final_expr(var("a")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );
    let ens_b = method_call(
        final_expr(var("b")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // body: a_final = *b, b_final = *a (swap)
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), deref(var("b")));
    final_values.insert("b".to_string(), deref(var("a")));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[req_a, req_b], &[ens_a, ens_b], &final_values)
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "swap_nonzero should preserve both invariants: got {result:?}"
    );
}
/// Negative test: swapping NonZero with an unconstrained source breaks invariant.
///
/// Models the case where only one parameter has its invariant in the precondition,
/// so the other's final value is not guaranteed to satisfy the invariant.
///
/// ```rust
/// #[requires((*a).invariant())]
/// // MISSING: #[requires((*b).invariant())]
/// #[ensures((^a).invariant())]
/// #[ensures((^b).invariant())]
/// fn swap_nonzero_partial(a: &mut NonZero, b: &mut NonZero) {
///     let t = *a;
///     *a = *b;
///     *b = t; // ^a = *b but *b may not be > 0
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_verify_mut_borrow_swap_nonzero_partial_precondition_fails() {
    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: only (*a).invariant() -- missing (*b).invariant()
    let req_a = method_call(
        deref(var("a")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // ensures: (^a).invariant() && (^b).invariant()
    let ens_a = method_call(
        final_expr(var("a")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );
    let ens_b = method_call(
        final_expr(var("b")),
        &trust_wp_core::logic::type_invariant_method_name("NonZero"),
        vec![],
    );

    // body: a_final = *b, b_final = *a
    let mut final_values = HashMap::new();
    final_values.insert("a".to_string(), deref(var("b")));
    final_values.insert("b".to_string(), deref(var("a")));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[req_a], &[ens_a, ens_b], &final_values)
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "swap with partial precondition should fail (^a = *b, but *b unconstrained): got {result:?}"
    );
}
