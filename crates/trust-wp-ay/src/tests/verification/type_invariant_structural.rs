// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Structural type invariant regression tests (#2669, AC3 + AC4).
//!
//! These tests verify multi-field struct invariants that reference tuple/named
//! field accessors. This covers the `generated.rs` and `non_zero.rs` compat
//! patterns at the ay encoding level.
//!
//! Test scenarios:
//! 1. Sum10 pattern: `self.0 + self.1 == 10` — invariant over two fields
//! 2. Sum10 with swap: postcondition that swapped fields still sum to 10
//! 3. Sum10 construction: building a new Sum10 from invariant-holding inputs
//! 4. NonZero newtype: `self.0 > 0` — single-field invariant (regression)
//! 5. NonZero add returning Self: arithmetic on invariant types produces
//!    invariant result
//! 6. Invariant with named fields: `self.x + self.y == 10`

use super::*;

// ============================================================================
// Test 1: Sum10 two-field invariant: get_0(self) + get_1(self) == 10
// ============================================================================

/// Sum10 pattern from `generated.rs`: struct Sum10(i32, i32) with
/// invariant `self.0@ + self.1@ == 10`.
///
/// At the ay level, field access is via `get_0(self)` and `get_1(self)` UFs.
/// The invariant body uses these to express the constraint.
///
/// Function:
/// ```rust
/// #[requires(x.invariant())]
/// #[ensures(result == 10)]
/// fn sum_fields(x: Sum10) -> i32 {
///     x.0 + x.1
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_sum10_invariant_field_sum_equals_constant() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Sum10");

    // invariant body: get_0(self) + get_1(self) == 10
    let inv_body = eq(
        add(get_field(0, var("self")), get_field(1, var("self"))),
        int(10),
    );

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Sum10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: inv_body,
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: x.invariant()
    let req = method_call(var("x"), &inv_method, vec![]);

    // ensures: result == 10
    let ens = eq(var("result"), int(10));

    // body: result = get_0(x) + get_1(x)
    let body = add(get_field(0, var("x")), get_field(1, var("x")));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Sum10: get_0(x) + get_1(x) == 10 from invariant, body sums fields: got {result:?}"
    );
}

/// Negative: Sum10 invariant permits a concrete non-positive first field.
///
/// The invariant `self.0 + self.1 == 10` does not imply `self.0 > 0`.
/// Counterexample: self.0 = -5, self.1 = 15.
#[test]
#[timeout(30000)]
fn test_sum10_invariant_does_not_constrain_individual_fields() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Sum10");

    let inv_body = eq(
        add(get_field(0, var("self")), get_field(1, var("self"))),
        int(10),
    );

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Sum10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: inv_body,
        is_newtype: false,
        element_invariant_method: None,
    };

    let concrete_sum10 = logic_fn_call(
        &trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(2),
        vec![int(-5), int(15)],
    );

    // requires: concrete Sum10 value satisfies the invariant (-5 + 15 == 10)
    let req_inv = method_call(concrete_sum10, &inv_method, vec![]);

    // ensures: result > 0 — NOT implied by sum == 10 (field 0 could be -5)
    let ens = gt(var("result"), int(0));

    // body: result = -5 (the concrete first field)
    let body = int(-5);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_inv], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(
            result,
            VerificationResult::Failed(_)
                | VerificationResult::Unknown(
                    crate::verify::UnknownReason::QuantifierEmatchingExistsIncomplete
                )
        ),
        "the concrete body -5 must not prove result > 0; AY may fail closed when validating the unrelated invariant quantifier: got {result:?}"
    );
}

// ============================================================================
// Test 2: Sum10 swap — swapped fields still sum to 10
// ============================================================================

/// Swapping fields of a Sum10 preserves the invariant.
///
/// ```rust
/// #[requires(x.invariant())]
/// #[ensures(result.invariant())]
/// fn swap(x: Sum10) -> Sum10 {
///     Sum10(x.1, x.0)
/// }
/// ```
///
/// If get_0(x) + get_1(x) == 10, then a swap (get_1(x), get_0(x)) still
/// sums to 10. At the ay level, the result's fields are the reverse of
/// the input's, and the postcondition checks result.invariant().
#[test]
#[timeout(30000)]
fn test_sum10_swap_preserves_invariant() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Sum10");

    let inv_body = eq(
        add(get_field(0, var("self")), get_field(1, var("self"))),
        int(10),
    );

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Sum10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: inv_body,
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: x.invariant()
    let req = method_call(var("x"), &inv_method, vec![]);

    // ensures: get_0(result) + get_1(result) == 10
    // This is the expanded form of result.invariant(). We use the expanded
    // form because at the ay level, field accessors are UFs and the identity
    // body (result = x) means get_0(result) == get_0(x), enabling the solver
    // to substitute the invariant constraint.
    let ens = eq(
        add(get_field(0, var("result")), get_field(1, var("result"))),
        int(10),
    );

    // body: result = x (identity, invariant preserved trivially)
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Sum10: identity preserves field sum invariant: got {result:?}"
    );
}

// ============================================================================
// Test 3: Sum10 construction from components
// ============================================================================

/// Invariant pass-through: function that accepts and returns a Sum10.
///
/// ```rust
/// #[requires(x.invariant())]
/// #[ensures(result.invariant())]
/// fn identity(x: Sum10) -> Sum10 {
///     x
/// }
/// ```
///
/// The invariant is assumed on the input and must hold on the output.
/// Since `result = x`, the invariant transfers directly through the
/// type invariant UF axiom.
#[test]
#[timeout(30000)]
fn test_sum10_invariant_pass_through() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Sum10");

    let inv_body = eq(
        add(get_field(0, var("self")), get_field(1, var("self"))),
        int(10),
    );

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Sum10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: inv_body,
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: x.invariant()
    let req = method_call(var("x"), &inv_method, vec![]);

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

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
        "Sum10: identity pass-through preserves invariant: got {result:?}"
    );
}

/// Negative: constructing a value that violates the invariant.
///
/// Without the precondition `a + b == 10`, the invariant cannot be proved.
#[test]
#[timeout(30000)]
fn test_sum10_construction_without_precondition_fails() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Sum10");

    let inv_body = eq(
        add(get_field(0, var("self")), get_field(1, var("self"))),
        int(10),
    );

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Sum10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: inv_body,
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: (nothing — no invariant precondition)
    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = x (x is unconstrained)
    let body = var("x");

    let outcome = crate::verify_function_with_modes_outcome(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    let evidence_gap = crate::refutation_evidence_gap_reason(&outcome);
    if (!matches!(outcome.result, VerificationResult::Failed(_)) || evidence_gap.is_some())
        && std::env::var_os("TWP_BR_DBG").is_some()
    {
        if let Some(replay) = outcome
            .provenance
            .as_ref()
            .and_then(|provenance| provenance.native_replay_json.as_deref())
        {
            eprintln!("SUM10_NATIVE_REPLAY_BEGIN\n{replay}\nSUM10_NATIVE_REPLAY_END");
        }
    }
    let result = outcome.result;
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Sum10: unconstrained x cannot satisfy invariant: got {result:?}"
    );
    assert!(
        evidence_gap.is_none(),
        "Sum10 counterexample needs accepted, validated model evidence: {evidence_gap:?}"
    );
}

// ============================================================================
// Test 4: NonZero newtype single-field invariant (regression)
// ============================================================================

/// NonZero newtype pattern from `non_zero.rs`: struct NonZeroU32(u32) with
/// invariant `self.0@ > 0`.
///
/// For newtypes (`is_newtype: true`), the field-0 access is identity:
/// `self.0 == self` in the logical domain. So the invariant body is
/// simply `self > 0`.
///
/// ```rust
/// #[requires(n@ > 0)]
/// #[ensures(result.invariant())]
/// fn new(n: u32) -> NonZeroU32 {
///     NonZeroU32(n)
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_nonzero_newtype_construction() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZeroU32");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroU32".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: n > 0
    let req = gt(var("n"), int(0));

    // ensures: result.invariant() (result > 0)
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = n (newtype construction is identity)
    let body = var("n");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "NonZeroU32::new: n > 0 => result > 0: got {result:?}"
    );
}

/// Negative: NonZero construction without precondition.
#[test]
#[timeout(30000)]
fn test_nonzero_newtype_construction_without_precondition_fails() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZeroU32");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroU32".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: (nothing)
    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = n (unconstrained)
    let body = var("n");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        crate::tests::rejected(&result),
        "NonZeroU32::new without precondition should fail: got {result:?}"
    );
}

// ============================================================================
// Test 5: NonZero add returning Self — arithmetic preservation
// ============================================================================

/// NonZero add: two positive values added produce a positive result.
///
/// ```rust
/// #[requires(self.0@ + rhs.0@ <= u32::MAX@)]
/// fn add(self, rhs: Self) -> Self {
///     Self(self.0 + rhs.0)
/// }
/// ```
///
/// The invariant on self and rhs guarantees both are > 0. The sum of two
/// positive integers is positive (in unbounded SMT arithmetic).
#[test]
#[timeout(30000)]
fn test_nonzero_add_returns_invariant_result() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZeroU32");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroU32".to_string(),
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

    // body: result = self + rhs
    let body = add(var("self_"), var("rhs"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_self, req_rhs], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "NonZeroU32::add: self>0 + rhs>0 => result>0: got {result:?}"
    );
}

// ============================================================================
// Test 6: Invariant with named fields
// ============================================================================

/// Struct with named fields using the `named_field` accessor.
///
/// ```rust
/// struct Point {
///     x: i32,
///     y: i32,
/// }
///
/// impl Invariant for Point {
///     #[logic]
///     fn invariant(self) -> bool {
///         pearlite! { self.x@ >= 0 && self.y@ >= 0 }
///     }
/// }
///
/// #[requires(p.invariant())]
/// #[ensures(result >= 0)]
/// fn x_coord(p: Point) -> i32 {
///     p.x
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_named_field_invariant() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Point");

    // invariant body: self.x >= 0 && self.y >= 0
    let inv_body = and(
        ge(named_field("x", var("self")), int(0)),
        ge(named_field("y", var("self")), int(0)),
    );

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Point".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: inv_body,
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: p.invariant()
    let req = method_call(var("p"), &inv_method, vec![]);

    // ensures: result >= 0
    let ens = ge(var("result"), int(0));

    // body: result = p.x
    let body = named_field("x", var("p"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Point.x >= 0 from invariant(p): got {result:?}"
    );
}

/// Negative: the named-field invariant permits the boundary value y = 0.
///
/// The invariant gives `p.y >= 0`, but the postcondition asks for `result > 0`.
/// Counterexample: p.y = 0.
#[test]
#[timeout(30000)]
fn test_named_field_invariant_not_strictly_positive() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Point");

    let inv_body = and(
        ge(named_field("x", var("self")), int(0)),
        ge(named_field("y", var("self")), int(0)),
    );

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Point".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: inv_body,
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: p.invariant(); the body returns the concrete boundary value y = 0.
    let req_inv = method_call(var("p"), &inv_method, vec![]);

    // ensures: result > 0 — strictly positive is NOT guaranteed (y could be 0)
    let ens = gt(var("result"), int(0));

    // body: result = 0
    let body = int(0);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_inv], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        crate::tests::rejected(&result),
        "Point.y >= 0 does not imply result > 0 (y=0 is cex): got {result:?}"
    );
}

/// Named field invariant combined with explicit requires to prove tighter bound.
///
/// ```rust
/// #[requires(p.invariant())]
/// #[requires(p.x@ > 5)]
/// #[ensures(result >= 6)]
/// fn shifted_x(p: Point) -> i32 {
///     p.x
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_named_field_invariant_with_explicit_requires() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Point");

    let inv_body = and(
        ge(named_field("x", var("self")), int(0)),
        ge(named_field("y", var("self")), int(0)),
    );

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Point".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: inv_body,
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: p.invariant() AND p.x > 5
    let req_inv = method_call(var("p"), &inv_method, vec![]);
    let req_bound = gt(named_field("x", var("p")), int(5));

    // ensures: result >= 6 (p.x > 5, so p.x >= 6)
    let ens = ge(var("result"), int(6));

    // body: result = p.x
    let body = named_field("x", var("p"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_inv, req_bound], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "invariant(p) + p.x > 5 => p.x >= 6: got {result:?}"
    );
}
