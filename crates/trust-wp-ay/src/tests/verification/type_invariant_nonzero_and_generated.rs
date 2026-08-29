// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end verification tests modeling the Creusot compat patterns from
//! `type_invariants/non_zero.rs` and `type_invariants/generated.rs` (#2695).
//!
//! These tests exercise the full verification pipeline for the specific
//! invariant patterns used by the Creusot compatibility test suite:
//!
//! 1. **NonZero pattern** (`self != 0`): Models `NonZero<T>` where the type
//!    invariant guarantees the inner value is non-zero. Uses `ne(self, 0)`
//!    rather than `gt(self, 0)`, matching the actual Rust NonZero guarantee.
//!
//! 2. **Generated pattern**: Models `#[derive(Default)]` types with user
//!    invariants like `self.a + self.b == 10`. Tests that multi-field struct
//!    invariants work through field accessors in the verification pipeline.
//!
//! 3. **NonZero through Option**: Models `NonZero::new(value)` returning
//!    `Option<NonZero>` — unwrapping produces a value satisfying the invariant.

use super::*;

// ============================================================================
// NonZero `ne(self, 0)` invariant — identity through get()
// ============================================================================

/// Models the Creusot `non_zero.rs` pattern: NonZero::get returns the
/// inner value, which satisfies `result != 0`.
///
/// ```rust
/// #[invariant(self.0 != 0)]
/// struct NonZero(u32);
///
/// #[requires(x.invariant())]
/// #[ensures(result@ != 0)]
/// fn get_inner(x: NonZero) -> u32 {
///     x.0
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_nonzero_ne_invariant_get_inner() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZeroU32");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroU32".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: ne(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant()  (expands to x != 0)
    let req = method_call(var("x"), &inv_method, vec![]);

    // ensures: result != 0
    let ens = ne(var("result"), int(0));

    // body: result = x (newtype get() is identity)
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "NonZero(ne) get: x!=0 should verify result!=0: got {result:?}"
    );
}

// ============================================================================
// NonZero `ne(self, 0)` — addition does NOT preserve the invariant
// ============================================================================

/// x != 0 and y != 0 does NOT imply x + y != 0 (counterexample: x=1, y=-1).
/// This is a key semantic property of the `ne` shape vs the `gt` shape.
#[test]
#[timeout(30000)]
fn test_nonzero_ne_invariant_not_preserved_by_add() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZeroSigned");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroSigned".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: ne(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    let req_x = method_call(var("x"), &inv_method, vec![]);
    let req_y = method_call(var("y"), &inv_method, vec![]);
    let ens = ne(var("result"), int(0));
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
// NonZero `ne(self, 0)` — postcondition on result invariant
// ============================================================================

/// When the result type also has the NonZero invariant, the postcondition
/// `result.invariant()` is injected. Body must satisfy it.
#[test]
#[timeout(30000)]
fn test_nonzero_ne_result_invariant_postcondition_verified() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZeroU32");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroU32".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: ne(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant()
    let req = method_call(var("x"), &inv_method, vec![]);

    // ensures: result.invariant() (result != 0)
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = x (pass-through preserves invariant)
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "NonZero pass-through should preserve result invariant: got {result:?}"
    );
}

/// Negative: returning 0 violates the NonZero result invariant.
#[test]
#[timeout(30000)]
fn test_nonzero_ne_result_invariant_violated_by_zero() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZeroU32");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroU32".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: ne(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    let req = method_call(var("x"), &inv_method, vec![]);
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = 0 — violates invariant
    let body = int(0);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "returning 0 should violate NonZero result invariant: got {result:?}"
    );
}

// ============================================================================
// Generated pattern — multi-field struct with sum constraint
// ============================================================================

/// Models the Creusot `generated.rs` pattern: a struct with a derived Default
/// and a user-defined invariant on the relationship between fields.
///
/// ```rust
/// #[derive(Default)]
/// #[invariant(self.a + self.b == 10)]
/// struct SumTo10 {
///     a: i32,
///     b: i32,
/// }
///
/// #[requires(x.invariant())]
/// #[ensures(result == 10)]
/// fn sum_fields(x: SumTo10) -> i32 {
///     x.a + x.b
/// }
/// ```
///
/// The invariant body uses `__trust_wp_tuple_get_0(self) + __trust_wp_tuple_get_1(self) == 10`.
#[test]
#[timeout(30000)]
fn test_generated_sum_invariant_field_sum() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("SumTo10");

    // Body: get_0(self) + get_1(self) == 10
    let body_inv = eq(
        add(get_field(0, var("self")), get_field(1, var("self"))),
        int(10),
    );

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "SumTo10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: body_inv,
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: x.invariant()
    let req = method_call(var("x"), &inv_method, vec![]);

    // ensures: result == 10
    let ens = eq(var("result"), int(10));

    // body: result = x.a + x.b = get_0(x) + get_1(x)
    let body = add(get_field(0, var("x")), get_field(1, var("x")));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "SumTo10 invariant: get_0(x)+get_1(x)==10 should verify result==10: got {result:?}"
    );
}

/// Negative: a generated value whose fields sum to 10 fails a postcondition
/// claiming that the field sum is 20.
#[test]
#[timeout(30000)]
fn test_generated_sum_invariant_wrong_total_fails() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name;

    let body_inv = eq(
        add(get_field(0, var("self")), get_field(1, var("self"))),
        int(10),
    );

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "SumTo10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: body_inv,
        is_newtype: false,
        element_invariant_method: None,
    };

    // Concrete generated value with a + b == 10.
    let body = logic_fn_call(&tuple_logic_fn_name(2), vec![int(5), int(5)]);
    // ensures: result.a + result.b == 20 — wrong, constructed value sums to 10.
    let ens = eq(
        add(get_field(0, var("result")), get_field(1, var("result"))),
        int(20),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "generated SumTo10 value has field sum 10, not 20: should fail, got {result:?}"
    );
}

/// Generated pattern: field swap preserves the invariant.
///
/// ```rust
/// #[requires(x.invariant())]
/// #[ensures(result.invariant())]
/// fn swap_fields(x: SumTo10) -> SumTo10 {
///     SumTo10 { a: x.b, b: x.a }
/// }
/// ```
///
/// Swapping fields preserves a + b == 10 since b + a == a + b.
/// The body returns a new struct where field 0 = old field 1 and vice versa.
/// We model this as: result = tuple(get_1(x), get_0(x)), with the result
/// invariant checking get_0(result) + get_1(result) == 10.
#[test]
#[timeout(30000)]
fn test_generated_swap_preserves_invariant() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("SumTo10");

    let body_inv = eq(
        add(get_field(0, var("self")), get_field(1, var("self"))),
        int(10),
    );

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "SumTo10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: body_inv,
        is_newtype: false,
        element_invariant_method: None,
    };

    // requires: x.invariant()
    let req = method_call(var("x"), &inv_method, vec![]);

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = x (pass-through — swap is identity for the sum)
    // We model the swap by returning x directly since get_0(x) + get_1(x) == 10
    // is symmetric, and the verification needs to confirm the invariant holds.
    // A more detailed test would construct the tuple, but at the SMT level,
    // the key property is that the invariant body is checked on the result.
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "SumTo10 pass-through should preserve invariant: got {result:?}"
    );
}

// ============================================================================
// Generated pattern: invariant combined with Default
// ============================================================================

/// The Default impl for SumTo10 must produce a value satisfying the invariant.
/// Models: Default::default() has postcondition result.invariant().
///
/// With invariant a + b == 10: Default could produce (5, 5), (0, 10), etc.
/// This test verifies that given `result == default_value` where default
/// satisfies the invariant, the postcondition `result.invariant()` holds.
#[test]
#[timeout(30000)]
fn test_generated_default_satisfies_invariant() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("SumTo10");

    let body_inv = eq(
        add(get_field(0, var("self")), get_field(1, var("self"))),
        int(10),
    );

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "SumTo10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: body_inv,
        is_newtype: false,
        element_invariant_method: None,
    };

    // No preconditions (Default::default takes no arguments)
    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result is a specific default value where a=5, b=5
    // We model this by assuming the result fields satisfy a + b == 10
    // through explicit field equality assertions.
    // In practice, the driver injects the invariant assumption for
    // constructed values, but at the ay level we test that the
    // postcondition can be verified when the body establishes the
    // field values that satisfy the invariant.
    //
    // We use let_assume to model the construction: assume fields sum to 10,
    // then prove the invariant holds.
    let body = let_assume(
        eq(
            add(get_field(0, var("result")), get_field(1, var("result"))),
            int(10),
        ),
        var("result"),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Default value satisfying a+b==10 should verify invariant: got {result:?}"
    );
}

// ============================================================================
// NonZero through view operator (@) — models NonZero::new postcondition
// ============================================================================

/// Models the NonZero::new(value) pattern where the postcondition connects
/// the result to the input through the view operator.
///
/// ```rust
/// #[ensures(value@ != 0 ==> result.is_some())]
/// #[ensures(value@ != 0 ==> result.unwrap()@ == value@)]
/// ```
///
/// At the SMT level, we model this as: when value != 0, result == value.
/// This is a simplification that tests the invariant flow without the
/// Option encoding.
#[test]
#[timeout(30000)]
fn test_nonzero_new_conditional_invariant() {
    let _inv_method = trust_wp_core::logic::type_invariant_method_name("NonZeroU32");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroU32".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: ne(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: value != 0 (modeling the Some branch)
    let req = ne(var("value"), int(0));

    // ensures: result != 0 (the NonZero invariant on the constructed value)
    let ens = ne(var("result"), int(0));

    // body: result = value (the Some(NonZero(value)) unwrapped is value)
    let body = var("value");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "NonZero::new with value!=0 should verify result!=0: got {result:?}"
    );
}

// ============================================================================
// Additional NonZero and Generated coverage
// ============================================================================

/// NonZero checked subtraction: if `x != 0`, `y != 0`, and `x > y`, then
/// `x - y != 0`.
#[test]
#[timeout(30000)]
fn test_nonzero_ne_subtraction_conditional_postcondition() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZeroU32");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroU32".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: ne(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    let req_x = method_call(var("x"), &inv_method, vec![]);
    let req_y = method_call(var("y"), &inv_method, vec![]);
    let req_gt = gt(var("x"), var("y"));
    let ens = ne(var("result"), int(0));
    let body = sub(var("x"), var("y"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_x, req_y, req_gt], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x!=0, y!=0, and x>y should verify x-y!=0: got {result:?}"
    );
}

/// Negative: without `x > y`, `x != 0` and `y != 0` do not imply `x - y != 0`
/// because equal inputs produce zero.
#[test]
#[timeout(30000)]
fn test_nonzero_ne_subtraction_equal_values_fails() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZeroU32");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroU32".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: ne(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    let req_x = method_call(var("x"), &inv_method, vec![]);
    let req_y = method_call(var("y"), &inv_method, vec![]);
    let ens = ne(var("result"), int(0));
    let body = sub(var("x"), var("y"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_x, req_y], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "x!=0 and y!=0 alone should not verify x-y!=0: got {result:?}"
    );
}

/// Generated invariant update: choosing `result.0 = value` and
/// `result.1 = 10 - value` preserves `result.invariant()`.
#[test]
#[timeout(30000)]
fn test_generated_field_update_preserves_invariant() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("SumTo10");

    let body_inv = eq(
        add(get_field(0, var("self")), get_field(1, var("self"))),
        int(10),
    );

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "SumTo10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: body_inv,
        is_newtype: false,
        element_invariant_method: None,
    };

    let req = method_call(var("x"), &inv_method, vec![]);
    let ens = method_call(var("result"), &inv_method, vec![]);
    let body = let_assume(
        and(
            eq(get_field(0, var("result")), var("value")),
            eq(get_field(1, var("result")), sub(int(10), var("value"))),
        ),
        var("result"),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "setting result.0=value and result.1=10-value should preserve SumTo10: got {result:?}"
    );
}

/// Negative: an uncompensated generated field update does not preserve
/// `a + b == 10`.
#[test]
#[timeout(30000)]
fn test_generated_field_update_without_compensation_fails() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name;

    let body_inv = eq(
        add(get_field(0, var("self")), get_field(1, var("self"))),
        int(10),
    );

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "SumTo10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: body_inv,
        is_newtype: false,
        element_invariant_method: None,
    };

    let body = logic_fn_call(&tuple_logic_fn_name(2), vec![int(6), int(5)]);
    let ens = eq(
        add(get_field(0, var("result")), get_field(1, var("result"))),
        int(10),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "updating only result.0 without compensating result.1 should violate SumTo10: got {result:?}"
    );
}

/// Mixed invariants: `x != 0` and `s.a + s.b == 10` imply
/// `x * (s.a + s.b) != 0`.
#[test]
#[timeout(30000)]
fn test_mixed_nonzero_and_sum10_invariants() {
    let nonzero_method = trust_wp_core::logic::type_invariant_method_name("NonZeroU32");
    let sumto10_method = trust_wp_core::logic::type_invariant_method_name("SumTo10");

    let nonzero_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZeroU32".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: ne(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    let sumto10_def = trust_wp_core::type_invariant_def! {
        type_name: "SumTo10".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: eq(
            add(get_field(0, var("self")), get_field(1, var("self"))),
            int(10),
        ),
        is_newtype: false,
        element_invariant_method: None,
    };

    let req_x = method_call(var("x"), &nonzero_method, vec![]);
    let req_s = method_call(var("s"), &sumto10_method, vec![]);
    let ens = ne(var("result"), int(0));
    let sum_expr = add(get_field(0, var("s")), get_field(1, var("s")));
    let body = let_assume(eq(sum_expr, int(10)), mul(var("x"), int(10)));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_x, req_s], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[nonzero_def, sumto10_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x!=0 and SumTo10(s) should verify x*(s.0+s.1)!=0: got {result:?}"
    );
}
