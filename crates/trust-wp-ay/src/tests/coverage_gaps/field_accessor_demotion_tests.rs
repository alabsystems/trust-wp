// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the field accessor demotion exemption (#2316).
//!
//! Tuple field accessors (`__trust_wp_tuple_get_N`) and named field accessors
//! (`__trust_wp_field_*`) are exempted from `SortFallbackToIntFromLogicFn`
//! unsoundness demotion. These tests verify that:
//!
//! 1. The exemption doesn't produce false Verified for Bool-typed fields
//! 2. The exemption correctly allows verification of Int-typed fields
//! 3. Sort inference correctly classifies these as non-Bool-unknown

use ntest::timeout;

use super::*;
use crate::{
    encoder::unsoundness::{self, UnsoundnessCategory},
    verify_function_with_modes, VerificationRequest, VerificationResult,
};

fn sample_struct_adt_decls() -> trust_wp_core::logic::AdtDecls {
    use trust_wp_core::{
        formula::ExprSort,
        logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
    };

    std::collections::HashMap::from([(
        "Foo".to_string(),
        AdtDecl::new(
            "crate::Foo".to_string(),
            "Foo".to_string(),
            AdtKind::Struct,
            vec![AdtConstructorDecl::new(
                "Foo".to_string(),
                "Foo".to_string(),
                vec![AdtFieldDecl::new("val".to_string(), ExprSort::Int)],
            )],
        ),
    )])
}

/// Named field accessor on an Int field should verify without demotion when
/// ADT metadata is present.
///
/// Scenario: struct Foo { val: i32 }
///   requires: (none)
///   ensures: result == __trust_wp_field_val(x)
///   body: __trust_wp_field_val(x)
///
/// Under `#1982`, this path uses the native selector for `Foo::val`
/// rather than an untyped UF fallback. The body-binding identity
/// `result == field_val(x)` verifies directly. (#1982, #2316)
///
/// NOTE: Adding a precondition `field_val(x) > 0` triggers ay-dpll
/// "internal-error" at the current pin (likely a solver bug with
/// datatype selectors in precondition assertion contexts). This test
/// validates the encoding path without the precondition; the
/// precondition variant should be revisited after a ay bump.
#[test]
#[timeout(30000)]
fn field_accessor_int_field_verifies_without_demotion() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let foo_sort = ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("crate::Foo"));
    let x = var_with_sort("x", foo_sort);
    let field_val = named_field("val", x);
    let ensures = vec![eq(var("result"), field_val.clone())];
    let body = field_val.clone();

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .return_expr(Some(&body))
            .adt_decls(Some(sample_struct_adt_decls())),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "native Int field selector body binding should verify (result == field_val(x)): {result:?}"
    );

    // The exemption should prevent SortFallbackToIntFromLogicFn from firing
    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "Named field accessor should NOT increment SortFallbackToIntFromLogicFn. Delta: {delta:?}"
    );

    unsoundness::reset();
}

/// Tuple field accessor should also be exempt from demotion.
///
/// Scenario: result = tuple_get_0(tuple2(5, 10))
///   ensures: result == 5
///
/// The tuple_get_0 accessor should not trigger demotion.
#[test]
#[timeout(30000)]
fn tuple_field_accessor_exempt_from_demotion() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let tuple_val = logic_fn_call("__trust_wp_tuple2", vec![int(5), int(10)]);
    let field_0 = get_field(0, var("result"));
    let ensures = vec![eq(field_0, int(5))];

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).return_expr(Some(&tuple_val)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Tuple field accessor should verify with axioms: {result:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta
            .get(&UnsoundnessCategory::SortFallbackToIntFromLogicFn)
            .copied()
            .unwrap_or(0),
        0,
        "Tuple field accessor should NOT increment SortFallbackToIntFromLogicFn. Delta: {delta:?}"
    );

    unsoundness::reset();
}

/// Bool field used as standalone predicate must not produce false Verified.
///
/// Scenario: struct Foo { flag: bool }
///   requires: (none)
///   ensures: __trust_wp_field_flag(x)   [standalone Bool predicate]
///
/// Without any precondition, `field_flag(x)` is unconstrained. The
/// postcondition should NOT verify (there's no guarantee flag is true).
/// This tests that the Sort::Int encoding of Bool fields doesn't allow
/// false proofs via the demotion exemption.
#[test]
#[timeout(30000)]
fn bool_field_standalone_predicate_not_false_verified() {
    unsoundness::reset();

    let field_flag = named_field("flag", var("x"));
    let ensures = vec![field_flag];

    let result = verify_function_with_modes(VerificationRequest::new(&[], &ensures))
        .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Unconstrained Bool field predicate should fail. Got: {result:?}"
    );

    unsoundness::reset();
}

/// Bool field equality comparison is sound but may be incomplete.
///
/// Scenario:
///   requires: __trust_wp_field_flag(x) == true
///   ensures: __trust_wp_field_flag(result) == true
///   body: x (identity)
///
/// When flag is known to be true (precondition) and result = x,
/// the postcondition SHOULD verify via UF congruence. However, Bool
/// fields encoded as Int cause ay to return Unknown("incomplete")
/// because the Bool literal `true` vs Int encoding creates a coercion
/// gap that ay's E-matching cannot bridge. This is a COMPLETENESS
/// limitation, not a soundness issue.
#[test]
#[timeout(30000)]
fn bool_field_equality_with_precondition_sound() {
    unsoundness::reset();

    let x_flag = named_field("flag", var("x"));
    let result_flag = named_field("flag", var("result"));

    let requires = vec![eq(x_flag, bool_expr(true))];
    let ensures = vec![eq(result_flag, bool_expr(true))];
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Bool field with true precondition should verify. Got: {result:?}"
    );

    unsoundness::reset();
}

/// Bool field in implies position should not cause sort mismatch panic.
///
/// Scenario:
///   requires: (none)
///   ensures: __trust_wp_field_flag(x) ==> result > 0
///
/// The field accessor returns Int (exempted), but the implies operator
/// expects Bool operands. The encoder should handle the coercion or
/// the verification should complete without panic.
#[test]
#[timeout(30000)]
fn bool_field_in_implies_no_panic() {
    unsoundness::reset();

    let field_flag = named_field("flag", var("x"));
    let ensures = vec![implies(field_flag, gt(var("result"), int(0)))];

    let result = verify_function_with_modes(VerificationRequest::new(&[], &ensures))
        .unwrap_or_else(|err| panic!("Bool field in implies should not panic: {err:?}"));

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Bool field in implies should fail without a result bound: {result:?}"
    );

    unsoundness::reset();
}

/// Wrong Bool field postcondition should not produce false Verified.
///
/// Scenario:
///   requires: __trust_wp_field_flag(x) == true
///   ensures: __trust_wp_field_flag(result) == false
///   body: x (identity)
///
/// This SHOULD fail because result = x and flag(x) == true contradicts
/// flag(result) == false. However, ay may return Unknown("incomplete")
/// due to Bool-as-Int encoding limitations. The key soundness property:
/// it must NOT be Verified.
#[test]
#[timeout(30000)]
fn bool_field_wrong_postcondition_not_verified() {
    unsoundness::reset();

    let x_flag = named_field("flag", var("x"));
    let result_flag = named_field("flag", var("result"));

    let requires = vec![eq(x_flag, bool_expr(true))];
    let ensures = vec![eq(result_flag, bool_expr(false))];
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).return_expr(Some(&body)),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Contradictory Bool field postcondition should fail: {result:?}"
    );

    unsoundness::reset();
}
