// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Ground tuple destructor instances must coerce Bool fields to Int when a
/// tuple projection is used in arithmetic. (#724)
#[test]
#[timeout(30000)]
fn test_ground_tuple_destructor_instances_coerce_bool_field_for_lia() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name;

    let body_eq = eq(
        var("t"),
        logic_fn_call(&tuple_logic_fn_name(2), vec![bool_expr(true), int(9)]),
    );
    let post = eq(add(get_field(0, var("t")), get_field(1, var("t"))), int(10));

    let result = verify_function_with_modes(VerificationRequest::new(&[body_eq], &[post])).unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Bool tuple field should coerce to Int in arithmetic postconditions: {result:?}"
    );
}

/// The Bool-to-Int ground tuple path must still produce a counterexample for a
/// broken arithmetic postcondition. (#724)
#[test]
#[timeout(30000)]
fn test_ground_tuple_destructor_instances_coerce_bool_field_detects_violation() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name;

    let body_eq = eq(
        var("t"),
        logic_fn_call(&tuple_logic_fn_name(2), vec![bool_expr(true), int(8)]),
    );
    let post = eq(add(get_field(0, var("t")), get_field(1, var("t"))), int(10));

    let result = verify_function_with_modes(VerificationRequest::new(&[body_eq], &[post])).unwrap();
    assert!(
        matches!(
            result,
            VerificationResult::Failed(_)
                | VerificationResult::Unknown(
                    crate::verify::UnknownReason::QuantifierEmatchingExistsIncomplete
                )
        ),
        "the concrete tuple (true, 8), whose coerced sum is 9, must not prove equality to 10; AY may fail closed while validating tuple destructor quantifiers: {result:?}"
    );
}
