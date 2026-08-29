// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_ay::VerificationResult;
use trust_wp_core::formula::{BinOp, PureExpr};

use crate::callbacks::struct_field_map::extract_int_type_from_path;

#[test]
fn extract_int_type_from_path_known_types() {
    assert_eq!(extract_int_type_from_path("i32::checked_add"), Some("i32"));
    assert_eq!(extract_int_type_from_path("u8::saturating_sub"), Some("u8"));
    assert_eq!(extract_int_type_from_path("i64::wrapping_mul"), Some("i64"));
    assert_eq!(
        extract_int_type_from_path("usize::checked_add"),
        Some("usize")
    );
    assert_eq!(
        extract_int_type_from_path("core::num::i32::checked_add"),
        Some("i32")
    );
    assert_eq!(
        extract_int_type_from_path("core::num::<impl i8>::wrapping_add"),
        Some("i8")
    );
}

#[test]
fn extract_int_type_from_path_non_integer() {
    assert_eq!(extract_int_type_from_path("Vec::push"), None);
    assert_eq!(extract_int_type_from_path("String::len"), None);
    assert_eq!(extract_int_type_from_path("my_module::my_fn"), None);
    assert_eq!(
        extract_int_type_from_path("core::num::NonZeroU8::new"),
        None
    );
    assert_eq!(
        extract_int_type_from_path("core::num::<impl NonZeroI32>::new"),
        None
    );
}

/// Verify that type constants flow through to the encoder: a spec referencing
/// `Self::MIN@` and `Self::MAX@` should verify when type constants are provided,
/// and the resolved values should match the concrete integer bounds.
#[test]
fn type_constants_flow_through_verify_function() {
    use trust_wp_ay::{type_constants_for_int, verify_function_with_modes, VerificationRequest};

    // Spec: requires x >= Self::MIN@ && x <= Self::MAX@
    //       ensures result >= -128 && result <= 127
    // Body: result = x
    // With i8 type constants (MIN=-128, MAX=127), the precondition bounds x,
    // and the postcondition holds because result == x and x is in [-128, 127].
    // Without type constants, Self::MIN@ and Self::MAX@ are uninterpreted
    // so x is unbounded and the postcondition would not be provable.
    let req = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "Self::MIN".to_string(),
                None,
            )))),
        )),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Le,
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "Self::MAX".to_string(),
                None,
            )))),
        )),
    );
    // ensures: result >= -128 && result <= 127
    let ens = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(-128)),
        )),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Le,
            Arc::new(PureExpr::Int(127)),
        )),
    );
    // body: result = x
    let body = PureExpr::Var("x".to_string(), None);

    let tc = type_constants_for_int("i8");
    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_constants(tc.as_ref()),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "expected Verified with type constants, got {result:?}"
    );
}

/// Without type constants, Self::MIN@ and Self::MAX@ are uninterpreted,
/// so a spec that depends on their concrete values should not verify.
#[test]
fn type_constants_none_leaves_uninterpreted() {
    use trust_wp_ay::{verify_function_with_modes, VerificationRequest};

    // Spec: requires Self::MIN@ < Self::MAX@
    //       ensures Self::MIN@ >= 0
    // Without concrete type constants, both names are uninterpreted symbols.
    // Then `requires` does not imply `ensures` (e.g. MIN=-1, MAX=0),
    // so verification should fail.
    let req = PureExpr::BinOp(
        Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "Self::MIN".to_string(),
            None,
        )))),
        BinOp::Lt,
        Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "Self::MAX".to_string(),
            None,
        )))),
    );
    let ens = PureExpr::BinOp(
        Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "Self::MIN".to_string(),
            None,
        )))),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );

    let result = verify_function_with_modes(VerificationRequest::new(&[req], &[ens]))
        .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "expected Failed without type constants (Self::MIN@ is uninterpreted), got {result:?}"
    );
}
