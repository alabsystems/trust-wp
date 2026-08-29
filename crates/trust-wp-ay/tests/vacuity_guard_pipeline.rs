// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;
use trust_wp_ay::{verify_function_with_modes, VerificationRequest, VerificationResult};
use trust_wp_core::formula::{BinOp, PureExpr};

#[test]
#[timeout(10000)]
fn test_vacuity_guard_contradictory_preconditions_pipeline() {
    let requires = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Lt,
            Arc::new(PureExpr::Int(0)),
        ),
    ];
    let ensures = vec![PureExpr::Bool(false)];

    let request = VerificationRequest::new(&requires, &ensures);
    let result = verify_function_with_modes(request).expect("encoding should succeed");

    match &result {
        VerificationResult::Unknown(reason) => {
            assert!(
                reason.as_str().contains("vacuous"),
                "Unknown reason should mention vacuity, got: {}",
                reason.as_str()
            );
        }
        VerificationResult::Verified(_) => {
            panic!("contradictory preconditions should not produce Verified (#2404 bug class)");
        }
        other => panic!("expected Unknown(vacuous), got: {other:?}"),
    }
}

#[test]
#[timeout(10000)]
fn test_vacuity_guard_legitimate_verification_still_passes() {
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];

    let request = VerificationRequest::new(&requires, &ensures);
    let result = verify_function_with_modes(request).expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "legitimate verification should still produce Verified, got: {result:?}"
    );
}
