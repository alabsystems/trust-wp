// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Match expression encoding tests for trust-wp-ay.

use std::sync::Arc;

use trust_wp_core::formula::Pattern;

use super::*;

/// Regression for #1811: a body that returns `Err(42)` binds `result` to the
/// `Err` constructor it names, never to the type's value constructor `Ok`
/// (`result = Ok(42)` would decide a variant the body does not choose).
#[test]
#[timeout(30000)]
fn test_result_err_body_uses_err_constructor_not_default_ok() {
    use crate::verify::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // Postcondition: match result { Ok(_) => false, Err(e) => e == 42 }
    let ensures = vec![PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("result".to_string(), None)),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Ok".to_string(),
                    inner: Some(Box::new(Pattern::Wildcard)),
                },
                body: PureExpr::Bool(false),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Err".to_string(),
                    inner: Some(Box::new(Pattern::Binding("e".to_string()))),
                },
                body: PureExpr::BinOp(
                    Arc::new(PureExpr::Var("e".to_string(), None)),
                    trust_wp_core::formula::BinOp::Eq,
                    Arc::new(PureExpr::Int(42)),
                ),
            },
        ],
    }];

    // Body: Err(42) — MIR preserved the Err constructor.
    let return_expr = PureExpr::LogicFnCall {
        name: "Err".to_string(),
        args: vec![PureExpr::Int(42)],
    };

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures)
            .return_expr(Some(&return_expr))
            .timeout(Some(std::time::Duration::from_secs(10))),
    );

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Err(42) body with Err-matching postcondition should verify: {result:?}"
    );
}

/// `from_arms` cannot produce `UserDefined` with empty constructors because
/// the `!saw_constructor` guard returns `None` before reaching the
/// `UserDefined` branch. This test verifies the invariant. (#1980)
#[test]
#[timeout(30000)]
fn test_from_arms_no_constructors_returns_none() {
    use crate::encoder::match_enc::SwitchTarget;

    // Arms with no Constructor patterns → from_arms returns None.
    let wildcard_only = vec![MatchArm {
        pattern: Pattern::Wildcard,
        body: bool_expr(true),
    }];
    assert_eq!(
        SwitchTarget::from_arms(&wildcard_only),
        None,
        "No constructor arms should return None, not UserDefined with empty vec"
    );

    // Empty arms → also None.
    assert_eq!(
        SwitchTarget::from_arms(&[]),
        None,
        "Empty arms should return None"
    );
}
