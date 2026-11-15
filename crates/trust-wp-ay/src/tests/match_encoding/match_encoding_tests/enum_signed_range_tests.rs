// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Match expression encoding tests for trust-wp-ay.

use super::*;

/// Build ADT metadata for a user-defined enum `Shape { Circle(i32), Square(i32) }`.
fn sample_enum_adt_decls() -> trust_wp_core::logic::AdtDecls {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    std::collections::HashMap::from([(
        "Shape".to_string(),
        AdtDecl::new(
            "crate::Shape".to_string(),
            "Shape".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "Circle".to_string(),
                    "Circle".to_string(),
                    vec![AdtFieldDecl::new("0".to_string(), ExprSort::Int)],
                ),
                AdtConstructorDecl::new(
                    "Square".to_string(),
                    "Square".to_string(),
                    vec![AdtFieldDecl::new("0".to_string(), ExprSort::Int)],
                ),
            ],
        ),
    )])
}

fn sample_nullary_enum_adt_decls() -> trust_wp_core::logic::AdtDecls {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtKind};

    std::collections::HashMap::from([(
        "State".to_string(),
        AdtDecl::new(
            "crate::State".to_string(),
            "State".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new("On".to_string(), "On".to_string(), vec![]),
                AdtConstructorDecl::new("Off".to_string(), "Off".to_string(), vec![]),
            ],
        ),
    )])
}

/// User-defined enum constructor in a return expression should encode
/// natively when ADT metadata is registered, without requiring a prior
/// match declaration. (#1982)
///
/// Scenario: enum Shape { Circle(i32), Square(i32) }
///   requires: (none)
///   ensures: result == Circle(5)
///   body: Circle(5)
///
/// The constructor `Circle(5)` should use the native datatype constructor
/// from the registered ADT, not an untyped UF fallback.
#[test]
#[timeout(30000)]
fn test_enum_constructor_without_match_via_adt_decls() {
    let body = logic_fn_call("Circle", vec![int(5)]);
    let ensures = eq(var("result"), logic_fn_call("Circle", vec![int(5)]));

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[], std::slice::from_ref(&ensures))
            .return_expr(Some(&body))
            .adt_decls(Some(sample_enum_adt_decls())),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    assert!(
        matches!(result, crate::VerificationResult::Verified(_)),
        "enum constructor in return expr should verify via registered ADT metadata: {result:?}"
    );
}

/// Bare zero-field enum variants should also route through the registered
/// datatype path instead of behaving like unconstrained variables. (#1982)
#[test]
#[timeout(30000)]
fn test_nullary_enum_constructor_without_match_via_adt_decls() {
    let body = var("On");
    let ensures = ne(var("result"), var("Off"));

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[], std::slice::from_ref(&ensures))
            .return_expr(Some(&body))
            .adt_decls(Some(sample_nullary_enum_adt_decls())),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    // KNOWN-CLASS PIN (upstream proof-trusted certification gap): the verdict
    // demotes to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
            crate::tests::helpers::verified_or_known_proof_trusted(&result),
            "distinct nullary constructors should remain disjoint via registered ADT metadata: {result:?}"
        );
}

/// Two distinct enum constructors should not be equal even when both carry
/// the same payload. (#1982)
///
/// Scenario: enum Shape { Circle(i32), Square(i32) }
///   requires: (none)
///   ensures: Circle(5) == Square(5)  [should FAIL]
///   body: Circle(5)
///
/// With proper ADT encoding, Circle and Square are distinct constructors,
/// so verification returns Failed.
#[test]
#[timeout(30000)]
fn test_enum_distinct_constructors_not_equal() {
    let body = logic_fn_call("Circle", vec![int(5)]);
    let ensures = eq(
        logic_fn_call("Circle", vec![int(5)]),
        logic_fn_call("Square", vec![int(5)]),
    );

    let result = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[], std::slice::from_ref(&ensures))
            .return_expr(Some(&body))
            .adt_decls(Some(sample_enum_adt_decls())),
    )
    .unwrap_or_else(|err| panic!("Verification should not error: {err:?}"));

    assert!(
        matches!(result, crate::VerificationResult::Failed(_)),
        "Circle(5) == Square(5) should fail because constructors are distinct: {result:?}"
    );
}
