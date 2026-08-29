// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =============================================================================
// synthesize_identity_final_values tests
// =============================================================================

#[test]
fn test_synthesize_identity_final_values_no_mut_borrow_body() {
    // With has_mut_borrow_body=false and a final var in ensures,
    // but no closure receiver call assumptions, do not synthesize identity:
    // arbitrary non-closure prophecy carriers need MIR-derived final values.
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    )];
    let call_assumptions = vec![];
    let result = synthesize_identity_final_values(false, &ensures, &call_assumptions);
    assert_eq!(
        result, None,
        "non-closure final vars must not synthesize identity without receiver evidence"
    );
}

#[test]
fn test_synthesize_identity_final_values_with_mut_borrow_body() {
    let ensures = vec![PureExpr::Final(Arc::new(PureExpr::Var(
        "x".to_string(),
        None,
    )))];
    let result = synthesize_identity_final_values(true, &ensures, &[]);
    assert_eq!(result, None, "mut_borrow_body disables identity synthesis");
}

#[test]
fn test_synthesize_identity_final_values_filters_to_closure_receivers() {
    let ensures = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "f".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(42)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(7)),
        ),
    ];
    let call_assumptions = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "f".to_string(),
            None,
        )))),
        method: "postcondition".to_string(),
        args: vec![
            PureExpr::Var("arg".to_string(), None),
            PureExpr::Var("result".to_string(), None),
        ],
    }];

    let map = synthesize_identity_final_values(false, &ensures, &call_assumptions)
        .expect("matching closure receivers should synthesize identity final values");

    assert_eq!(
        map.get("f"),
        Some(&PureExpr::Var("f".to_string(), None)),
        "closure receiver should synthesize ^f == f"
    );
    assert!(
        !map.contains_key("x"),
        "non-closure prophecy vars must not synthesize identity values"
    );
}

#[test]
fn test_synthesize_identity_final_values_no_final_vars() {
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    )];
    let result = synthesize_identity_final_values(false, &ensures, &[]);
    assert_eq!(
        result, None,
        "no final vars must skip synthesized-final-values mode entirely"
    );
}
