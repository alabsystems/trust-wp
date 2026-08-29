// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use crate::AYEncoder;

#[test]
#[timeout(30000)]
fn test_nested_deref_logic_fn_call_rewrites_consistently() {
    let mut encoder = AYEncoder::new();

    let nested = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::LogicFnCall {
        name: "f".to_string(),
        args: vec![
            PureExpr::Var("x".to_string(), None),
            PureExpr::Var("y".to_string(), None),
        ],
    }))));

    let pushed = PureExpr::LogicFnCall {
        name: "f".to_string(),
        args: vec![
            PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            ))))),
            PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "y".to_string(),
                None,
            ))))),
        ],
    };

    let nested_term = encoder
        .encode_pure(&nested)
        .expect("nested Deref(LogicFnCall) should encode");
    let pushed_term = encoder
        .encode_pure(&pushed)
        .expect("manually pushed deref call should encode");

    assert_eq!(
        nested_term, pushed_term,
        "nested deref rewrite should normalize to the same term as manual push"
    );
}

#[test]
#[timeout(30000)]
fn test_nested_final_logic_fn_call_rewrites_consistently() {
    let mut encoder = AYEncoder::new();

    let nested = PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(PureExpr::LogicFnCall {
        name: "g".to_string(),
        args: vec![
            PureExpr::Var("x".to_string(), None),
            PureExpr::Var("y".to_string(), None),
        ],
    }))));

    let pushed = PureExpr::LogicFnCall {
        name: "g".to_string(),
        args: vec![
            PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "x".to_string(),
                None,
            ))))),
            PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "y".to_string(),
                None,
            ))))),
        ],
    };

    let nested_term = encoder
        .encode_pure(&nested)
        .expect("nested Final(LogicFnCall) should encode");
    let pushed_term = encoder
        .encode_pure(&pushed)
        .expect("manually pushed final call should encode");

    assert_eq!(
        nested_term, pushed_term,
        "nested final rewrite should normalize to the same term as manual push"
    );
}

#[test]
#[timeout(30000)]
fn test_nested_deref_method_call_rewrites_receiver_and_args() {
    let mut encoder = AYEncoder::new();

    let nested = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
        method: "set".to_string(),
        args: vec![
            PureExpr::Var("y".to_string(), None),
            PureExpr::Var("z".to_string(), None),
        ],
    }))));

    let pushed = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(
            PureExpr::Var("x".to_string(), None),
        ))))),
        method: "set".to_string(),
        args: vec![
            PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "y".to_string(),
                None,
            ))))),
            PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "z".to_string(),
                None,
            ))))),
        ],
    };

    let nested_term = encoder
        .encode_pure(&nested)
        .expect("nested Deref(MethodCall) should encode");
    let pushed_term = encoder
        .encode_pure(&pushed)
        .expect("manually pushed deref method call should encode");

    assert_eq!(
        nested_term, pushed_term,
        "nested deref method rewrite should preserve receiver/arg depth"
    );
}

#[test]
#[timeout(30000)]
fn test_nested_final_method_call_rewrites_receiver_and_args() {
    let mut encoder = AYEncoder::new();

    let nested = PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("x".to_string(), None)),
        method: "set".to_string(),
        args: vec![
            PureExpr::Var("y".to_string(), None),
            PureExpr::Var("z".to_string(), None),
        ],
    }))));

    // VARIABLE arguments keep the legacy full distribution (#124 exempts
    // only GROUND-CONSTANT arguments, which have no temporal state and whose
    // wrapping minted refused `^<literal>` shapes).
    let pushed = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(
            PureExpr::Var("x".to_string(), None),
        ))))),
        method: "set".to_string(),
        args: vec![
            PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "y".to_string(),
                None,
            ))))),
            PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "z".to_string(),
                None,
            ))))),
        ],
    };

    let nested_term = encoder
        .encode_pure(&nested)
        .expect("nested Final(MethodCall) should encode");
    let pushed_term = encoder
        .encode_pure(&pushed)
        .expect("manually pushed final method call should encode");

    assert_eq!(
        nested_term, pushed_term,
        "nested final method rewrite should preserve receiver/arg depth"
    );
}

#[test]
#[timeout(30000)]
fn test_nested_deref_view_rewrites_consistently() {
    let mut encoder = AYEncoder::new();

    let nested = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::View(
        Arc::new(PureExpr::Var("x".to_string(), None)),
    )))));
    let pushed = PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Deref(
        Arc::new(PureExpr::Var("x".to_string(), None)),
    )))));

    let nested_term = encoder
        .encode_pure(&nested)
        .expect("nested Deref(View) should encode");
    let pushed_term = encoder
        .encode_pure(&pushed)
        .expect("manually pushed deref view should encode");

    assert_eq!(
        nested_term, pushed_term,
        "nested deref view rewrite should normalize to the same term as manual push"
    );
}

#[test]
#[timeout(30000)]
fn test_nested_final_view_rewrites_consistently() {
    let mut encoder = AYEncoder::new();

    let nested = PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(PureExpr::View(
        Arc::new(PureExpr::Var("x".to_string(), None)),
    )))));
    let pushed = PureExpr::View(Arc::new(PureExpr::Final(Arc::new(PureExpr::Final(
        Arc::new(PureExpr::Var("x".to_string(), None)),
    )))));

    let nested_term = encoder
        .encode_pure(&nested)
        .expect("nested Final(View) should encode");
    let pushed_term = encoder
        .encode_pure(&pushed)
        .expect("manually pushed final view should encode");

    assert_eq!(
        nested_term, pushed_term,
        "nested final view rewrite should normalize to the same term as manual push"
    );
}
