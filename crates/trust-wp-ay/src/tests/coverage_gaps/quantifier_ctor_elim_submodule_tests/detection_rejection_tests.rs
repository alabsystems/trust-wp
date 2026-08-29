// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Non-equality body returns None (body is a bare BinOp::Gt, not Eq).
#[test]
#[timeout(30000)]
fn test_detect_non_equality_body_returns_none() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("x", Sort::Datatype(dt))
        .expect("declare x");

    // exists<v> v > 0  (not an equality)
    let body = gt(var("v"), int(0));

    let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &["v"]);
    assert!(info.is_none(), "non-equality body should return None");
}

/// Unknown constructor name (not registered) returns None.
#[test]
#[timeout(30000)]
fn test_detect_unregistered_constructor_returns_none() {
    let encoder = AYEncoder::new_with_quantifiers();
    // No datatype registered

    let body = eq(var("x"), logic_fn_call("Unknown::Ctor", vec![var("v")]));

    let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &["v"]);
    assert!(
        info.is_none(),
        "unregistered constructor should return None"
    );
}

// Constructor-argument rejection tests moved to `detection_argument_rejection_tests.rs`.
