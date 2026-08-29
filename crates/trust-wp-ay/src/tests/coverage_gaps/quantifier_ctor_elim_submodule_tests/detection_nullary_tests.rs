// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Nullary constructor as bare Var: `exists<v> x == On` (On is a bare Var
/// that matches a nullary constructor).
#[test]
#[timeout(30000)]
fn test_detect_nullary_bare_var_constructor() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dt = state_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("x", Sort::Datatype(dt))
        .expect("declare x");

    // exists<v> x == On  (On as bare Var)
    let body = eq(var("x"), var("On"));

    let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &["v"]);
    assert!(
        info.is_some(),
        "nullary constructor as bare Var should be detected"
    );
    let info = info.unwrap();
    assert_eq!(info.ctor_name, "On");
    assert!(
        info.var_field_map.is_empty(),
        "nullary constructor has no field map"
    );
}

/// Nullary constructor as LogicFnCall: `exists<v> x == State::On()`.
#[test]
#[timeout(30000)]
fn test_detect_nullary_logic_fn_call_constructor() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dt = state_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("x", Sort::Datatype(dt))
        .expect("declare x");

    // exists<v> x == State::On()  (LogicFnCall with empty args)
    let body = eq(var("x"), logic_fn_call("State::On", vec![]));

    let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &["v"]);
    assert!(
        info.is_some(),
        "nullary constructor as LogicFnCall should be detected"
    );
    let info = info.unwrap();
    assert_eq!(info.ctor_name, "State::On");
    assert!(info.var_field_map.is_empty());
}
