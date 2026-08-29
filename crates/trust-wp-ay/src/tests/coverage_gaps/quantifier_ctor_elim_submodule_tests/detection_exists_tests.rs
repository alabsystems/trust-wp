// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

/// Exists with reversed equality: `Some(v) == x` detected correctly.
#[test]
#[timeout(30000)]
fn test_detect_exists_reversed_equality() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("x", Sort::Datatype(dt))
        .expect("declare x");

    // exists<v> Some(v) == x  (reversed)
    let body = eq(logic_fn_call("OptionInt::Some", vec![var("v")]), var("x"));

    let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &["v"]);
    assert!(
        info.is_some(),
        "reversed equality Some(v) == x should be detected"
    );
    let info = info.unwrap();
    assert_eq!(info.ctor_name, "OptionInt::Some");
    assert_eq!(info.var_field_map, vec![("v", 0)]);
}

/// Multi-variable detection: `exists<k, v> x == Pair(k, v)`.
#[test]
#[timeout(30000)]
fn test_detect_multi_variable_constructor_eq() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dt = pair_int_bool_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("x", Sort::Datatype(dt))
        .expect("declare x");

    let body = eq(
        var("x"),
        logic_fn_call("PairIntBool::Pair", vec![var("k"), var("v")]),
    );

    let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &["k", "v"]);
    assert!(info.is_some(), "multi-variable detection should succeed");
    let info = info.unwrap();
    assert_eq!(info.ctor_name, "PairIntBool::Pair");
    assert_eq!(info.var_field_map, vec![("k", 0), ("v", 1)]);
}
