// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Duplicate qvar in constructor arguments rejects detection.
/// `exists<v> x == Pair(v, v)` — `v` appears twice.
#[test]
#[timeout(30000)]
fn test_detect_duplicate_qvar_argument_rejects() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dt = pair_int_bool_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("x", Sort::Datatype(dt))
        .expect("declare x");

    let body = eq(
        var("x"),
        logic_fn_call("PairIntBool::Pair", vec![var("v"), var("v")]),
    );

    let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &["v"]);
    assert!(
        info.is_none(),
        "duplicate qvar in constructor args must reject detection"
    );
}

/// Non-Var constructor argument rejects detection.
/// `exists<v> x == Some(v + 1)` — `v + 1` is a BinOp, not a Var.
#[test]
#[timeout(30000)]
fn test_detect_non_var_constructor_argument_rejects() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("x", Sort::Datatype(dt))
        .expect("declare x");

    let body = eq(
        var("x"),
        logic_fn_call("OptionInt::Some", vec![add(var("v"), int(1))]),
    );

    let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &["v"]);
    assert!(
        info.is_none(),
        "non-Var constructor argument (v + 1) must reject detection"
    );
}

/// Constructor arg that is a qvar but NOT in the provided qvar list rejects.
/// `exists<v> x == Pair(v, w)` where only `v` is a qvar — `w` is free.
#[test]
#[timeout(30000)]
fn test_detect_free_variable_in_constructor_args_rejects() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dt = pair_int_bool_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("x", Sort::Datatype(dt))
        .expect("declare x");

    let body = eq(
        var("x"),
        logic_fn_call("PairIntBool::Pair", vec![var("v"), var("w")]),
    );

    // Only "v" is a qvar — "w" is not, so detection should fail.
    let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &["v"]);
    assert!(
        info.is_none(),
        "free variable 'w' in constructor args should reject detection"
    );
}
