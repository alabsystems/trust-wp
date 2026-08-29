// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Empty qvars list — should still detect nullary constructor pattern.
#[test]
#[timeout(30000)]
fn test_detect_empty_qvars_nullary_constructor() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dt = state_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("x", Sort::Datatype(dt))
        .expect("declare x");

    let body = eq(var("x"), logic_fn_call("State::On", vec![]));

    let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &[]);
    assert!(
        info.is_some(),
        "empty qvars with nullary constructor should still detect"
    );
}

/// Empty qvars list with non-nullary constructor — should reject because
/// constructor args are not in qvar set.
#[test]
#[timeout(30000)]
fn test_detect_empty_qvars_non_nullary_rejects() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);
    encoder
        .get_or_declare_var("x", Sort::Datatype(dt))
        .expect("declare x");

    let body = eq(var("x"), logic_fn_call("OptionInt::Some", vec![var("v")]));

    let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &[]);
    assert!(
        info.is_none(),
        "empty qvars with non-nullary constructor should reject"
    );
}
