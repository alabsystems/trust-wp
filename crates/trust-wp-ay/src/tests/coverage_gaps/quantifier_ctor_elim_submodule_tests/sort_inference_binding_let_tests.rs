// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ════════════════════════════════════════════════════════════════════════
// sort_inference.rs tests — Let binding shadowing and shadow-value checks
// ════════════════════════════════════════════════════════════════════════

/// Let body is skipped when the variable name shadows the qvar.
#[test]
#[timeout(30000)]
fn test_infer_sort_let_shadows_qvar() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    // let v = 0 in Some(v) — the `v` in Some(v) is the Let-bound `v`, not our qvar.
    let body = let_bind(
        "v",
        int(0),
        logic_fn_call("OptionInt::Some", vec![var("v")]),
    );

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        None,
        "Let binding should shadow qvar, preventing inference from body"
    );
}

/// Let value still checked even when body is shadowed.
#[test]
#[timeout(30000)]
fn test_infer_sort_let_value_checked_before_shadow() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    // let v = Some(v) in ... — the `v` in Some(v) refers to our qvar before the shadow.
    let body = let_bind(
        "v",
        logic_fn_call("OptionInt::Some", vec![var("v")]),
        int(0),
    );

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        Some(Sort::Int),
        "Let value should be checked before the shadow takes effect"
    );
}
