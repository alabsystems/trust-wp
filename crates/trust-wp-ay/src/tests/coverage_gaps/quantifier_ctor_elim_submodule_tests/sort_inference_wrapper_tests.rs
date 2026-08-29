// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ════════════════════════════════════════════════════════════════════════
// sort_inference.rs tests — wrapper/context propagation
// ════════════════════════════════════════════════════════════════════════

/// Inference through UnOp (Not).
#[test]
#[timeout(30000)]
fn test_infer_sort_through_unop() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = not(eq(
        var("x"),
        logic_fn_call("OptionInt::Some", vec![var("v")]),
    ));

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        Some(Sort::Int),
        "v should be inferred through UnOp (Not)"
    );
}

/// Inference through Deref wrapper.
#[test]
#[timeout(30000)]
fn test_infer_sort_through_deref() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = deref(logic_fn_call("OptionInt::Some", vec![var("v")]));

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        Some(Sort::Int),
        "v should be inferred through Deref"
    );
}

/// Inference through Old wrapper.
#[test]
#[timeout(30000)]
fn test_infer_sort_through_old() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = old(logic_fn_call("OptionInt::Some", vec![var("v")]));

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        Some(Sort::Int),
        "v should be inferred through Old"
    );
}

/// Inference through View wrapper.
#[test]
#[timeout(30000)]
fn test_infer_sort_through_view() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = view(logic_fn_call("OptionInt::Some", vec![var("v")]));

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        Some(Sort::Int),
        "v should be inferred through View"
    );
}
