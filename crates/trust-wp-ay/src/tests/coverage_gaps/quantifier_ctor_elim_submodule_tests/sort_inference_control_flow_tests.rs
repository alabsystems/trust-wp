// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ════════════════════════════════════════════════════════════════════════
// sort_inference.rs tests — direct control-flow inference
// ════════════════════════════════════════════════════════════════════════

/// Infer sort through BinOp: `x == Some(v)` — v is at field index 0 (Sort::Int).
#[test]
#[timeout(30000)]
fn test_infer_sort_through_binop() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = eq(var("x"), logic_fn_call("OptionInt::Some", vec![var("v")]));

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        Some(Sort::Int),
        "v in Some(v) should infer Int from constructor field sort"
    );
}

/// Infer sort through Ite: `if cond then Some(v) else None`.
#[test]
#[timeout(30000)]
fn test_infer_sort_through_ite() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = ite(
        bool_expr(true),
        logic_fn_call("OptionInt::Some", vec![var("v")]),
        logic_fn_call("OptionInt::None", vec![]),
    );

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        Some(Sort::Int),
        "v through Ite branch should still infer constructor field sort"
    );
}

/// Infer sort through Let value expression.
#[test]
#[timeout(30000)]
fn test_infer_sort_through_let_value() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = let_bind(
        "tmp",
        logic_fn_call("OptionInt::Some", vec![var("v")]),
        var("tmp"),
    );

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        Some(Sort::Int),
        "v in Let value should be inferred"
    );
}
