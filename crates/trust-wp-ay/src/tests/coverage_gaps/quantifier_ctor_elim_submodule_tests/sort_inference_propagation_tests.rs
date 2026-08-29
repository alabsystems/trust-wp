// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ════════════════════════════════════════════════════════════════════════
// sort_inference.rs tests — LetAssume / LetObligation and qvar deref cases
// ════════════════════════════════════════════════════════════════════════

/// Inference through LetAssume: `let_assume { assumption: Some(v); body: x }`.
#[test]
#[timeout(30000)]
fn test_infer_sort_through_let_assume() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = let_assume(logic_fn_call("OptionInt::Some", vec![var("v")]), var("x"));

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        Some(Sort::Int),
        "v should be inferred through LetAssume assumption"
    );
}

/// Inference through LetObligation body.
#[test]
#[timeout(30000)]
fn test_infer_sort_through_let_obligation() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = let_obligation(var("x"), logic_fn_call("OptionInt::Some", vec![var("v")]));

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        Some(Sort::Int),
        "v should be inferred through LetObligation body"
    );
}

/// Deref-wrapped qvar reference: `Some(*v)` — arg_is_qvar_reference
/// unwraps Deref, so the field sort should be inferred.
#[test]
#[timeout(30000)]
fn test_infer_sort_deref_wrapped_qvar() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = logic_fn_call("OptionInt::Some", vec![deref(var("v"))]);

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        Some(Sort::Int),
        "*v in constructor arg should still infer field sort"
    );
}
