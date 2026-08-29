// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ════════════════════════════════════════════════════════════════════════
// batch_inference.rs tests — propagation through branches and wrappers
// ════════════════════════════════════════════════════════════════════════

/// Batch inference through BinOp with both variables in different sub-expressions.
#[test]
#[timeout(30000)]
fn test_batch_inference_across_binop() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let result_dt = result_int_int_datatype();
    encoder.ensure_datatype_declared(&result_dt);

    // x == Some(v) && y == Ok(w)
    let body = and(
        eq(var("x"), logic_fn_call("OptionInt::Some", vec![var("v")])),
        eq(var("y"), logic_fn_call("OwnResult::Ok", vec![var("w")])),
    );

    let batch = infer_constructor_arg_sorts_batch(&encoder, &body, &["v", "w"]);
    assert_eq!(batch.get("v").cloned(), Some(Sort::Int), "v from Some");
    assert_eq!(batch.get("w").cloned(), Some(Sort::Int), "w from Ok");
    assert_eq!(batch.len(), 2);
}

/// Batch inference through Ite — variables in all branches.
#[test]
#[timeout(30000)]
fn test_batch_inference_through_ite() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let result_dt = result_int_int_datatype();
    encoder.ensure_datatype_declared(&result_dt);

    // if cond then Some(v) else Ok(w) — v in then-branch, w in else-branch.
    let body = ite(
        bool_expr(true),
        logic_fn_call("OptionInt::Some", vec![var("v")]),
        logic_fn_call("OwnResult::Ok", vec![var("w")]),
    );

    let batch = infer_constructor_arg_sorts_batch(&encoder, &body, &["v", "w"]);
    assert_eq!(
        batch.get("v").cloned(),
        Some(Sort::Int),
        "v from then-branch"
    );
    assert_eq!(
        batch.get("w").cloned(),
        Some(Sort::Int),
        "w from else-branch"
    );
}

/// Batch inference through LetAssume and LetObligation.
#[test]
#[timeout(30000)]
fn test_batch_inference_through_let_assume_and_obligation() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let result_dt = result_int_int_datatype();
    encoder.ensure_datatype_declared(&result_dt);

    // let_assume { assumption: Some(v); body: Ok(w) }
    let body = let_assume(
        logic_fn_call("OptionInt::Some", vec![var("v")]),
        logic_fn_call("OwnResult::Ok", vec![var("w")]),
    );

    let batch = infer_constructor_arg_sorts_batch(&encoder, &body, &["v", "w"]);
    assert_eq!(
        batch.get("v").cloned(),
        Some(Sort::Int),
        "v from assumption"
    );
    assert_eq!(batch.get("w").cloned(), Some(Sort::Int), "w from body");
}
