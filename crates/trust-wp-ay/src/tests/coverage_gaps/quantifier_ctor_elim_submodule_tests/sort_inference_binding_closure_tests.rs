// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ════════════════════════════════════════════════════════════════════════
// sort_inference.rs tests — closure shadowing
// ════════════════════════════════════════════════════════════════════════

/// Closure with parameter shadowing the qvar should not infer from body.
#[test]
#[timeout(30000)]
fn test_infer_sort_closure_shadows_qvar() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    // |v| Some(v) — the closure parameter `v` shadows our qvar.
    let body = PureExpr::Closure {
        params: vec![("v".to_string(), None)],
        body: Arc::new(logic_fn_call("OptionInt::Some", vec![var("v")])),
    };

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        None,
        "closure parameter should shadow qvar, preventing inference from body"
    );
}

/// Closure with different parameter does NOT shadow.
#[test]
#[timeout(30000)]
fn test_infer_sort_closure_no_shadow() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    // |x| Some(v) — parameter is `x`, not `v`, so `v` is still free.
    let body = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(logic_fn_call("OptionInt::Some", vec![var("v")])),
    };

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        Some(Sort::Int),
        "closure parameter 'x' should not shadow qvar 'v'"
    );
}
