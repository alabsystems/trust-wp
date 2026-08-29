// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ════════════════════════════════════════════════════════════════════════
// batch_inference.rs tests — infer_constructor_arg_sorts_batch shadowing and early-exit
// ════════════════════════════════════════════════════════════════════════

/// Batch inference with Let binding shadowing one variable.
#[test]
#[timeout(30000)]
fn test_batch_inference_let_shadow() {
    let mut encoder = AYEncoder::new();
    let dt = pair_int_bool_datatype();
    encoder.ensure_datatype_declared(&dt);

    // let v = 0 in Pair(v, w) — Let shadows `v`.
    let body = let_bind(
        "v",
        int(0),
        logic_fn_call("PairIntBool::Pair", vec![var("v"), var("w")]),
    );

    let batch = infer_constructor_arg_sorts_batch(&encoder, &body, &["v", "w"]);
    // The Let value (int(0)) is checked first — no constructor there.
    // Then the body is checked, but `v` is shadowed. However, `w` is still free.
    assert_eq!(
        batch.get("w").cloned(),
        Some(Sort::Bool),
        "w should be inferred from Let body (not shadowed)"
    );
}

/// Batch inference with nested quantifier shadowing.
#[test]
#[timeout(30000)]
fn test_batch_inference_nested_quantifier_shadow() {
    let mut encoder = AYEncoder::new();
    let dt = pair_int_bool_datatype();
    encoder.ensure_datatype_declared(&dt);

    // forall<v: Int> Pair(v, w) — `v` is shadowed by the inner quantifier.
    let body = PureExpr::Forall {
        var: "v".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(logic_fn_call("PairIntBool::Pair", vec![var("v"), var("w")])),
        triggers: vec![],
    };

    let batch = infer_constructor_arg_sorts_batch(&encoder, &body, &["v", "w"]);
    assert_eq!(
        batch.get("w").cloned(),
        Some(Sort::Bool),
        "w should be inferred (not shadowed by inner quantifier)"
    );
}
