// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ════════════════════════════════════════════════════════════════════════
// batch_inference.rs tests — infer_constructor_arg_sorts_batch direct cases
// ════════════════════════════════════════════════════════════════════════

/// Batch inference produces same results as per-variable inference.
#[test]
#[timeout(30000)]
fn test_batch_inference_matches_per_variable() {
    let mut encoder = AYEncoder::new();
    let dt = pair_int_bool_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = logic_fn_call("PairIntBool::Pair", vec![var("k"), var("v")]);

    let batch = infer_constructor_arg_sorts_batch(&encoder, &body, &["k", "v"]);
    let single_k = infer_constructor_arg_sort(&encoder, &body, "k");
    let single_v = infer_constructor_arg_sort(&encoder, &body, "v");

    assert_eq!(
        batch.get("k").cloned(),
        single_k,
        "batch k should match single k"
    );
    assert_eq!(
        batch.get("v").cloned(),
        single_v,
        "batch v should match single v"
    );
    assert_eq!(batch.len(), 2, "batch should resolve both variables");
}

/// Batch inference: variable not in constructor returns empty result for that var.
#[test]
#[timeout(30000)]
fn test_batch_inference_missing_variable() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = logic_fn_call("OptionInt::Some", vec![var("v")]);

    let batch = infer_constructor_arg_sorts_batch(&encoder, &body, &["v", "w"]);
    assert_eq!(batch.get("v").cloned(), Some(Sort::Int));
    assert!(
        !batch.contains_key("w"),
        "w not in constructor should not appear in batch result"
    );
}

// Batch propagation tests moved to `batch_inference_branch_propagation_tests.rs`.
