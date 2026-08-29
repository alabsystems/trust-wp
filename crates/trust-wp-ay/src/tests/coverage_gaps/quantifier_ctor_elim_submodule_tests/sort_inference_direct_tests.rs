// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ════════════════════════════════════════════════════════════════════════
// sort_inference.rs tests — direct expression-tree inference
// ════════════════════════════════════════════════════════════════════════

/// Multi-field datatype: infer different sorts for different field positions.
#[test]
#[timeout(30000)]
fn test_infer_sort_multi_field_different_sorts() {
    let mut encoder = AYEncoder::new();
    let dt = pair_int_bool_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = logic_fn_call("PairIntBool::Pair", vec![var("k"), var("v")]);

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "k"),
        Some(Sort::Int),
        "k at field 0 should infer Int"
    );
    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        Some(Sort::Bool),
        "v at field 1 should infer Bool"
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
