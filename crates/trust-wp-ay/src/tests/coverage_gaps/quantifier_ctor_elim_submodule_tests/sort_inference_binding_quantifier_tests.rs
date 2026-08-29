// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ════════════════════════════════════════════════════════════════════════
// sort_inference.rs tests — nested quantifier shadowing
// ════════════════════════════════════════════════════════════════════════

/// Nested Forall quantifier shadowing the qvar.
#[test]
#[timeout(30000)]
fn test_infer_sort_nested_forall_shadows_qvar() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    // forall<v: Int> Some(v) — inner quantifier shadows our qvar.
    let body = PureExpr::Forall {
        var: "v".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(logic_fn_call("OptionInt::Some", vec![var("v")])),
        triggers: vec![],
    };

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        None,
        "nested Forall binding should shadow qvar"
    );
}

/// Nested Exists quantifier shadowing the qvar.
#[test]
#[timeout(30000)]
fn test_infer_sort_nested_exists_shadows_qvar() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = PureExpr::Exists {
        var: "v".to_string(),
        var_sort: None,
        body: Arc::new(logic_fn_call("OptionInt::Some", vec![var("v")])),
        triggers: vec![],
    };

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        None,
        "nested Exists binding should shadow qvar"
    );
}
