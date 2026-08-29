// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ════════════════════════════════════════════════════════════════════════
// batch inference consistency tests
// ════════════════════════════════════════════════════════════════════════

/// Batch inference consistency: batch and single inference agree on a complex
/// expression tree with multiple variables across different sub-expressions.
#[test]
#[timeout(30000)]
fn test_batch_single_consistency_complex_tree() {
    let mut encoder = AYEncoder::new();
    let opt_dt = option_int_datatype();
    let pair_dt = pair_int_bool_datatype();
    encoder.ensure_datatype_declared(&opt_dt);
    encoder.ensure_datatype_declared(&pair_dt);

    // implies(eq(x, Some(a)), eq(y, Pair(b, c)))
    let body = implies(
        eq(var("x"), logic_fn_call("OptionInt::Some", vec![var("a")])),
        eq(
            var("y"),
            logic_fn_call("PairIntBool::Pair", vec![var("b"), var("c")]),
        ),
    );

    let qvars = ["a", "b", "c"];
    let batch = infer_constructor_arg_sorts_batch(&encoder, &body, &qvars);

    for &v in &qvars {
        let single = infer_constructor_arg_sort(&encoder, &body, v);
        assert_eq!(
            batch.get(v).cloned(),
            single,
            "batch and single must agree for variable '{v}'"
        );
    }
    assert_eq!(batch.get("a").cloned(), Some(Sort::Int), "a from Some");
    assert_eq!(batch.get("b").cloned(), Some(Sort::Int), "b from Pair fst");
    assert_eq!(batch.get("c").cloned(), Some(Sort::Bool), "c from Pair snd");
}
