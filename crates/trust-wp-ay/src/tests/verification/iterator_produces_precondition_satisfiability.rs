// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Soundness regression coverage for iterator `produces` preconditions. (#2404)

use super::*;

/// Regression for #2404: the full `into_iter` produces precondition set must
/// stay satisfiable. If these assumptions become contradictory, both the
/// positive and negative verification tests vacuously verify.
#[test]
#[timeout(30000)]
fn test_diag_into_iter_produces_preconditions_are_satisfiable() {
    let vec_len = eq(method_call(view(var("vec")), "len", vec![]), int(3));
    let vec_first = eq(
        method_call(view(var("vec")), "index_logic", vec![int(0)]),
        int(42),
    );
    let seq_v = logic_fn_call("seq", vec![var("v")]);
    let concat = method_call(seq_v, "concat", vec![view(var("next_iter"))]);
    let produces = method_call(view(var("vec")), "ext_eq", vec![concat]);
    let preconditions = vec![vec_len, vec_first, produces];

    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.register_sort_hints(&preconditions);
    for expr in &preconditions {
        let term = encoder
            .encode_pure(expr)
            .unwrap_or_else(|e| panic!("precondition should encode: {e:?}"));
        encoder.assert_term(term);
    }

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "into_iter produces preconditions must be satisfiable: got {result:?}"
    );
}
