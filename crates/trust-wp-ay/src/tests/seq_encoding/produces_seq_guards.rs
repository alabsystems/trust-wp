// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for Seq guards on iterator `produces` carriers.

use ay_dpll::api::Sort;
use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn produces_bridges_visited_arg_locked_as_int() {
    let mut encoder = AYEncoder::new();

    let visited = var("visited");
    let visited_term = encoder
        .encode_pure(&visited)
        .expect("pre-lock visited as default Int");
    assert_eq!(
        encoder.solver.get_sort(visited_term),
        Sort::Int,
        "test setup should lock the visited carrier as Int"
    );

    let produces = method_call(var("iter"), "produces", vec![visited, var("next")]);
    let result = encoder.encode_pure(&produces);

    assert!(
        result.is_ok(),
        "produces should bridge the semantically-Seq visited argument instead of panicking: {result:?}"
    );
    assert_eq!(
        encoder.solver.get_sort(result.expect("checked ok")),
        Sort::Bool
    );
}

#[test]
#[timeout(30000)]
fn seq_len_term_bridges_int_fallback_carrier() {
    let mut encoder = AYEncoder::new();
    let raw = encoder
        .solver_mut()
        .declare_const("raw_int_seq_carrier", Sort::Int);

    let len = encoder
        .seq_len_term(raw)
        .expect("seq_len_term should bridge an Int fallback carrier");
    let duplicate = encoder
        .seq_len_term(raw)
        .expect("the finite length component should be stable");

    assert_eq!(encoder.solver.get_sort(len), Sort::Int);
    assert_eq!(len, duplicate);
    assert!(
        !encoder.seq_state_for_test().funcs_is_some(),
        "a ground finite component must not initialize the global Seq projector theory"
    );
}
