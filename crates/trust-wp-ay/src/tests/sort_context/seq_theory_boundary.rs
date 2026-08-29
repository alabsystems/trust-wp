// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_sort_from_param_sort_seq_keeps_theory_lazy() {
    let mut encoder = AYEncoder::new();

    let seq_sort = encoder.sort_from_param_sort(ExprSort::Seq);
    assert!(
        seq_sort.is_seq(),
        "ExprSort::Seq must convert to Sort::Uninterpreted(\"Seq\"), got: {seq_sort:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_none(),
        "sort_from_param_sort(Seq) should not initialize the Seq theory table"
    );

    let _ = encoder.ensure_seq_theory();
    assert!(
        encoder.seq_state_for_test().funcs_is_some(),
        "ensure_seq_theory() should initialize Seq theory declarations on demand"
    );
}

#[test]
#[timeout(30000)]
fn test_sort_from_expr_sort_seq_keeps_theory_lazy() {
    let mut encoder = AYEncoder::new();

    let seq_sort = encoder.sort_from_expr_sort(ExprSort::Seq);
    assert!(
        seq_sort.is_seq(),
        "ExprSort::Seq must map to Sort::Uninterpreted(\"Seq\"), got: {seq_sort:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_none(),
        "sort_from_expr_sort(Seq) should not initialize Seq theory declarations"
    );

    let _ = encoder.ensure_seq_theory();
    assert!(
        encoder.seq_state_for_test().funcs_is_some(),
        "ensure_seq_theory() should initialize Seq theory declarations on demand"
    );
}

#[test]
#[timeout(30000)]
fn test_sort_from_expr_sort_ref_seq_keeps_theory_lazy() {
    let mut encoder = AYEncoder::new();

    let seq_sort = encoder.sort_from_expr_sort(ExprSort::Ref(Box::new(ExprSort::Seq)));
    assert!(
        seq_sort.is_seq(),
        "ExprSort::Ref(Seq) must map to Sort::Uninterpreted(\"Seq\"), got: {seq_sort:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_none(),
        "sort_from_expr_sort(Ref(Seq)) should not initialize Seq theory declarations"
    );

    let _ = encoder.ensure_seq_theory();
    assert!(
        encoder.seq_state_for_test().funcs_is_some(),
        "ensure_seq_theory() should still initialize Seq theory after Ref(Seq) sort lookup"
    );
}
