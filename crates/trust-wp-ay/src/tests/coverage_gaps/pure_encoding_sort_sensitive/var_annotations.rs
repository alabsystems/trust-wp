// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// ── Var encoding with sort annotations ───────────────────────────────

/// Var with ExprSort::Bool annotation gets Bool sort.
#[test]
#[timeout(30000)]
fn var_with_bool_annotation_gets_bool_sort() {
    let mut encoder = AYEncoder::new();

    let expr = var_with_sort("p", ExprSort::Bool);
    let _term = encoder
        .encode_pure(&expr)
        .expect("Bool-annotated var should encode");

    assert_eq!(
        encoder.var_sort("p"),
        Some(&Sort::Bool),
        "ExprSort::Bool annotation must produce Bool-sorted variable"
    );
}

/// Var with ExprSort::Seq annotation gets non-Int sort.
#[test]
#[timeout(30000)]
fn var_with_seq_annotation_gets_non_int_sort() {
    let mut encoder = AYEncoder::new();

    let expr = var_with_sort("s", ExprSort::Seq);
    let _term = encoder
        .encode_pure(&expr)
        .expect("Seq-annotated var should encode");

    let sort = encoder.var_sort("s");
    assert!(sort.is_some(), "Seq-annotated var must have a sort");
    assert_ne!(sort, Some(&Sort::Int), "Seq-annotated var must not be Int");
}
