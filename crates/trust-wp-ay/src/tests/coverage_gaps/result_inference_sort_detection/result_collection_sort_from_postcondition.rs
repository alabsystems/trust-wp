// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;

use super::*;
use crate::verify::{
    result_collection_sort_from_postcondition,
    result_collection_sort_from_postcondition_with_context,
};

/// `*result == (*s).reverse()` — reverse returns Seq, so result should be Seq.
#[test]
#[timeout(30000)]
fn collection_sort_result_eq_reverse() {
    let ensures = vec![eq(
        deref(var("result")),
        method_call(deref(var("s")), "reverse", vec![]),
    )];
    let sort = result_collection_sort_from_postcondition(&ensures);
    assert!(sort.is_some(), "should detect Seq sort from reverse");
    let sort = sort.unwrap();
    assert!(sort.is_seq(), "expected Seq sort, got {sort:?}");
}

/// `s.reverse() == result` — reversed operand order still detected.
#[test]
#[timeout(30000)]
fn collection_sort_reverse_eq_result() {
    let ensures = vec![eq(method_call(var("s"), "reverse", vec![]), var("result"))];
    let sort = result_collection_sort_from_postcondition(&ensures);
    assert!(
        sort.is_some(),
        "should detect Seq sort with reversed operands"
    );
}

/// `result == s.push_back(x)` — push_back returns Seq.
#[test]
#[timeout(30000)]
fn collection_sort_result_eq_push_back() {
    let ensures = vec![eq(
        var("result"),
        method_call(var("s"), "push_back", vec![var("x")]),
    )];
    assert!(result_collection_sort_from_postcondition(&ensures).is_some());
}

/// `result == s.tail()` — tail returns Seq.
#[test]
#[timeout(30000)]
fn collection_sort_result_eq_tail() {
    let ensures = vec![eq(var("result"), method_call(var("s"), "tail", vec![]))];
    assert!(result_collection_sort_from_postcondition(&ensures).is_some());
}

/// `result > 0` — Int comparison, no collection sort.
#[test]
#[timeout(30000)]
fn collection_sort_int_comparison_returns_none() {
    let ensures = vec![gt(var("result"), int(0))];
    assert_eq!(result_collection_sort_from_postcondition(&ensures), None);
}

/// Empty postconditions return None.
#[test]
#[timeout(30000)]
fn collection_sort_empty_ensures() {
    assert_eq!(result_collection_sort_from_postcondition(&[]), None);
}

/// `result == 42` — Int equality, no collection sort.
#[test]
#[timeout(30000)]
fn collection_sort_result_eq_int_returns_none() {
    let ensures = vec![eq(var("result"), int(42))];
    assert_eq!(result_collection_sort_from_postcondition(&ensures), None);
}

/// Collection sort inside logical connector: `x > 0 && result == s.reverse()`.
#[test]
#[timeout(30000)]
fn collection_sort_inside_and_connector() {
    let ensures = vec![and(
        gt(var("x"), int(0)),
        eq(var("result"), method_call(var("s"), "reverse", vec![])),
    )];
    assert!(result_collection_sort_from_postcondition(&ensures).is_some());
}

/// Collection sort inside implies: `x > 0 ==> result == s.concat(t)`.
#[test]
#[timeout(30000)]
fn collection_sort_inside_implies() {
    let ensures = vec![implies(
        gt(var("x"), int(0)),
        eq(
            var("result"),
            method_call(var("s"), "concat", vec![var("t")]),
        ),
    )];
    assert!(result_collection_sort_from_postcondition(&ensures).is_some());
}

/// Second ensures clause provides collection sort.
#[test]
#[timeout(30000)]
fn collection_sort_second_clause() {
    let ensures = vec![
        gt(var("result_len"), int(0)),
        eq(var("result"), method_call(var("s"), "reverse", vec![])),
    ];
    assert!(result_collection_sort_from_postcondition(&ensures).is_some());
}

/// `result.len() == s.len()` — result is receiver of len(), not in Eq with
/// a collection expression. No collection sort inference.
#[test]
#[timeout(30000)]
fn collection_sort_result_as_receiver_no_inference() {
    let ensures = vec![eq(
        method_call(var("result"), "len", vec![]),
        method_call(var("s"), "len", vec![]),
    )];
    assert_eq!(result_collection_sort_from_postcondition(&ensures), None);
}

/// Context-aware inference: `result.ext_eq(m_snap)` should recover FMap from a
/// declared argument even though there is no `result == <expr>` equality.
#[test]
#[timeout(30000)]
fn collection_sort_result_ext_eq_receiver_uses_declared_fmap_context() {
    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("m_snap", Sort::Uninterpreted("FMap".to_string()))
        .expect("declare FMap snapshot");

    let ensures = vec![method_call(var("result"), "ext_eq", vec![var("m_snap")])];

    assert_eq!(
        result_collection_sort_from_postcondition_with_context(&mut encoder, &ensures),
        Some(Sort::Uninterpreted("FMap".to_string())),
        "receiver-style ext_eq should recover FMap sort from encoder context"
    );
}

/// Receiver-style `len()` stays ambiguous even with context — only the narrow
/// `ext_eq` bridge participates in result collection inference.
#[test]
#[timeout(30000)]
fn collection_sort_result_len_receiver_still_none_with_context() {
    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("s", Sort::seq(Sort::Int))
        .expect("declare Seq witness");

    let ensures = vec![eq(
        method_call(var("result"), "len", vec![]),
        method_call(var("s"), "len", vec![]),
    )];

    assert_eq!(
        result_collection_sort_from_postcondition_with_context(&mut encoder, &ensures),
        None,
        "ambiguous receiver-style len() should not force a collection carrier"
    );
}
