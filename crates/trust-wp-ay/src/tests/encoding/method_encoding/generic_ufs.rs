// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_encode_deep_model_as_uninterpreted() {
    // x.deep_model() should encode as an Int-returning uninterpreted function.
    // UF name: method_deep_model_1_i (1 param = receiver, sort = Int).
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("x"), "deep_model", vec![]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("deep_model should encode as uninterpreted function");
    assert!(
        encoder.decls().has_logic_func("method_deep_model_1_i"),
        "deep_model should declare method_deep_model_1_i UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_encode_capacity_as_uninterpreted() {
    // v.capacity() should encode as an Int-returning uninterpreted function.
    // UF name: method_capacity_1_i (1 param = receiver, sort = Int).
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("v"), "capacity", vec![]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("capacity should encode as uninterpreted function");
    assert!(
        encoder.decls().has_logic_func("method_capacity_1_i"),
        "capacity should declare method_capacity_1_i UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_encode_produces_as_bool_predicate() {
    // iter.produces(seq, next_iter) should encode as a Bool predicate.
    // UF name: method_produces_3_i_s_i (3 params: receiver=Int, visited=Seq, o=Int).
    // Seq sort maps to "s" in method_sort_tag after Sort::Seq migration.
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("iter"), "produces", vec![var("seq"), var("next")]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("produces should encode as Bool predicate");
    assert!(
        encoder.decls().has_logic_func("method_produces_3_i_s_i"),
        "produces should declare method_produces_3_i_s_i UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_encode_namespace_as_uninterpreted() {
    // token.namespace() should encode as an Int-returning UF.
    // UF name: method_namespace_1_i (1 param = receiver, sort = Int).
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("token"), "namespace", vec![]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("namespace should encode as uninterpreted function");
    assert!(
        encoder.decls().has_logic_func("method_namespace_1_i"),
        "namespace should declare method_namespace_1_i UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_encode_id_as_uninterpreted() {
    // x.id() should encode as an Int-returning UF.
    // UF name: method_id_1_i (1 param = receiver, sort = Int).
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("x"), "id", vec![]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("id should encode as uninterpreted function");
    assert!(
        encoder.decls().has_logic_func("method_id_1_i"),
        "id should declare method_id_1_i UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_encode_set_as_uninterpreted() {
    // ghost.set(val) should encode as an Int-returning UF.
    // UF name: method_set_2_i_i (2 params: receiver=Int, val=Int).
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("ghost"), "set", vec![var("val")]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("set should encode as uninterpreted function");
    assert!(
        encoder.decls().has_logic_func("method_set_2_i_i"),
        "set should declare method_set_2_i_i UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_encode_map_as_int_uf() {
    // collection.map(f) returns a new collection (Int), not Bool (#885).
    // UF name: method_map_2_i_i (2 params: receiver=Int, f=Int; returns Int).
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("coll"), "map", vec![var("f")]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("map should encode as Int UF");
    assert!(
        encoder.decls().has_logic_func("method_map_2_i_i"),
        "map should declare method_map_2_i_i UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

#[test]
#[timeout(30000)]
fn test_encode_filter_as_int_uf() {
    // collection.filter(pred) returns a new collection (Int), not Bool (#885).
    // UF name: method_filter_2_i_i (2 params: receiver=Int, pred=Int; returns Int).
    let mut encoder = AYEncoder::new();

    let expr = method_call(var("coll"), "filter", vec![var("pred")]);

    let _term = encoder
        .encode_pure(&expr)
        .expect("filter should encode as Int UF");
    assert!(
        encoder.decls().has_logic_func("method_filter_2_i_i"),
        "filter should declare method_filter_2_i_i UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

/// Regression: fset.map(f).contains(x) must not panic (#885).
/// Before fix, map() encoded as Bool, and contains() expected Int receiver.
#[test]
#[timeout(30000)]
fn test_map_then_contains_no_sort_mismatch() {
    let mut encoder = AYEncoder::new();

    // fset.map(f).contains(x) — chained method call
    let map_result = method_call(var("fset"), "map", vec![var("f")]);
    let contains_expr = method_call(map_result, "contains", vec![var("x")]);

    let result = encoder.encode_pure(&contains_expr);
    assert!(
        result.is_ok(),
        "map().contains() must not panic with sort mismatch: {result:?}"
    );
}

/// Regression: fset.filter(f).contains(x) must not panic (#885).
#[test]
#[timeout(30000)]
fn test_filter_then_contains_no_sort_mismatch() {
    let mut encoder = AYEncoder::new();

    // fset.filter(pred).contains(x) — chained method call
    let filter_result = method_call(var("fset"), "filter", vec![var("pred")]);
    let contains_expr = method_call(filter_result, "contains", vec![var("x")]);

    let result = encoder.encode_pure(&contains_expr);
    assert!(
        result.is_ok(),
        "filter().contains() must not panic with sort mismatch: {result:?}"
    );
}

/// Regression: `get()` in Bool context must encode as Bool and avoid
/// `mk_and` sort panics. (#885)
#[test]
#[timeout(30000)]
fn test_get_in_bool_context_encodes_as_bool_predicate() {
    let mut encoder = AYEncoder::new();

    let expr = and(
        method_call(var("xs"), "contains", vec![var("x")]),
        method_call(var("f"), "get", vec![var("x")]),
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Bool-context get() should encode without sort panic: {result:?}"
    );
    assert!(
        encoder.decls().has_logic_func("method_get_2_i_i"),
        "Bool-context get() should declare Bool method UF; found: {:?}",
        encoder.decls().logic_func_names().collect::<Vec<_>>()
    );
}

/// Regression: view-shaped non-Seq `ext_eq` must not force Seq encoding.
/// Before fix, this could route to Seq and panic with `mk_eq(Seq, Int)`.
#[test]
#[timeout(30000)]
fn test_encode_ext_eq_view_non_seq_fallback() {
    let mut encoder = AYEncoder::new();

    let expr = method_call(view(var("m1")), "ext_eq", vec![view(var("m2"))]);
    let result = encoder.encode_pure(&expr);

    assert!(
        result.is_ok(),
        "view-shaped non-Seq ext_eq should not panic: {result:?}"
    );
}

/// Regression: constructor match over non-datatype scrutinee should
/// gracefully fall back to UF testers/accessors instead of panicking
/// in `datatype_selector`. (#885)
#[test]
#[timeout(30000)]
fn test_match_constructor_on_non_datatype_scrutinee_no_panic() {
    let mut encoder = AYEncoder::new();

    let scrutinee = method_call(var("m"), "get", vec![var("i")]);
    let expr = match_expr(
        scrutinee,
        vec![
            (
                Pattern::Constructor {
                    name: "Some".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "None".into(),
                    inner: None,
                },
                int(0),
            ),
        ],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "constructor match over Int scrutinee should not panic: {result:?}"
    );
}
