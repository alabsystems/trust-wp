// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `collection_dispatch.rs` sort-aware routing.
//!
//! Verifies that ambiguous collection methods (len, index, get, contains,
//! is_empty, set, remove, intersection, difference) route to the correct
//! Seq/FMap/FSet/Mapping encoder based on receiver sort annotations and hints.
//!
//! These tests use real AYEncoder instances to exercise the full dispatch
//! chain including sort inference fallbacks.

use std::sync::Arc;

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, ExprSort, PureExpr};

use crate::{
    encoder::AYEncoder,
    tests::helpers::{int, named_field, var, var_with_sort, view},
};

// ── Helper: build a Seq-annotated receiver ──────────────────────────

fn seq_receiver(name: &str) -> PureExpr {
    var_with_sort(name, ExprSort::Seq)
}

fn fmap_receiver(name: &str) -> PureExpr {
    var_with_sort(name, ExprSort::FMap)
}

fn bare_receiver(name: &str) -> PureExpr {
    var(name)
}

// ── encode_len_dispatch ─────────────────────────────────────────────

#[test]
#[timeout(30000)]
fn len_dispatch_seq_annotated_receiver_succeeds() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_len_dispatch(&seq_receiver("v"), &[], None);
    assert!(
        result.is_ok(),
        "Seq-annotated receiver len should succeed: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn len_dispatch_fmap_annotated_receiver_succeeds() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_len_dispatch(&fmap_receiver("m"), &[], None);
    assert!(
        result.is_ok(),
        "FMap-annotated receiver len should succeed: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn len_dispatch_bare_receiver_falls_to_fset() {
    let mut encoder = AYEncoder::new();
    // Bare receiver with no annotations or hints → falls through to fset_len
    let result = encoder.encode_len_dispatch(&bare_receiver("s"), &[], None);
    assert!(
        result.is_ok(),
        "bare receiver len should succeed via fset fallback: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn len_dispatch_seq_hint_receiver_routes_to_seq() {
    let mut encoder = AYEncoder::new();
    // Record a Seq sort hint for the variable, then use a bare receiver
    encoder.record_sort_hint("v".to_string(), ExprSort::Seq);
    let result = encoder.encode_len_dispatch(&bare_receiver("v"), &[], None);
    assert!(
        result.is_ok(),
        "Seq-hinted receiver len should succeed: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn len_dispatch_fmap_hint_receiver_routes_to_fmap() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("m".to_string(), ExprSort::FMap);
    let result = encoder.encode_len_dispatch(&bare_receiver("m"), &[], None);
    assert!(
        result.is_ok(),
        "FMap-hinted receiver len should succeed: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn len_dispatch_structural_field_view_receiver_reuses_seq_placeholder() {
    let mut encoder = AYEncoder::new();
    let iter_mut_sort = Sort::Uninterpreted("IterMut".to_string());
    let _ = encoder
        .get_or_declare_var("self", iter_mut_sort)
        .expect("declare self as IterMut");
    let receiver = view(named_field("inner", bare_receiver("self")));

    let result = encoder.encode_len_dispatch(&receiver, &[], None);
    assert!(
        result.is_ok(),
        "View(structural field).len() should route through Seq: {result:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_some(),
        "structural field len should initialize Seq theory"
    );
    assert!(
        !encoder.decls().has_spec_func("fset_len"),
        "structural field len must not fall through to fset_len"
    );
    assert!(
        encoder
            .seq_state_for_test()
            .get_bridge_fn("__int_to_seq_bridge")
            .is_none(),
        "structural field len should reuse a Seq placeholder, not the Int->Seq bridge"
    );
}

// ── encode_index_get_dispatch ───────────────────────────────────────

#[test]
#[timeout(30000)]
fn index_get_dispatch_seq_annotated_receiver() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_index_get_dispatch(&seq_receiver("v"), "get", &[int(0)], None);
    assert!(
        result.is_ok(),
        "Seq-annotated receiver get should succeed: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn index_get_dispatch_fmap_annotated_receiver() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_index_get_dispatch(&fmap_receiver("m"), "get", &[int(0)], None);
    assert!(
        result.is_ok(),
        "FMap-annotated receiver get should succeed: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn index_dispatch_bare_receiver_falls_to_fmap() {
    let mut encoder = AYEncoder::new();
    // Bare receiver with no annotations → falls through to fmap
    let result = encoder.encode_index_get_dispatch(&bare_receiver("x"), "index", &[int(0)], None);
    assert!(
        result.is_ok(),
        "bare receiver index should succeed via fmap fallback: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn get_ghost_strips_suffix() {
    let mut encoder = AYEncoder::new();
    let result =
        encoder.encode_index_get_dispatch(&seq_receiver("v"), "get_ghost", &[int(0)], None);
    assert!(
        result.is_ok(),
        "get_ghost should strip suffix and succeed: {result:?}"
    );
}

// ── encode_index_logic_dispatch ─────────────────────────────────────

#[test]
#[timeout(30000)]
fn index_logic_seq_annotated_int_key() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_index_logic_dispatch(&seq_receiver("v"), &[int(0)], None);
    assert!(
        result.is_ok(),
        "Seq-annotated index_logic with Int key should succeed: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn index_logic_fmap_annotated() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_index_logic_dispatch(&fmap_receiver("m"), &[int(0)], None);
    assert!(
        result.is_ok(),
        "FMap-annotated index_logic should succeed: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn index_logic_bare_receiver_defaults_to_fmap() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_index_logic_dispatch(&bare_receiver("x"), &[int(0)], None);
    assert!(
        result.is_ok(),
        "bare receiver index_logic should fall to fmap: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn index_logic_native_seq_key_in_var_sorts_avoids_seq_indexing() {
    let mut encoder = AYEncoder::new();
    let seq_sort = Sort::seq(Sort::Int);
    let _ = encoder.solver.declare_const("k", seq_sort.clone());
    encoder
        .var_sorts_mut_for_test()
        .insert("k".to_string(), seq_sort);

    let result =
        encoder.encode_index_logic_dispatch(&seq_receiver("v"), &[bare_receiver("k")], None);
    assert!(
        result.is_ok(),
        "Seq receiver with native Seq key in var_sorts should avoid seq indexing: {result:?}"
    );
    assert!(
        encoder
            .decls()
            .logic_func_names()
            .any(|name| name.starts_with("method_index_logic_2")),
        "Seq-keyed index_logic should use the non-Seq fallback UF"
    );
    assert!(
        !encoder
            .decls()
            .logic_func_names()
            .any(|name| name.starts_with("seq_")),
        "Seq-keyed index_logic must avoid Seq indexing symbols"
    );
}

#[test]
#[timeout(30000)]
fn index_logic_bool_hinted_current_key_on_unclassified_view_uses_bool_fallback() {
    let mut encoder = AYEncoder::new();
    let receiver = view(var("cell"));
    let key = PureExpr::Deref(Arc::new(var("s")));
    let hinted_lookup = PureExpr::MethodCall {
        receiver: Arc::new(receiver.clone()),
        method: "index_logic".to_string(),
        args: vec![key.clone()],
    };
    let bool_context = PureExpr::BinOp(
        Arc::new(hinted_lookup),
        trust_wp_core::formula::BinOp::Eq,
        Arc::new(PureExpr::Bool(true)),
    );

    encoder.register_formula_sort_hints(std::slice::from_ref(&bool_context));

    let result = encoder.encode_index_logic_dispatch(&receiver, &[key], None);
    assert!(
        result.is_ok(),
        "Bool-hinted current-key unclassified lookup should encode: {result:?}"
    );
    assert!(
        encoder
            .decls()
            .logic_func_names()
            .any(|name| name.starts_with("method_index_logic_2")),
        "Bool-hinted current-key unclassified lookup should use Bool-UF fallback"
    );
}

#[test]
#[timeout(30000)]
fn index_logic_quantified_seq_key_on_predcell_view_uses_bool_fallback() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let predcell = ExprSort::Ref(Box::new(ExprSort::Datatype(intern_sort_name(
        "trust_wp_std::std::cell::PredCell",
    ))));
    let seq_ref = ExprSort::Ref(Box::new(ExprSort::Seq));
    let seq_key = PureExpr::Deref(Arc::new(var("s")));
    let predicate_index = PureExpr::MethodCall {
        receiver: Arc::new(view(var_with_sort("cell", predcell))),
        method: "index_logic".to_string(),
        args: vec![seq_key],
    };
    let seq_len = PureExpr::MethodCall {
        receiver: Arc::new(view(var("s"))),
        method: "len".to_string(),
        args: vec![],
    };
    let quantified = PureExpr::Forall {
        var: "s".to_string(),
        var_sort: Some(seq_ref),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(predicate_index),
            trust_wp_core::formula::BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(seq_len),
                trust_wp_core::formula::BinOp::Eq,
                Arc::new(int(2)),
            )),
        )),
        triggers: vec![],
    };

    encoder.register_formula_sort_hints(std::slice::from_ref(&quantified));
    encoder.register_sort_hints(std::slice::from_ref(&quantified));

    let result = encoder.encode_pure(&quantified);
    assert!(
        result.is_ok(),
        "quantified PredCell Seq-key lookup should encode: {result:?}"
    );
    assert!(
        encoder
            .decls()
            .logic_func_names()
            .any(|name| name.starts_with("method_index_logic_2")),
        "quantified PredCell Seq-key lookup should use Bool-UF fallback"
    );
}

// ── encode_contains_dispatch ────────────────────────────────────────

#[test]
#[timeout(30000)]
fn contains_dispatch_seq_annotated() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_contains_dispatch(&seq_receiver("v"), &[int(42)], None);
    assert!(
        result.is_ok(),
        "Seq-annotated contains should succeed: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn contains_dispatch_fmap_annotated() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_contains_dispatch(&fmap_receiver("m"), &[int(42)], None);
    assert!(
        result.is_ok(),
        "FMap-annotated contains should succeed: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn contains_dispatch_bare_receiver_falls_to_fset() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_contains_dispatch(&bare_receiver("s"), &[int(42)], None);
    assert!(
        result.is_ok(),
        "bare receiver contains should succeed via fset fallback: {result:?}"
    );
}

// ── encode_is_empty_dispatch ────────────────────────────────────────

#[test]
#[timeout(30000)]
fn is_empty_dispatch_seq_annotated() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_is_empty_dispatch(&seq_receiver("v"), &[], None);
    assert!(
        result.is_ok(),
        "Seq-annotated is_empty should succeed: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn is_empty_dispatch_seq_returns_bool() {
    let mut encoder = AYEncoder::new();
    let term = encoder
        .encode_is_empty_dispatch(&seq_receiver("v"), &[], None)
        .expect("should succeed");
    let sort = encoder.solver.get_sort(term);
    assert_eq!(sort, Sort::Bool, "is_empty should return Bool sort");
}

#[test]
#[timeout(30000)]
fn is_empty_dispatch_bare_falls_to_fset() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_is_empty_dispatch(&bare_receiver("s"), &[], None);
    assert!(
        result.is_ok(),
        "bare receiver is_empty should succeed via fset: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn is_empty_dispatch_seq_hint_routes_to_seq() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("v".to_string(), ExprSort::Seq);
    let term = encoder
        .encode_is_empty_dispatch(&bare_receiver("v"), &[], None)
        .expect("should succeed with Seq hint");
    let sort = encoder.solver.get_sort(term);
    assert_eq!(sort, Sort::Bool, "Seq is_empty via hint should return Bool");
}

// ── encode_set_dispatch ─────────────────────────────────────────────

#[test]
#[timeout(30000)]
fn set_dispatch_seq_annotated() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_set_dispatch(&seq_receiver("v"), &[int(0), int(42)], None);
    assert!(
        result.is_ok(),
        "Seq-annotated set should succeed: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn set_dispatch_bare_falls_to_int_uf() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_set_dispatch(&bare_receiver("x"), &[int(0), int(42)], None);
    assert!(
        result.is_ok(),
        "bare receiver set should succeed via Int UF fallback: {result:?}"
    );
}

// ── encode_remove_dispatch ──────────────────────────────────────────

#[test]
#[timeout(30000)]
fn remove_dispatch_seq_falls_to_int_uf() {
    let mut encoder = AYEncoder::new();
    // Seq doesn't define remove — should fall through to Int UF
    let result = encoder.encode_remove_dispatch(&seq_receiver("v"), &[int(0)], None);
    assert!(
        result.is_ok(),
        "Seq receiver remove should succeed via Int UF: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn remove_dispatch_bare_receiver_falls_to_fset() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_remove_dispatch(&bare_receiver("s"), &[int(42)], None);
    assert!(
        result.is_ok(),
        "bare receiver remove should succeed via fset: {result:?}"
    );
}

// ── encode_set_op_dispatch ──────────────────────────────────────────

#[test]
#[timeout(30000)]
fn intersection_dispatch_bare_falls_to_fset() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_set_op_dispatch(
        &bare_receiver("a"),
        "intersection",
        &[bare_receiver("b")],
        None,
    );
    assert!(
        result.is_ok(),
        "bare receiver intersection should succeed via fset: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn difference_dispatch_bare_falls_to_fset() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_set_op_dispatch(
        &bare_receiver("a"),
        "difference",
        &[bare_receiver("b")],
        None,
    );
    assert!(
        result.is_ok(),
        "bare receiver difference should succeed via fset: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn set_op_dispatch_seq_falls_to_int_uf() {
    let mut encoder = AYEncoder::new();
    // Seq doesn't define intersection — should fall through to Int UF
    let result = encoder.encode_set_op_dispatch(
        &seq_receiver("v"),
        "intersection",
        &[seq_receiver("w")],
        None,
    );
    assert!(
        result.is_ok(),
        "Seq receiver intersection should succeed via Int UF: {result:?}"
    );
}

// ── Sort consistency across dispatch methods ────────────────────────

/// Verify that len + is_empty agree on sort routing for Seq receivers.
/// Both should treat a Seq-annotated receiver as Seq.
#[test]
#[timeout(30000)]
fn len_and_is_empty_agree_on_seq_routing() {
    let mut encoder = AYEncoder::new();
    let receiver = seq_receiver("v");

    let len_result = encoder.encode_len_dispatch(&receiver, &[], None);
    assert!(
        len_result.is_ok(),
        "len should succeed for Seq: {len_result:?}"
    );

    let is_empty_result = encoder.encode_is_empty_dispatch(&receiver, &[], None);
    assert!(
        is_empty_result.is_ok(),
        "is_empty should succeed for Seq: {is_empty_result:?}"
    );
}

/// Verify that len + contains agree on sort routing for FMap receivers.
#[test]
#[timeout(30000)]
fn len_and_contains_agree_on_fmap_routing() {
    let mut encoder = AYEncoder::new();
    let receiver = fmap_receiver("m");

    let len_result = encoder.encode_len_dispatch(&receiver, &[], None);
    assert!(
        len_result.is_ok(),
        "len should succeed for FMap: {len_result:?}"
    );

    let contains_result = encoder.encode_contains_dispatch(&receiver, &[int(42)], None);
    assert!(
        contains_result.is_ok(),
        "contains should succeed for FMap: {contains_result:?}"
    );
}

/// Verify that view-wrapped Seq receivers route correctly through all methods.
#[test]
#[timeout(30000)]
fn view_wrapped_seq_receiver_routes_correctly() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("v".to_string(), ExprSort::Seq);
    let receiver = view(bare_receiver("v"));

    let len_result = encoder.encode_len_dispatch(&receiver, &[], None);
    assert!(
        len_result.is_ok(),
        "view-wrapped Seq len should succeed: {len_result:?}"
    );

    let is_empty_result = encoder.encode_is_empty_dispatch(&receiver, &[], None);
    assert!(
        is_empty_result.is_ok(),
        "view-wrapped Seq is_empty should succeed: {is_empty_result:?}"
    );
}
