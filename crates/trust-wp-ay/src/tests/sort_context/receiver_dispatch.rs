// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Focused regression tests for method dispatch correctness based on
//! receiver sort classification. (#994 Phase 3 Slice 2)
//!
//! These tests model the exact receiver shapes from the `collections`
//! and collection-oriented compatibility fixtures:
//!
//! - `collections` failure: `seq_len ... got FMap` and `seq_contains ... got Tuple2`
//!   → FMap-annotated receivers misrouted through Seq dispatch
//! - Seq dispatch failures in loop contexts
//!   → Seq-annotated receivers need correct dispatch
//!
//! Each test creates a `AYEncoder`, builds a `PureExpr::MethodCall` with a
//! specific receiver annotation/hint shape, encodes it, and asserts the
//! correct dispatch path was taken by checking which UF was declared.

use ntest::timeout;
use trust_wp_core::formula::intern_sort_name;

use super::*;

// ── Helpers ─────────────────────────────────────────────────────────

fn fmap_var(name: &str) -> PureExpr {
    let id = intern_sort_name("HashMap");
    PureExpr::Var(name.to_string(), Some(ExprSort::Datatype(id)))
}

fn seq_var(name: &str) -> PureExpr {
    let id = intern_sort_name("VecDeque");
    PureExpr::Var(name.to_string(), Some(ExprSort::Datatype(id)))
}

fn ref_fmap_var(name: &str) -> PureExpr {
    let id = intern_sort_name("HashMap");
    PureExpr::Var(
        name.to_string(),
        Some(ExprSort::Ref(Box::new(ExprSort::Datatype(id)))),
    )
}

fn ref_seq_var(name: &str) -> PureExpr {
    let id = intern_sort_name("VecDeque");
    PureExpr::Var(
        name.to_string(),
        Some(ExprSort::Ref(Box::new(ExprSort::Datatype(id)))),
    )
}

// ── FMap receiver dispatch: len ─────────────────────────────────────

/// FMap-annotated receiver (HashMap) calling `.len()` must dispatch to
/// `fmap_len`, NOT `seq_len` or `fset_len`. (#994 `collections` RC2)
#[test]
#[timeout(30000)]
fn test_fmap_annotated_receiver_len_dispatches_to_fmap() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(fmap_var("m"), "len", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(result.is_ok(), "FMap .len() must encode: {result:?}");
    assert!(
        encoder.decls().has_spec_func("fmap_len"),
        "HashMap .len() must declare fmap_len"
    );
    assert!(
        !encoder.decls().has_spec_func("fset_len"),
        "HashMap .len() must NOT declare fset_len"
    );
}

/// View(Deref(Var("m", Ref(Datatype(HashMap))))) calling `.len()` must still
/// dispatch to FMap. This is the common pattern for `&mut HashMap` receivers
/// in function bodies after MIR lowering. (#994 `collections` RC2)
#[test]
#[timeout(30000)]
fn test_view_deref_fmap_receiver_len_dispatches_to_fmap() {
    let mut encoder = AYEncoder::new();
    let receiver = view(deref(ref_fmap_var("m")));
    let expr = method_call(receiver, "len", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "View(Deref(HashMap)) .len() must encode: {result:?}"
    );
    assert!(
        encoder.decls().has_spec_func("fmap_len"),
        "View(Deref(HashMap)) .len() must declare fmap_len"
    );
    assert!(
        !encoder.decls().has_spec_func("fset_len"),
        "View(Deref(HashMap)) .len() must NOT declare fset_len"
    );
}

// ── FMap receiver dispatch: contains ────────────────────────────────

/// FMap-annotated receiver calling `.contains(k)` must dispatch to
/// `fmap_contains`, NOT `fset_contains`. (#994 `collections` RC2)
#[test]
#[timeout(30000)]
fn test_fmap_annotated_receiver_contains_dispatches_to_fmap() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(fmap_var("m"), "contains", vec![var("k")]);

    let result = encoder.encode_pure(&expr);
    assert!(result.is_ok(), "FMap .contains() must encode: {result:?}");
    assert!(
        encoder.decls().has_spec_func("fmap_contains"),
        "HashMap .contains() must declare fmap_contains"
    );
    assert!(
        !encoder.decls().has_spec_func("fset_contains"),
        "HashMap .contains() must NOT declare fset_contains"
    );
}

// ── FMap receiver dispatch: get ─────────────────────────────────────

/// FMap-annotated receiver calling `.get(k)` must dispatch to
/// `fmap_lookup`. (#994 `collections` RC2)
#[test]
#[timeout(30000)]
fn test_fmap_annotated_receiver_get_dispatches_to_fmap() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(fmap_var("m"), "get", vec![var("k")]);

    let result = encoder.encode_pure(&expr);
    assert!(result.is_ok(), "FMap .get() must encode: {result:?}");
    assert!(
        encoder.decls().has_spec_func("fmap_lookup"),
        "HashMap .get() must declare fmap_lookup"
    );
}

// ── Seq receiver dispatch: len ──────────────────────────────────────

/// Seq-annotated receiver (Datatype(VecDeque)) calling `.len()` must dispatch
/// to Seq theory (seq_len), NOT fmap_len or fset_len.
/// (#994)
#[test]
#[timeout(30000)]
fn test_seq_receiver_len_dispatches_to_seq() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(seq_var("l"), "len", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(result.is_ok(), "VecDeque .len() must encode: {result:?}");
    assert!(
        !encoder.decls().has_spec_func("fmap_len"),
        "VecDeque .len() must NOT declare fmap_len"
    );
    assert!(
        !encoder.decls().has_spec_func("fset_len"),
        "VecDeque .len() must NOT declare fset_len"
    );
}

/// View(Deref(Var("l", Ref(Datatype(VecDeque))))) calling `.len()` must dispatch
/// to Seq under the common wrapper pattern.
#[test]
#[timeout(30000)]
fn test_view_deref_seq_receiver_len_dispatches_to_seq() {
    let mut encoder = AYEncoder::new();
    let receiver = view(deref(ref_seq_var("l")));
    let expr = method_call(receiver, "len", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "View(Deref(VecDeque)) .len() must encode: {result:?}"
    );
    assert!(
        !encoder.decls().has_spec_func("fmap_len"),
        "View(Deref(VecDeque)) .len() must NOT declare fmap_len"
    );
    assert!(
        !encoder.decls().has_spec_func("fset_len"),
        "View(Deref(VecDeque)) .len() must NOT declare fset_len"
    );
}

// ── Seq receiver dispatch: index ────────────────────────────────────

/// Seq-annotated receiver calling `.index(i)` must dispatch to Seq theory,
/// NOT FMap. (#994)
#[test]
#[timeout(30000)]
fn test_seq_receiver_index_dispatches_to_seq() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(seq_var("l"), "index", vec![var("i")]);

    let result = encoder.encode_pure(&expr);
    assert!(result.is_ok(), "VecDeque .index() must encode: {result:?}");
    assert!(
        !encoder.decls().has_spec_func("fmap_lookup"),
        "VecDeque .index() must NOT declare fmap_lookup"
    );
}

// ── FMap receiver dispatch via sort hint (no annotation) ────────────

/// When a receiver has no annotation but the sort resolver has an FMap hint,
/// `.len()` must dispatch to fmap_len. (#994)
///
/// This models loop-generated variables that lose their original annotations
/// but retain sort hints from the prescan. The prescan's ambiguous-method
/// heuristic (`is_ambiguous_seq`) must NOT override the explicit FMap hint
/// with Seq. Without the `record_sort_hint` priority guard, View(Var("m"))
/// receivers with FMap hints get misclassified as Seq.
#[test]
#[timeout(30000)]
fn test_unannotated_receiver_with_fmap_hint_len_dispatches_to_fmap() {
    let mut encoder = AYEncoder::new();
    // Register an FMap sort hint on the view name for this var
    encoder.record_sort_hint("m_view".to_string(), ExprSort::FMap);

    // View(Var("m", None)) — no annotation, but hint is set
    let receiver = view(var("m"));
    let expr = method_call(receiver, "len", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "unannotated .len() with FMap hint must encode: {result:?}"
    );

    // The FMap hint must survive the prescan's ambiguous-method Seq heuristic.
    let view_sort = encoder.var_sorts_for_test().get("m_view");
    let fmap = Sort::Uninterpreted("FMap".to_string());
    assert_eq!(
        view_sort,
        Some(&fmap),
        "m_view must retain FMap sort despite prescan Seq heuristic"
    );

    assert!(
        encoder.decls().has_spec_func("fmap_len"),
        "unannotated .len() with FMap hint must declare fmap_len"
    );
    assert!(
        !encoder.decls().has_spec_func("fset_len"),
        "unannotated .len() with FMap hint must NOT declare fset_len"
    );
}

/// A concrete registered FMap sort must beat a conflicting Seq hint on the
/// synthesized view name. Otherwise `m@.get(k)` falls into Seq dispatch and
/// panics with `seq_get ... got FMap`, matching the remaining `#2116`
/// compat failure in `roundtrip_hashmap_*`.
#[test]
#[timeout(30000)]
fn test_declared_fmap_sort_beats_conflicting_seq_hint_on_view_receiver() {
    let mut encoder = AYEncoder::new();
    let fmap = Sort::Uninterpreted("FMap".to_string());
    encoder
        .get_or_declare_var("m", fmap.clone())
        .expect("declare m with FMap sort");
    encoder.record_sort_hint("m_view".to_string(), ExprSort::Seq);

    let receiver = view(var("m"));
    assert!(
        !encoder.is_seq_receiver(&receiver, None),
        "declared FMap sort must override conflicting Seq hint"
    );
    assert!(
        encoder.is_fmap_receiver(&receiver, None),
        "view receiver should still classify as FMap"
    );

    let expr = method_call(receiver, "get", vec![var("k")]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "view receiver with declared FMap sort must encode through fmap lookup: {result:?}"
    );
    assert_eq!(
        encoder.var_sort("m_view"),
        Some(&fmap),
        "view receiver must declare m_view as FMap, not inherit a stale Seq hint"
    );
    assert!(
        encoder.decls().has_spec_func("fmap_lookup"),
        "FMap view receiver get() must declare fmap_lookup"
    );
}

/// Unannotated receiver with Seq hint dispatches `.len()` to Seq. (#994)
#[test]
#[timeout(30000)]
fn test_unannotated_receiver_with_seq_hint_len_dispatches_to_seq() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("l_view".to_string(), ExprSort::Seq);

    let receiver = view(var("l"));
    let expr = method_call(receiver, "len", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "unannotated .len() with Seq hint must encode: {result:?}"
    );
    assert!(
        !encoder.decls().has_spec_func("fmap_len"),
        "unannotated .len() with Seq hint must NOT declare fmap_len"
    );
    assert!(
        !encoder.decls().has_spec_func("fset_len"),
        "unannotated .len() with Seq hint must NOT declare fset_len"
    );
}

/// Receiver classification should reuse the shared derived-name fallback chain
/// instead of requiring the exact synthesized alias to carry the Seq hint.
/// Otherwise `old(^v@)` misses the existing `v_view` hint. (#2020)
#[test]
#[timeout(30000)]
fn test_is_seq_receiver_composes_final_old_view_fallbacks() {
    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("v_view".to_string(), ExprSort::Seq);

    let receiver = old(view(final_expr(var("v"))));

    assert!(
        encoder.is_seq_receiver(&receiver, None),
        "final_old_v_view should classify as Seq via the shared fallback chain"
    );
}

/// Nested mut-ref carriers should keep peeling through the synthesized derived
/// name when classifying receivers. Otherwise `(*^self_)@.tail()` still looks
/// like `&mut [T]` instead of Seq and falls out of Seq dispatch. (#1805)
#[test]
#[timeout(30000)]
fn test_nested_mutref_seq_receiver_tail_uses_multi_peel_projection() {
    let mut encoder = AYEncoder::new();
    let nested_seq = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::MutRef(
        Box::new(ExprSort::Seq),
    ))));
    encoder
        .get_or_declare_var("self_", nested_seq)
        .expect("declare nested mutref self_");

    let receiver = view(deref(final_expr(var("self_"))));
    assert!(
        encoder.is_seq_receiver(&receiver, None),
        "(*^self_)@ should classify as Seq via repeated derived-name peeling"
    );

    let expr = method_call(receiver, "tail", vec![]);
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "(*^self_)@.tail() should encode through Seq dispatch: {result:?}"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_some(),
        "tail on (*^self_)@ should initialize Seq functions"
    );
}

// ── Inferred-sort fallback for unannotated + no-hint receivers ──────

/// When a receiver has FMap sort in var_sorts but no annotation or hint,
/// the inferred-sort fallback in `encode_method_call_impl` should catch it.
/// This tests the `infer_encoded_sort` safety net. (#994)
#[test]
#[timeout(30000)]
fn test_var_sorts_fmap_receiver_len_uses_inferred_fallback() {
    let mut encoder = AYEncoder::new();

    // Declare the variable with FMap sort in var_sorts
    let fmap_sort = Sort::Uninterpreted("FMap".to_string());
    let _var_term = encoder.solver.declare_const("m", fmap_sort.clone());
    encoder
        .var_sorts_mut_for_test()
        .insert("m".to_string(), fmap_sort);

    // Bare Var("m", None) — no annotation, no hint, but var_sorts knows it
    let expr = method_call(var("m"), "len", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "var_sorts FMap .len() must encode: {result:?}"
    );
    assert!(
        encoder.decls().has_spec_func("fmap_len"),
        "var_sorts FMap .len() must declare fmap_len via inferred-sort fallback"
    );
    assert!(
        !encoder.decls().has_spec_func("fset_len"),
        "var_sorts FMap .len() must NOT declare fset_len"
    );
}

/// Same as above but for Seq sort in var_sorts. (#994)
#[test]
#[timeout(30000)]
fn test_var_sorts_seq_receiver_len_uses_inferred_fallback() {
    let mut encoder = AYEncoder::new();

    let seq_sort = Sort::seq(Sort::Int);
    let _var_term = encoder.solver.declare_const("l", seq_sort.clone());
    encoder
        .var_sorts_mut_for_test()
        .insert("l".to_string(), seq_sort);

    let expr = method_call(var("l"), "len", vec![]);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "var_sorts Seq .len() must encode: {result:?}"
    );
    assert!(
        !encoder.decls().has_spec_func("fmap_len"),
        "var_sorts Seq .len() must NOT declare fmap_len"
    );
    assert!(
        !encoder.decls().has_spec_func("fset_len"),
        "var_sorts Seq .len() must NOT declare fset_len"
    );
}

// ── Cross-method consistency on same FMap receiver ──────────────────

/// A single FMap receiver calling `.len()` then `.contains(k)` then `.get(k)`
/// should use fmap_len, fmap_contains, fmap_lookup consistently. (#994)
#[test]
#[timeout(30000)]
fn test_fmap_receiver_cross_method_dispatch_consistency() {
    let mut encoder = AYEncoder::new();

    let len_expr = method_call(fmap_var("m"), "len", vec![]);
    let contains_expr = method_call(fmap_var("m"), "contains", vec![var("k")]);
    let get_expr = method_call(fmap_var("m"), "get", vec![var("k")]);

    let r1 = encoder.encode_pure(&len_expr);
    let r2 = encoder.encode_pure(&contains_expr);
    let r3 = encoder.encode_pure(&get_expr);

    assert!(r1.is_ok(), "FMap .len() must encode: {r1:?}");
    assert!(r2.is_ok(), "FMap .contains() must encode: {r2:?}");
    assert!(r3.is_ok(), "FMap .get() must encode: {r3:?}");

    assert!(
        encoder.decls().has_spec_func("fmap_len"),
        "cross-method: must have fmap_len"
    );
    assert!(
        encoder.decls().has_spec_func("fmap_contains"),
        "cross-method: must have fmap_contains"
    );
    assert!(
        encoder.decls().has_spec_func("fmap_lookup"),
        "cross-method: must have fmap_lookup"
    );
    assert!(
        !encoder.decls().has_spec_func("fset_len"),
        "cross-method: must NOT have fset_len"
    );
    assert!(
        !encoder.decls().has_spec_func("fset_contains"),
        "cross-method: must NOT have fset_contains"
    );
}
