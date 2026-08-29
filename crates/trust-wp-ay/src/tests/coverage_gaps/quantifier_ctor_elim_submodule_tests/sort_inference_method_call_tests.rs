// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ════════════════════════════════════════════════════════════════════════
// sort_inference.rs tests — MethodCall inference
// ════════════════════════════════════════════════════════════════════════

/// Infer sort through MethodCall receiver: `receiver.method()` where
/// receiver contains the constructor call.
#[test]
#[timeout(30000)]
fn test_infer_sort_through_method_call_receiver() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = method_call(
        logic_fn_call("OptionInt::Some", vec![var("v")]),
        "unwrap",
        vec![],
    );

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        Some(Sort::Int),
        "v in MethodCall receiver should be inferred"
    );
}

/// Infer sort through MethodCall args.
#[test]
#[timeout(30000)]
fn test_infer_sort_through_method_call_args() {
    let mut encoder = AYEncoder::new();
    let dt = option_int_datatype();
    encoder.ensure_datatype_declared(&dt);

    let body = method_call(
        var("x"),
        "compare",
        vec![logic_fn_call("OptionInt::Some", vec![var("v")])],
    );

    assert_eq!(
        infer_constructor_arg_sort(&encoder, &body, "v"),
        Some(Sort::Int),
        "v in MethodCall args should be inferred"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_method_call_usage_sort_seq_receiver_len() {
    let body = method_call(var("s"), "len", vec![]);

    assert_eq!(
        infer_method_call_usage_sort(&body, "s"),
        Some(Sort::seq(Sort::Int)),
        "s.len() should infer Seq receiver sort"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_method_call_usage_sort_fmap_receiver_lookup() {
    let body = method_call(var("m"), "lookup", vec![int(0)]);

    assert_eq!(
        infer_method_call_usage_sort(&body, "m"),
        Some(Sort::Uninterpreted("FMap".to_string())),
        "m.lookup(0) should infer FMap receiver sort"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_method_call_usage_sort_index_arg_int() {
    let body = method_call(var("s"), "get", vec![var("i")]);

    assert_eq!(
        infer_method_call_usage_sort(&body, "i"),
        Some(Sort::Int),
        "seq.get(i) should infer Int for the index argument"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_method_call_usage_sort_ignores_shadowed_nested_quantifier_var() {
    let body = forall("s", gt(method_call(var("s"), "len", vec![]), int(0)));

    assert_eq!(
        infer_method_call_usage_sort(&body, "s"),
        None,
        "nested quantifier binding should shadow the outer qvar name"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_method_call_usage_sorts_batch_collects_receiver_and_arg_sorts() {
    let body = add(
        method_call(var("s"), "len", vec![]),
        method_call(var("m"), "lookup", vec![var("k")]),
    );
    let result = infer_method_call_usage_sorts_batch(&body, &["s", "m", "k"]);

    assert_eq!(
        result.get("s"),
        Some(&Sort::seq(Sort::Int)),
        "batch inference should record Seq receiver usage"
    );
    assert_eq!(
        result.get("m"),
        Some(&Sort::Uninterpreted("FMap".to_string())),
        "batch inference should record FMap receiver usage"
    );
    assert_eq!(
        result.get("k"),
        Some(&Sort::Int),
        "batch inference should record Int key/index usage"
    );
}

/// View-wrapped receivers must NOT infer a receiver sort (#579 compat).
///
/// `view(var("b")).len()` means `b@.len()`, where `b@` is the model view
/// (a Seq). The variable `b` itself is NOT a Seq — it may be an opaque
/// type whose view is Seq. The View/derived-name mechanism handles this
/// through `{var}_view` sort hints. Matching through View wrappers would
/// incorrectly upgrade `b` from Int to Seq, breaking view-variable separation.
#[test]
#[timeout(30000)]
fn test_infer_method_call_usage_sort_view_wrapped_receiver_excluded() {
    // view(var("b")).len() — b's VIEW is Seq, not b itself.
    let body = method_call(view(var("b")), "len", vec![]);

    assert_eq!(
        infer_method_call_usage_sort(&body, "b"),
        None,
        "View-wrapped receiver must not infer Seq sort for the underlying variable"
    );
}

/// Bare receiver without View should still infer Seq.
#[test]
#[timeout(30000)]
fn test_infer_method_call_usage_sort_bare_receiver_infers_seq() {
    // var("s").len() — s itself is the Seq receiver.
    let body = method_call(var("s"), "len", vec![]);

    assert_eq!(
        infer_method_call_usage_sort(&body, "s"),
        Some(Sort::seq(Sort::Int)),
        "Bare receiver should infer Seq sort"
    );
}

/// Deref-wrapped receiver should still infer Seq (Deref is identity for sort).
#[test]
#[timeout(30000)]
fn test_infer_method_call_usage_sort_deref_receiver_infers_seq() {
    // deref(var("s")).len() — *s.len(), s itself is Seq.
    let body = method_call(deref(var("s")), "len", vec![]);

    assert_eq!(
        infer_method_call_usage_sort(&body, "s"),
        Some(Sort::seq(Sort::Int)),
        "Deref-wrapped receiver should infer Seq sort"
    );
}

// ── FSet receiver sort inference (#2696) ────────────────────────────

/// `s.is_subset(other)` should infer FSet receiver sort.
#[test]
#[timeout(30000)]
fn test_infer_method_call_usage_sort_fset_receiver_is_subset() {
    let body = method_call(var("s"), "is_subset", vec![var("other")]);

    assert_eq!(
        infer_method_call_usage_sort(&body, "s"),
        Some(Sort::Uninterpreted("FSet".to_string())),
        "s.is_subset(other) should infer FSet receiver sort"
    );
}

/// `s.union(other)` should infer FSet receiver sort.
#[test]
#[timeout(30000)]
fn test_infer_method_call_usage_sort_fset_receiver_union() {
    let body = method_call(var("s"), "union", vec![var("other")]);

    assert_eq!(
        infer_method_call_usage_sort(&body, "s"),
        Some(Sort::Uninterpreted("FSet".to_string())),
        "s.union(other) should infer FSet receiver sort"
    );
}

/// `s.intersection(other)` should infer FSet for the argument too.
#[test]
#[timeout(30000)]
fn test_infer_method_call_usage_sort_fset_arg_intersection() {
    let body = method_call(var("s"), "intersection", vec![var("t")]);

    assert_eq!(
        infer_method_call_usage_sort(&body, "t"),
        Some(Sort::Uninterpreted("FSet".to_string())),
        "s.intersection(t) should infer FSet for the argument t"
    );
}

// ── Extended argument sort inference (#2696) ─────────────────────────

/// `seq.set(i, v)` should infer Int for the value argument v.
#[test]
#[timeout(30000)]
fn test_infer_method_call_usage_sort_set_value_arg_int() {
    let body = method_call(var("s"), "set", vec![int(0), var("v")]);

    assert_eq!(
        infer_method_call_usage_sort(&body, "v"),
        Some(Sort::Int),
        "seq.set(0, v) should infer Int for the value argument"
    );
}

/// `seq.push_back(x)` should infer Int for the element argument.
#[test]
#[timeout(30000)]
fn test_infer_method_call_usage_sort_push_back_arg_int() {
    let body = method_call(var("s"), "push_back", vec![var("x")]);

    assert_eq!(
        infer_method_call_usage_sort(&body, "x"),
        Some(Sort::Int),
        "seq.push_back(x) should infer Int for the element argument"
    );
}

/// `m.merge(other)` should infer FMap for the argument.
#[test]
#[timeout(30000)]
fn test_infer_method_call_usage_sort_merge_arg_fmap() {
    let body = method_call(var("m"), "merge", vec![var("other")]);

    assert_eq!(
        infer_method_call_usage_sort(&body, "other"),
        Some(Sort::Uninterpreted("FMap".to_string())),
        "m.merge(other) should infer FMap for the argument"
    );
}

// ── Batch inference with new sorts (#2696) ───────────────────────────

/// Batch inference should correctly identify FSet and FMap receiver sorts.
#[test]
#[timeout(30000)]
fn test_infer_method_call_usage_sorts_batch_fset_and_fmap() {
    let body = add(
        method_call(var("s"), "union", vec![var("t")]),
        method_call(var("m"), "merge", vec![var("n")]),
    );
    let result = infer_method_call_usage_sorts_batch(&body, &["s", "t", "m", "n"]);

    assert_eq!(
        result.get("s"),
        Some(&Sort::Uninterpreted("FSet".to_string())),
        "batch should record FSet receiver usage for s.union()"
    );
    assert_eq!(
        result.get("t"),
        Some(&Sort::Uninterpreted("FSet".to_string())),
        "batch should record FSet argument usage for union(t)"
    );
    assert_eq!(
        result.get("m"),
        Some(&Sort::Uninterpreted("FMap".to_string())),
        "batch should record FMap receiver usage for m.merge()"
    );
    assert_eq!(
        result.get("n"),
        Some(&Sort::Uninterpreted("FMap".to_string())),
        "batch should record FMap argument usage for merge(n)"
    );
}
