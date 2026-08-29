// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// =============================================================================
// Coverage for #1965 Steps 2-4: sort inference on type invariant logic
// functions, annotated Seq hint collection, and formula sort hints.
// =============================================================================

/// Step 3 (#1965): LogicFnCall with `_inv` suffix must infer as Bool.
/// The `infer_expr_sort` function has a match arm for LogicFnCall names ending
/// in `_inv`, but existing tests only cover the MethodCall `invariant` path.
#[test]
#[timeout(30000)]
fn infer_expr_sort_logic_fn_call_inv_suffix_returns_bool() {
    let expr = logic_fn_call("MyStruct_inv", vec![var("self")]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "LogicFnCall with _inv suffix must return Bool, not Int"
    );
}

/// Step 3 (#1965): LogicFnCall matching `is_invariant_method_name` returns Bool.
/// Tests the __trust_wp_invariant_ prefix path through LogicFnCall (not MethodCall).
#[test]
#[timeout(30000)]
fn infer_expr_sort_logic_fn_call_trust_wp_invariant_prefix_returns_bool() {
    let name = trust_wp_core::logic::type_invariant_method_name("Vec_i32_");
    let expr = logic_fn_call(&name, vec![var("self")]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "LogicFnCall with __trust_wp_invariant_ prefix must return Bool"
    );
}

/// Step 3 (#1965) negative: LogicFnCall NOT matching _inv or invariant patterns
/// should still return Int (the default).
#[test]
#[timeout(30000)]
fn infer_expr_sort_logic_fn_call_non_invariant_stays_int() {
    let expr = logic_fn_call("compute_value", vec![var("x")]);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Non-invariant LogicFnCall should return Int"
    );
}

/// Step 4 (#1965): Ambiguous method on Seq-annotated Var receiver should collect
/// Seq hint via the `annotated_seq` guard in `collect_all_sort_hints`.
#[test]
#[timeout(30000)]
fn collect_sort_hints_annotated_seq_var_with_ambiguous_method() {
    use crate::encoder::sort_context::{collect_all_sort_hints, SortHintAccumulator};

    // s@Seq.len() — "len" is ambiguous, but the Seq annotation on s should force
    // the hint collector to tag s_view as Seq.
    let seq_var = var_with_sort("s", ExprSort::Seq);
    let len_call = method_call(view(seq_var), "len", vec![]);

    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&len_call, &mut acc);

    assert!(
        acc.seqs.contains("s_view"),
        "Seq-annotated Var receiver with ambiguous method 'len' must be tagged as Seq; seqs={:?}",
        acc.seqs,
    );
}

/// Ref(Seq)-annotated receivers should drive the ambiguous-method prescan the
/// same way as direct Seq annotations. This matches MIR typing for `&Seq<T>`.
#[test]
#[timeout(30000)]
fn collect_sort_hints_ref_seq_var_with_ambiguous_method() {
    use crate::encoder::sort_context::{collect_all_sort_hints, SortHintAccumulator};

    let seq_ref = var_with_sort("s", ExprSort::Ref(Box::new(ExprSort::Seq)));
    let len_call = method_call(seq_ref, "len", vec![]);

    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&len_call, &mut acc);

    assert!(
        acc.seqs.contains("s_view"),
        "Ref(Seq)-annotated receiver with ambiguous 'len' must be tagged as Seq; seqs={:?}",
        acc.seqs,
    );
}

/// Ref(FMap)-annotated final-view receivers must stay out of the Seq hint set
/// even though `View(Final(...)).len()` takes the non-Var ambiguous path.
#[test]
#[timeout(30000)]
fn collect_sort_hints_ref_fmap_final_view_len_prefers_fmap() {
    use crate::encoder::sort_context::{collect_all_sort_hints, SortHintAccumulator};

    let fmap_ref = var_with_sort("m", ExprSort::Ref(Box::new(ExprSort::FMap)));
    let len_call = method_call(view(final_expr(fmap_ref)), "len", vec![]);

    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&len_call, &mut acc);

    assert!(
        acc.fmaps.contains("final_m_view"),
        "Ref(FMap) final-view receiver must be tagged as FMap for ambiguous 'len'; fmaps={:?}",
        acc.fmaps,
    );
    assert!(
        !acc.seqs.contains("final_m_view"),
        "Ref(FMap) final-view receiver must not be mis-tagged as Seq; seqs={:?}",
        acc.seqs,
    );
}

/// Step 4 (#1965): Bare Var receiver (no annotation) with ambiguous method should
/// NOT be tagged as Seq — only non-Var receivers or annotated Vars get tagged.
#[test]
#[timeout(30000)]
fn collect_sort_hints_bare_var_with_ambiguous_method_no_seq() {
    use crate::encoder::sort_context::{collect_all_sort_hints, SortHintAccumulator};

    // s.len() — "len" is ambiguous, s is a bare Var with no annotation.
    // The is_ambiguous_seq guard requires !matches!(receiver, Var(_, _)).
    let len_call = method_call(var("s"), "len", vec![]);

    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&len_call, &mut acc);

    assert!(
        !acc.seqs.contains("s"),
        "Bare Var receiver with ambiguous method 'len' must NOT be tagged Seq; seqs={:?}",
        acc.seqs,
    );
}

/// Step 4 (#1965): Direct Seq-annotated Var with ambiguous method (no view wrapper)
/// triggers annotated_seq guard. normalize_seq_receiver_for_scan wraps bare Var in
/// View(...), so the resolved name is "s_view" (not "s"). This is the canonical
/// name form for Seq variables — the _view suffix is how the sort context tracks them.
#[test]
#[timeout(30000)]
fn collect_sort_hints_annotated_seq_direct_var_get() {
    use crate::encoder::sort_context::{collect_all_sort_hints, SortHintAccumulator};

    // s@Seq.get(0) — direct Var with Seq annotation, "get" is ambiguous method.
    // normalize_seq_receiver_for_scan wraps non-View receivers as View(Var("s")),
    // so resolve_view_var_name extracts "s_view".
    let seq_var = var_with_sort("s", ExprSort::Seq);
    let get_call = method_call(seq_var, "get", vec![int(0)]);

    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&get_call, &mut acc);

    assert!(
        acc.seqs.contains("s_view"),
        "Direct Seq-annotated Var with ambiguous method 'get' must be tagged as Seq \
         (normalized to s_view); seqs={:?}",
        acc.seqs,
    );
}

/// Receiver classification should honor authoritative FMap annotations even if
/// a stale Seq hint exists on the final-view name. This prevents `len` from
/// dispatching into `seq_len` on FMap terms. (#2209)
#[test]
#[timeout(30000)]
fn is_seq_receiver_ignores_conflicting_seq_hint_for_annotated_fmap() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("final_m_view".to_string(), ExprSort::Seq);

    let receiver = view(final_expr(var_with_sort(
        "m",
        ExprSort::Ref(Box::new(ExprSort::FMap)),
    )));

    assert!(
        !encoder.is_seq_receiver(&receiver, None),
        "Ref(FMap) annotation must override conflicting Seq hint"
    );
    assert!(
        encoder.is_fmap_receiver(&receiver, None),
        "Ref(FMap) annotation must still route ambiguous 'len' to FMap"
    );
}

/// Direct encoding of `(^m).len()` on a `Ref(FMap)` receiver should not reach
/// the Seq encoder, even if the final-view name has conflicting Seq evidence.
#[test]
#[timeout(30000)]
fn encode_len_on_ref_fmap_final_receiver_succeeds() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new();
    encoder.record_sort_hint("final_m_view".to_string(), ExprSort::Seq);

    let expr = method_call(
        view(final_expr(var_with_sort(
            "m",
            ExprSort::Ref(Box::new(ExprSort::FMap)),
        ))),
        "len",
        vec![],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Ref(FMap) final-view len() should not panic through seq_len: {result:?}"
    );
}

/// Direct encoding of `len` on a `Ref(Seq)` receiver should succeed without
/// relying on the non-Var ambiguous receiver heuristic. (#2209)
#[test]
#[timeout(30000)]
fn encode_len_on_ref_seq_receiver_succeeds() {
    let mut encoder = AYEncoder::new();
    let expr = method_call(
        var_with_sort("s", ExprSort::Ref(Box::new(ExprSort::Seq))),
        "len",
        vec![],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Ref(Seq) receiver should encode len() without sort mismatch: {result:?}"
    );
}
