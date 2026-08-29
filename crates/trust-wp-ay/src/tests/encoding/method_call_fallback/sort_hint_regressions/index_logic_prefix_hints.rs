// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #1805: index_logic on a Mapping receiver
/// with a Seq-sorted quantifier-bound argument should route to
/// fmap encoding, not seq encoding, even if prescan mis-tags
/// the receiver as Seq. (#1805 cell/03_as_slice_of_cells)
#[test]
#[timeout(30000)]
fn test_index_logic_seq_arg_routes_to_fmap_1805() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Simulate: forall<s: Seq> view(cell).index_logic(deref(s)) == 0
    // The View(Var("cell")) receiver may be mis-tagged as Seq by prescan,
    // but "s" is a Seq-sorted bound variable used as the key.
    // This should route to fmap encoding, not seq indexing.
    // Wrap in equality to produce a Bool body for the quantifier.
    let lookup = method_call(view(var("cell")), "index_logic", vec![deref(var("s"))]);
    let body = eq(lookup, int(0));
    let expr = forall_with_sort("s", ExprSort::Seq, body);

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "index_logic with Seq-sorted arg should not panic: {result:?}"
    );
}

/// Regression for #1805: in `old(...)` prefix contexts, index_logic
/// key detection must check prefixed base hints (e.g., `old_s`), not
/// only bare base names (`s`). Otherwise stale non-Seq metadata on
/// `old_s_current` can misroute to Seq indexing.
#[test]
#[timeout(30000)]
fn test_index_logic_old_prefix_prefers_prefixed_seq_key_hint_1805() {
    use ay_dpll::api::Sort;
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new();
    // Force receiver dispatch down the Seq-receiver branch so key-sort
    // classification decides between Seq indexing and non-Seq fallback.
    encoder.record_sort_hint("old_cell_view".to_string(), ExprSort::Seq);
    // Simulate stale non-Seq metadata on the derived key name.
    encoder
        .var_sorts_mut_for_test()
        .insert("old_s_current".to_string(), Sort::Bool);
    // The authoritative key hint exists only on the prefixed base name.
    encoder.record_sort_hint("old_s".to_string(), ExprSort::Seq);

    let lookup = old(method_call(
        view(var("cell")),
        "index_logic",
        vec![deref(var("s"))],
    ));
    let expr = eq(lookup, int(0));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "old(index_logic(*s)) with prefixed Seq key hint should encode: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "old(index_logic(*s)) should not trigger a solver panic: {:?}",
        encoder.solver_panic_reason()
    );
    let routed_non_seq = encoder
        .decls()
        .logic_func_names()
        .any(|name| name.starts_with("method_index_logic_2_"))
        || encoder.decls().has_spec_func("fmap_lookup");
    assert!(
        routed_non_seq,
        "old(index_logic(*s)) with Seq key should avoid Seq indexing (logic_fns={:?}, spec_fns={:?})",
        encoder.decls().logic_func_names().collect::<Vec<_>>(),
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );
}

/// Regression for #1805: when `old_`-prefixed key hints are absent, key
/// classification must still consult unprefixed base hints.
///
/// Without this fallback, `old(index_logic(*s))` can misclassify the key
/// as non-Seq in stale-metadata paths and route to Seq indexing.
#[test]
#[timeout(30000)]
fn test_index_logic_old_prefix_falls_back_to_unprefixed_seq_key_hint_1805() {
    use ay_dpll::api::Sort;
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new();
    // Force receiver dispatch down the Seq-receiver branch.
    encoder.record_sort_hint("old_cell_view".to_string(), ExprSort::Seq);
    // Simulate stale non-Seq metadata on derived key name.
    encoder
        .var_sorts_mut_for_test()
        .insert("old_s_current".to_string(), Sort::Bool);
    // Only the unprefixed base key is available.
    encoder.record_sort_hint("s".to_string(), ExprSort::Seq);

    let lookup = old(method_call(
        view(var("cell")),
        "index_logic",
        vec![deref(var("s"))],
    ));
    let expr = eq(lookup, int(0));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "old(index_logic(*s)) should encode with unprefixed Seq key hint: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "old(index_logic(*s)) should not trigger a solver panic: {:?}",
        encoder.solver_panic_reason()
    );
    let routed_non_seq = encoder
        .decls()
        .logic_func_names()
        .any(|name| name.starts_with("method_index_logic_2_"))
        || encoder.decls().has_spec_func("fmap_lookup");
    assert!(
        routed_non_seq,
        "old(index_logic(*s)) with fallback Seq key hint should avoid Seq indexing (logic_fns={:?}, spec_fns={:?})",
        encoder.decls().logic_func_names().collect::<Vec<_>>(),
        encoder.decls().spec_func_names().collect::<Vec<_>>()
    );
}
