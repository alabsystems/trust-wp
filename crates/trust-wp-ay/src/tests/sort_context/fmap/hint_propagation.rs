// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// =============================================================================
// FMap name propagation chain and ambiguous promotion (#994)
// =============================================================================

/// Test that register_sort_hints propagates FMap hints through the
/// `final_{x}_view` → `{x}_view` naming chain, matching the existing
/// Seq propagation behavior. (#994)
#[test]
#[timeout(30000)]
fn test_register_sort_hints_fmap_name_chain_final_to_view() {
    let mut encoder = AYEncoder::new();

    // Build an expression where `final_m_view` is used with an FMap-only
    // method (lookup). resolve_view_var_name resolves View(Final(Var("m")))
    // to "final_m_view". The prescan should tag it as FMap, then the name
    // propagation chain should propagate to `m_view` and `m`.
    let exprs = vec![PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Final(Arc::new(
            PureExpr::Var("m".to_string(), None),
        ))))),
        method: "lookup".to_string(),
        args: vec![PureExpr::Int(0)],
    }];

    encoder.register_sort_hints(&exprs);

    // `final_m_view` should be FMap (from hint collection)
    assert_eq!(
        encoder
            .sort_resolver_for_test()
            .get_sort_hint("final_m_view"),
        Some(&ExprSort::FMap),
        "final_m_view should have FMap hint from lookup method"
    );

    // `m_view` should be FMap (from name propagation chain)
    assert_eq!(
        encoder.sort_resolver_for_test().get_sort_hint("m_view"),
        Some(&ExprSort::FMap),
        "m_view should receive FMap hint via final_ prefix propagation"
    );

    // `m` should be FMap (from _view suffix propagation)
    assert_eq!(
        encoder.sort_resolver_for_test().get_sort_hint("m"),
        Some(&ExprSort::FMap),
        "m should receive FMap hint via _view suffix propagation"
    );
}

#[test]
#[timeout(30000)]
fn test_ext_eq_on_fmap_views_does_not_promote_seq_hints() {
    let expr = method_call(
        view(var_with_sort("r", ExprSort::FMap)),
        "ext_eq",
        vec![view(var_with_sort("xs_snap", ExprSort::FMap))],
    );

    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&expr, &mut acc);
    assert!(
        !acc.seqs.contains("r_view"),
        "FMap ext_eq receiver should not be pre-tagged Seq"
    );
    assert!(
        !acc.seqs.contains("xs_snap_view"),
        "FMap ext_eq arg should not be pre-tagged Seq"
    );

    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder.register_sort_hints(std::slice::from_ref(&expr));

    assert_ne!(
        encoder.sort_resolver_for_test().get_sort_hint("r_view"),
        Some(&ExprSort::Seq),
        "FMap ext_eq receiver hint must not become Seq"
    );
    assert_ne!(
        encoder
            .sort_resolver_for_test()
            .get_sort_hint("xs_snap_view"),
        Some(&ExprSort::Seq),
        "FMap ext_eq arg hint must not become Seq"
    );

    let term = encoder
        .encode_pure(&expr)
        .expect("FMap ext_eq should fall back to a Bool UF, not Seq ext_eq");
    assert_eq!(
        encoder.solver.get_sort(term),
        Sort::Bool,
        "ext_eq over FMap views must remain Bool-sorted"
    );
    assert!(
        encoder
            .decls()
            .has_logic_func("method_ext_eq_2_u464d6170_u464d6170"),
        "FMap ext_eq should use the generic Bool UF fallback"
    );
}

#[test]
#[timeout(30000)]
fn test_ext_eq_on_declared_fmap_views_ignores_conflicting_seq_hints() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let fmap = Sort::Uninterpreted("FMap".to_string());
    encoder
        .get_or_declare_var("r", fmap.clone())
        .expect("declare r as FMap");
    encoder
        .get_or_declare_var("xs_snap", fmap)
        .expect("declare xs_snap as FMap");
    encoder.record_sort_hint("r_view".to_string(), ExprSort::Seq);
    encoder.record_sort_hint("xs_snap_view".to_string(), ExprSort::Seq);

    let receiver = view(var("r"));
    let other = view(var("xs_snap"));
    assert!(
        !encoder.is_seq_receiver(&receiver, None),
        "declared FMap receiver must beat conflicting Seq hint"
    );
    assert!(
        !encoder.is_seq_receiver(&other, None),
        "declared FMap argument must beat conflicting Seq hint"
    );
    assert!(
        encoder.is_fmap_receiver(&receiver, None),
        "declared FMap receiver should still classify as FMap"
    );

    let expr = method_call(receiver, "ext_eq", vec![other]);
    let term = encoder
        .encode_pure(&expr)
        .expect("FMap ext_eq should remain on the Bool UF path");
    assert_eq!(
        encoder.solver.get_sort(term),
        Sort::Bool,
        "declared FMap ext_eq should stay Bool-sorted"
    );
    assert!(
        encoder
            .decls()
            .has_logic_func("method_ext_eq_2_u464d6170_u464d6170"),
        "declared FMap ext_eq should use the FMap Bool UF signature"
    );
}

#[test]
#[timeout(30000)]
fn test_predcell_alias_equality_propagates_mapping_hint_2316() {
    use trust_wp_core::formula::intern_sort_name;

    let predcell = ExprSort::Ref(Box::new(ExprSort::Datatype(intern_sort_name(
        "trust_wp_std::std::cell::PredCell",
    ))));
    let alias_equality = eq(view(var("call_2")), view(var_with_sort("pred", predcell)));
    let receiver = view(var("call_2"));
    let lookup = method_call(receiver.clone(), "index_logic", vec![int(7)]);

    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&alias_equality, &mut acc);
    assert!(
        acc.mappings.contains("call_2_view"),
        "Mapping equality should pre-tag lowered alias views"
    );
    assert!(
        !acc.seqs.contains("call_2_view"),
        "Mapping equality must not route lowered alias views onto Seq"
    );

    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("call_2", Sort::Uninterpreted("PredCellTemp".to_string()))
        .expect("declare lowered alias temp with a non-Mapping base sort");

    let exprs = vec![alias_equality, lookup.clone()];
    encoder.register_sort_hints(&exprs);

    let mapping = mapping_expr_sort();
    assert_eq!(
        encoder
            .sort_resolver_for_test()
            .get_sort_hint("call_2_view"),
        Some(&mapping),
        "lowered alias equality should register a direct Mapping hint"
    );
    assert!(
        encoder.is_mapping_receiver(&receiver, None),
        "lowered alias view should dispatch as Mapping after equality propagation"
    );
    assert!(
        !encoder.is_seq_receiver(&receiver, None),
        "lowered alias view must stay off the Seq receiver path"
    );

    let result = encoder.encode_pure(&lookup);
    assert!(
        result.is_ok(),
        "lowered alias Mapping lookup should encode cleanly: {result:?}"
    );
    assert_eq!(
        encoder.var_sort("call_2_view"),
        Some(&mapping_sort_for_test()),
        "direct Mapping hint should beat the base temp sort for call_2_view"
    );
    assert!(
        encoder.decls().has_spec_func("mapping_get"),
        "lowered alias lookup should declare mapping_get"
    );
    assert!(
        encoder.seq_state_for_test().funcs_is_none(),
        "lowered alias Mapping lookup should not initialize Seq functions"
    );
}

/// Test that the full PredCellAsSliceOfCells quantified formula shape encodes
/// correctly: `forall i. (0 <= i < pred.len()) => View(result.index_logic(i)) == pred.index_logic(i)`
/// where result is PredCellSlice-annotated and pred is Seq-annotated.
///
/// This covers the lowered alias path: pred.index_logic(i) goes through Seq
/// encoding (producing an Int-sorted term), while View(result.index_logic(i))
/// goes through Mapping encoding (producing a Mapping-sorted term). The
/// equality sort restoration mechanism (try_restore_seq_element_from_int)
/// must bridge the Int back to Mapping inside the quantifier body. (#2316)
#[test]
#[timeout(30000)]
fn test_predcell_as_slice_of_cells_quantified_equality_encodes_2316() {
    use trust_wp_core::formula::intern_sort_name;

    let predcell_slice_sort =
        ExprSort::Datatype(intern_sort_name("trust_wp_internal::PredCellSlice"));
    let seq_sort = ExprSort::Seq;

    // result has PredCellSlice annotation (like the MIR-extracted result of as_slice_of_cells)
    let result = var_with_sort("result", predcell_slice_sort);
    // pred has Seq annotation (like the Snapshot<Seq<Mapping<...>>> argument)
    let pred = var_with_sort("pred", seq_sort);

    let i_var = var("i");
    let result_elem_view = view(method_call(
        result.clone(),
        "index_logic",
        vec![i_var.clone()],
    ));
    let pred_elem = method_call(pred.clone(), "index_logic", vec![i_var.clone()]);

    // Build the quantified equality: forall i. (0 <= i < pred.len()) => result[i]@ == pred[i]
    let pred_len = method_call(pred.clone(), "len", vec![]);
    let in_bounds = and(
        le(int(0), i_var.clone()),
        lt(i_var.clone(), pred_len.clone()),
    );
    let elem_bridge = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(implies(
            in_bounds.clone(),
            eq(result_elem_view.clone(), pred_elem.clone()),
        )),
        triggers: vec![vec![result_elem_view.clone()]],
    };

    // Register sort hints and encode
    let mut encoder = AYEncoder::new_with_quantifiers();
    let all_exprs = vec![
        eq(method_call(view(result.clone()), "len", vec![]), pred_len),
        elem_bridge.clone(),
    ];
    encoder.register_sort_hints(&all_exprs);

    // The quantified formula should encode without error
    let result_term = encoder.encode_pure(&elem_bridge);
    assert!(
        result_term.is_ok(),
        "PredCellAsSliceOfCells quantified elem_bridge should encode: {result_term:?}"
    );

    // Verify the dedicated PredCellSlice elem view UF was declared.
    // The View(PredCellSlice.index_logic(i)) path uses __predcell_slice_elem_view_*
    // rather than generic mapping_get. Check that any such UF exists.
    let has_predcell_slice_view_uf = encoder
        .decls()
        .spec_func_names()
        .any(|name| name.starts_with("__predcell_slice_elem_view"));
    assert!(
        has_predcell_slice_view_uf,
        "PredCellSlice element view should declare __predcell_slice_elem_view UF"
    );
}

/// Test the nested double-quantifier lookup bridge from PredCellAsSliceOfCells:
/// `forall i. forall x. (0 <= i < pred.len()) => result[i]@.index_logic(x) == pred[i].index_logic(x)`
///
/// This exercises the deep Mapping lookup path: pred.index_logic(i).index_logic(x)
/// where the inner index goes through Seq path and the outer should dispatch to
/// Mapping via is_seq_index_mapping_candidate. (#2316)
#[test]
#[timeout(30000)]
fn test_predcell_as_slice_of_cells_nested_lookup_bridge_encodes_2316() {
    use trust_wp_core::formula::intern_sort_name;

    let predcell_slice_sort =
        ExprSort::Datatype(intern_sort_name("trust_wp_internal::PredCellSlice"));
    let seq_sort = ExprSort::Seq;

    let result = var_with_sort("result", predcell_slice_sort);
    let pred = var_with_sort("pred", seq_sort);

    let i_var = var("i");
    let x_var = var("x");
    let result_elem_view = view(method_call(
        result.clone(),
        "index_logic",
        vec![i_var.clone()],
    ));
    let pred_elem = method_call(pred.clone(), "index_logic", vec![i_var.clone()]);

    // Deep lookups: result[i]@.index_logic(x) and pred[i].index_logic(x)
    let result_elem_lookup =
        method_call(result_elem_view.clone(), "index_logic", vec![x_var.clone()]);
    let pred_elem_lookup = method_call(pred_elem.clone(), "index_logic", vec![x_var.clone()]);

    let pred_len = method_call(pred.clone(), "len", vec![]);
    let in_bounds = and(
        le(int(0), i_var.clone()),
        lt(i_var.clone(), pred_len.clone()),
    );

    // Nested quantifier: forall i. forall x. in_bounds => result[i]@[x] == pred[i][x]
    let elem_lookup_bridge = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(implies(
                in_bounds.clone(),
                eq(result_elem_lookup.clone(), pred_elem_lookup.clone()),
            )),
            triggers: vec![vec![result_elem_lookup.clone()]],
        }),
        triggers: vec![vec![result_elem_view.clone()]],
    };

    let mut encoder = AYEncoder::new_with_quantifiers();
    let all_exprs = vec![
        eq(method_call(view(result.clone()), "len", vec![]), pred_len),
        elem_lookup_bridge.clone(),
    ];
    encoder.register_sort_hints(&all_exprs);

    // The nested quantified formula should encode without error
    let result_term = encoder.encode_pure(&elem_lookup_bridge);
    assert!(
        result_term.is_ok(),
        "PredCellAsSliceOfCells nested lookup bridge should encode: {result_term:?}"
    );
}
