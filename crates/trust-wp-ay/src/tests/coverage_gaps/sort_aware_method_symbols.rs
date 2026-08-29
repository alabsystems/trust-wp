// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, ExprSort};

use super::*;

#[test]
#[timeout(30000)]
fn completed_on_iter_and_iter_mut_receivers_use_distinct_symbols() {
    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("iter", Sort::Uninterpreted("Iter".to_string()))
        .expect("declare Iter receiver");
    encoder
        .get_or_declare_var("iter_mut", Sort::Uninterpreted("IterMut".to_string()))
        .expect("declare IterMut receiver");

    let completed_iter = method_call(var("iter"), "completed", vec![]);
    let completed_iter_mut = method_call(var("iter_mut"), "completed", vec![]);

    assert!(
        encoder.encode_pure(&completed_iter).is_ok(),
        "completed() on Iter receiver should encode"
    );
    assert!(
        encoder.encode_pure(&completed_iter_mut).is_ok(),
        "completed() on IterMut receiver should encode"
    );

    assert!(
        encoder
            .decls()
            .has_logic_func("method_completed_1_u49746572"),
        "Iter receiver should get its own completed() symbol"
    );
    assert!(
        encoder
            .decls()
            .has_logic_func("method_completed_1_u497465724d7574"),
        "IterMut receiver should get its own completed() symbol"
    );
}

#[test]
#[timeout(30000)]
fn produces_on_iter_and_iter_mut_receivers_use_distinct_symbols() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .get_or_declare_var("iter", Sort::Uninterpreted("Iter".to_string()))
        .expect("declare Iter receiver");
    encoder
        .get_or_declare_var("next_iter", Sort::Uninterpreted("Iter".to_string()))
        .expect("declare Iter successor");
    encoder
        .get_or_declare_var("iter_mut", Sort::Uninterpreted("IterMut".to_string()))
        .expect("declare IterMut receiver");
    encoder
        .get_or_declare_var("next_iter_mut", Sort::Uninterpreted("IterMut".to_string()))
        .expect("declare IterMut successor");

    let seq_empty = logic_fn_call("seq_empty", vec![]);
    let produces_iter = method_call(
        var("iter"),
        "produces",
        vec![seq_empty.clone(), var("next_iter")],
    );
    let produces_iter_mut = method_call(
        var("iter_mut"),
        "produces",
        vec![seq_empty, var("next_iter_mut")],
    );

    assert!(
        encoder.encode_pure(&produces_iter).is_ok(),
        "produces() on Iter receiver should encode"
    );
    assert!(
        encoder.encode_pure(&produces_iter_mut).is_ok(),
        "produces() on IterMut receiver should encode"
    );

    assert!(
        encoder
            .decls()
            .has_logic_func("method_produces_3_u49746572_s_u49746572"),
        "Iter receiver should get its own produces() symbol"
    );
    assert!(
        encoder
            .decls()
            .has_logic_func("method_produces_3_u497465724d7574_s_u497465724d7574"),
        "IterMut receiver should get its own produces() symbol"
    );
}

#[test]
#[timeout(30000)]
fn predcell_slice_elem_view_uses_signature_disambiguation_2316() {
    let mut encoder = AYEncoder::new();
    let mapping = Sort::Uninterpreted("Mapping".to_string());
    let seq = Sort::seq(Sort::Int);
    encoder.get_or_declare_spec_fn(
        "__predcell_slice_elem_view",
        &[seq.clone(), Sort::Int],
        mapping.clone(),
    );

    let predcell_slice = ExprSort::Ref(Box::new(ExprSort::Datatype(intern_sort_name(
        "trust_wp_internal::PredCellSlice",
    ))));
    let expr = view(method_call(
        var_with_sort("cells", predcell_slice),
        "index_logic",
        vec![int(0)],
    ));

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "PredCellSlice element views should survive pre-existing spec UF signatures: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "PredCellSlice element view helper should not record a solver panic: {:?}",
        encoder.solver_panic_reason()
    );

    let helper_names = encoder
        .decls()
        .spec_func_names()
        .filter(|name| name.starts_with("__predcell_slice_elem_view"))
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(
        helper_names.len(),
        2,
        "collision-safe registration should keep both helper signatures distinct: {helper_names:?}"
    );
    assert!(
        helper_names
            .iter()
            .any(|name| name == "__predcell_slice_elem_view"),
        "legacy helper symbol should remain available for the original signature"
    );
    assert!(
        helper_names
            .iter()
            .any(|name| name != "__predcell_slice_elem_view"),
        "PredCellSlice helper should get a sort-aware collision symbol: {helper_names:?}"
    );
}
