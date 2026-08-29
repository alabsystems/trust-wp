// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// =============================================================================
// Mapping (total function) sort inference (#2317)
// =============================================================================

/// Mapping.set on a Mapping-annotated receiver infers Mapping sort. (#2317)
#[test]
#[timeout(30000)]
fn test_infer_mapping_set_returns_mapping_sort() {
    use trust_wp_core::formula::intern_sort_name;

    let mapping_dt = ExprSort::Datatype(intern_sort_name("Mapping"));
    let receiver = PureExpr::Var("m".to_string(), Some(mapping_dt));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "set".to_string(),
        args: vec![PureExpr::Int(0), PureExpr::Int(42)],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        mapping_sort_for_test(),
        "Mapping.set should infer as Mapping sort"
    );
}

/// Mapping.get on a Mapping-annotated receiver infers Int sort. (#2317)
#[test]
#[timeout(30000)]
fn test_infer_mapping_get_returns_int() {
    use trust_wp_core::formula::intern_sort_name;

    let mapping_dt = ExprSort::Datatype(intern_sort_name("Mapping"));
    let receiver = PureExpr::Var("m".to_string(), Some(mapping_dt));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "get".to_string(),
        args: vec![PureExpr::Int(0)],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Mapping.get should infer as Int (element access)"
    );
}

/// Mapping.index on a Mapping-annotated receiver infers Int sort. (#2317)
///
/// Regression guard: `index` must be in the element-accessor exclusion list
/// (sort_inference.rs:320-332) so it reaches the Mapping element-access arm
/// instead of generic Datatype propagation. Without the fix, this returns
/// Mapping sort, mismatching `encode_mapping_method` which uses `mapping_get`
/// (Sort::Int).
#[test]
#[timeout(30000)]
fn test_infer_mapping_index_returns_int() {
    use trust_wp_core::formula::intern_sort_name;

    let mapping_dt = ExprSort::Datatype(intern_sort_name("Mapping"));
    let receiver = PureExpr::Var("m".to_string(), Some(mapping_dt));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "index".to_string(),
        args: vec![PureExpr::Int(0)],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Mapping.index should infer as Int (matching encode_mapping_method)"
    );
}

/// Mapping.index_logic on a Mapping-annotated receiver infers Int. (#2317)
#[test]
#[timeout(30000)]
fn test_infer_mapping_index_logic_returns_int() {
    use trust_wp_core::formula::intern_sort_name;

    let mapping_dt = ExprSort::Datatype(intern_sort_name("Mapping"));
    let receiver = PureExpr::Var("m".to_string(), Some(mapping_dt));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "index_logic".to_string(),
        args: vec![PureExpr::Int(0)],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Mapping.index_logic should infer as Int (element access)"
    );
}

/// Mapping.set through &Mapping reference infers Mapping sort. (#2317)
#[test]
#[timeout(30000)]
fn test_infer_mapping_set_through_ref_returns_mapping() {
    use trust_wp_core::formula::intern_sort_name;

    let mapping_ref = ExprSort::Ref(Box::new(ExprSort::Datatype(intern_sort_name("Mapping"))));
    let receiver = PureExpr::Var("m".to_string(), Some(mapping_ref));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "set".to_string(),
        args: vec![PureExpr::Int(0), PureExpr::Int(42)],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        mapping_sort_for_test(),
        "Mapping.set through Ref should infer as Mapping"
    );
}

/// Mapping.get through deref'd reference infers Int. (#2317)
#[test]
#[timeout(30000)]
fn test_infer_mapping_get_through_deref_returns_int() {
    use trust_wp_core::formula::intern_sort_name;

    let mapping_ref = ExprSort::Ref(Box::new(ExprSort::Datatype(intern_sort_name("Mapping"))));
    let receiver = PureExpr::Deref(Arc::new(PureExpr::Var("m".to_string(), Some(mapping_ref))));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "get".to_string(),
        args: vec![PureExpr::Int(0)],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Mapping.get through Deref should infer as Int"
    );
}

/// Non-Mapping receiver calling .set should NOT infer as Mapping. (#2317)
#[test]
#[timeout(30000)]
fn test_infer_non_mapping_set_does_not_return_mapping() {
    let receiver = PureExpr::Var("v".to_string(), None);
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "set".to_string(),
        args: vec![PureExpr::Int(0), PureExpr::Int(42)],
    };
    assert_ne!(
        infer_expr_sort(&expr),
        mapping_sort_for_test(),
        "non-Mapping receiver .set should not infer as Mapping"
    );
}

/// Mapping.set/get ground frames preserve reads at distinct keys.
#[test]
#[timeout(30000)]
fn test_mapping_ground_frame_for_distinct_set_get_keys() {
    let mut encoder = AYEncoder::new();
    let mapping = Sort::Uninterpreted("Mapping".to_string());

    let get_decl =
        encoder.get_or_declare_spec_fn("mapping_get", &[mapping.clone(), Sort::Int], Sort::Int);
    let set_decl = encoder.get_or_declare_spec_fn(
        "mapping_set",
        &[mapping.clone(), Sort::Int, Sort::Int],
        mapping.clone(),
    );

    let m = encoder.solver.fresh_var("m", mapping);
    let k1 = encoder.solver.fresh_var("k1", Sort::Int);
    let k2 = encoder.solver.fresh_var("k2", Sort::Int);
    let v = encoder.solver.fresh_var("v", Sort::Int);

    let set_app = encoder.solver.apply(&set_decl, &[m, k1, v]);
    let get_set_k2 = encoder.solver.apply(&get_decl, &[set_app, k2]);
    encoder.register_standard_ground_application("mapping_set", set_app, vec![m, k1, v]);
    encoder.register_standard_ground_application("mapping_get", get_set_k2, vec![set_app, k2]);

    let asserted = encoder.assert_standard_ground_instances();
    assert!(
        asserted >= 2,
        "same-key and different-key Mapping set/get instances should be asserted, got {asserted}"
    );

    let keys_equal = encoder.solver.eq(k1, k2);
    let keys_differ = encoder.solver.not(keys_equal);
    encoder.solver.assert_term(keys_differ);

    let get_m_k2 = encoder.solver.apply(&get_decl, &[m, k2]);
    let frame_eq = encoder.solver.eq(get_set_k2, get_m_k2);
    let frame_neq = encoder.solver.not(frame_eq);
    encoder.solver.assert_term(frame_neq);

    let result = encoder.check_sat();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "Mapping frame should prove get(set(m,k1,v),k2) = get(m,k2) when k1 != k2, got {result:?}"
    );
}
