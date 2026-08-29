// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// =============================================================================
// Phase 2c: infer_expr_sort FMap/Datatype return sort propagation (#994)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_infer_fmap_insert_returns_fmap() {
    let expr = PureExpr::LogicFnCall {
        name: "fmap_insert".to_string(),
        args: vec![],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        fmap_sort_for_test(),
        "fmap_insert should infer as FMap"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_fmap_merge_returns_fmap() {
    let expr = PureExpr::LogicFnCall {
        name: "fmap_merge".to_string(),
        args: vec![],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        fmap_sort_for_test(),
        "fmap_merge should infer as FMap"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_fmap_empty_returns_fmap() {
    let expr = PureExpr::LogicFnCall {
        name: "FMap::empty".to_string(),
        args: vec![],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        fmap_sort_for_test(),
        "FMap::empty should infer as FMap"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_method_insert_on_fmap_receiver_returns_fmap() {
    let receiver = PureExpr::Var("m".to_string(), Some(ExprSort::FMap));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "insert".to_string(),
        args: vec![PureExpr::Int(1), PureExpr::Int(2)],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        fmap_sort_for_test(),
        "insert on FMap receiver should infer as FMap"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_method_merge_on_fmap_receiver_returns_fmap() {
    let receiver = PureExpr::Var("m".to_string(), Some(ExprSort::FMap));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "merge".to_string(),
        args: vec![],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        fmap_sort_for_test(),
        "merge on FMap receiver should infer as FMap"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_method_on_datatype_receiver_returns_datatype() {
    use trust_wp_core::formula::intern_sort_name;

    let dt_id = intern_sort_name("my::ResourceAlgebra");
    let receiver = PureExpr::Var("r".to_string(), Some(ExprSort::Datatype(dt_id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "compose".to_string(),
        args: vec![],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Uninterpreted("ResourceAlgebra".to_string()),
        "compose on Datatype receiver should infer as bare type name (#2155)"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_method_len_on_datatype_not_propagated() {
    use trust_wp_core::formula::intern_sort_name;

    let dt_id = intern_sort_name("my::List");
    let receiver = PureExpr::Var("l".to_string(), Some(ExprSort::Datatype(dt_id)));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "len".to_string(),
        args: vec![],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "len on Datatype receiver should still be Int"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_fmap_not_bool() {
    let expr = PureExpr::LogicFnCall {
        name: "fmap_insert".to_string(),
        args: vec![],
    };
    assert!(
        is_definitely_non_bool(&expr),
        "fmap_insert should be definitely non-Bool"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_method_on_deref_fmap_receiver() {
    let inner = PureExpr::Var("m".to_string(), Some(ExprSort::FMap));
    let receiver = PureExpr::Deref(Arc::new(inner));
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "insert".to_string(),
        args: vec![PureExpr::Int(1), PureExpr::Int(2)],
    };
    assert_eq!(
        infer_expr_sort(&expr),
        fmap_sort_for_test(),
        "insert on Deref(FMap) receiver should infer as FMap"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_view_of_predcell_receiver_returns_mapping_2316() {
    use trust_wp_core::formula::intern_sort_name;

    let predcell = ExprSort::Ref(Box::new(ExprSort::Datatype(intern_sort_name(
        "trust_wp_std::std::cell::PredCell",
    ))));
    let expr = view(var_with_sort("cell", predcell));

    assert_eq!(
        infer_expr_sort(&expr),
        mapping_sort_for_test(),
        "PredCell view should infer as Mapping"
    );
}
