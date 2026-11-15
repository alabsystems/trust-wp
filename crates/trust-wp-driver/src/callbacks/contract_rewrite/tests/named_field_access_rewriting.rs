// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// --- Named field access rewriting tests ---

#[test]
fn rewrites_named_field_to_tuple_get() {
    let mut field_map = HashMap::new();
    field_map.insert("inner".to_string(), 0);

    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_field_inner".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    let result =
        rewrite_named_field_access_expr(&expr, flat_tables(&field_map)).expect("resolvable");
    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        }
    );
}

#[test]
fn rewrites_nested_field_access() {
    let mut field_map = HashMap::new();
    field_map.insert("inner".to_string(), 0);

    // result >= __trust_wp_field_inner(x)
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_field_inner".to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        }),
    );
    let result =
        rewrite_named_field_access_expr(&expr, flat_tables(&field_map)).expect("resolvable");
    assert_eq!(
        result,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::LogicFnCall {
                name: "__trust_wp_tuple_get_0".to_string(),
                args: vec![PureExpr::Var("x".to_string(), None)],
            }),
        )
    );
}

#[test]
fn preserves_unknown_field_names() {
    let mut field_map = HashMap::new();
    field_map.insert("inner".to_string(), 0);

    // __trust_wp_field_other(x) — "other" not in field_map
    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_field_other".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    let result =
        rewrite_named_field_access_expr(&expr, flat_tables(&field_map)).expect("resolvable");
    assert_eq!(result, expr, "unknown field names should be preserved");
}

#[test]
fn rewrites_multi_field_struct() {
    let mut field_map = HashMap::new();
    field_map.insert("x".to_string(), 0);
    field_map.insert("y".to_string(), 1);
    field_map.insert("z".to_string(), 2);

    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_field_y".to_string(),
        args: vec![PureExpr::Var("p".to_string(), None)],
    };
    let result =
        rewrite_named_field_access_expr(&expr, flat_tables(&field_map)).expect("resolvable");
    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_1".to_string(),
            args: vec![PureExpr::Var("p".to_string(), None)],
        }
    );
}
