// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ── var_sort preservation regression tests (#2165) ──

/// `rewrite_logic_method_calls_expr` must preserve `var_sort` on Forall nodes.
#[test]
fn rewrite_logic_method_calls_preserves_forall_var_sort() {
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Seq),
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
        triggers: vec![],
    };
    let logic_methods = HashSet::new();
    let result = rewrite_logic_method_calls_expr(&expr, &logic_methods);
    match result {
        PureExpr::Forall { var_sort, .. } => {
            assert_eq!(
                var_sort,
                Some(ExprSort::Seq),
                "var_sort should be preserved"
            );
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

/// `rewrite_logic_method_calls_expr` must preserve `var_sort` on Exists nodes.
#[test]
fn rewrite_logic_method_calls_preserves_exists_var_sort() {
    let expr = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
        triggers: vec![],
    };
    let logic_methods = HashSet::new();
    let result = rewrite_logic_method_calls_expr(&expr, &logic_methods);
    match result {
        PureExpr::Exists { var_sort, .. } => {
            assert_eq!(
                var_sort,
                Some(ExprSort::Int),
                "var_sort should be preserved"
            );
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

/// `rewrite_logic_method_calls_expr` must preserve `MutRef`-typed quantifier sorts.
#[test]
fn rewrite_logic_method_calls_preserves_mutref_var_sort() {
    let mut_ref_sort = ExprSort::MutRef(Box::new(ExprSort::Bool));
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(mut_ref_sort.clone()),
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
        triggers: vec![],
    };
    let logic_methods = HashSet::new();
    let result = rewrite_logic_method_calls_expr(&expr, &logic_methods);
    match result {
        PureExpr::Forall { var_sort, .. } => {
            assert_eq!(
                var_sort,
                Some(mut_ref_sort),
                "MutRef var_sort should be preserved"
            );
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

/// `simplify_newtype_field_access_expr` must preserve `var_sort` on Forall nodes.
#[test]
fn simplify_newtype_preserves_forall_var_sort() {
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
        triggers: vec![],
    };
    let params = HashSet::new();
    let result = simplify_newtype_field_access_expr(&expr, &params);
    match result {
        PureExpr::Forall { var_sort, .. } => {
            assert_eq!(
                var_sort,
                Some(ExprSort::Bool),
                "var_sort should be preserved"
            );
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

/// `simplify_newtype_field_access_expr` must preserve `var_sort` on Exists nodes.
#[test]
fn simplify_newtype_preserves_exists_var_sort() {
    let expr = PureExpr::Exists {
        var: "y".to_string(),
        var_sort: Some(ExprSort::Seq),
        body: Arc::new(PureExpr::Var("y".to_string(), None)),
        triggers: vec![],
    };
    let params = HashSet::new();
    let result = simplify_newtype_field_access_expr(&expr, &params);
    match result {
        PureExpr::Exists { var_sort, .. } => {
            assert_eq!(
                var_sort,
                Some(ExprSort::Seq),
                "var_sort should be preserved on Exists"
            );
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

/// `rewrite_named_field_access_expr` must preserve `var_sort` on Forall nodes.
#[test]
fn rewrite_named_field_access_preserves_forall_var_sort() {
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        )),
        triggers: vec![],
    };
    let field_map = HashMap::new();
    let result = rewrite_named_field_access_expr(&expr, &field_map);
    match result {
        PureExpr::Forall { var_sort, .. } => {
            assert_eq!(
                var_sort,
                Some(ExprSort::Int),
                "var_sort should be preserved through named field access rewrite"
            );
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

/// `rewrite_named_field_access_expr` must preserve `var_sort` on Exists nodes.
#[test]
fn rewrite_named_field_access_preserves_exists_var_sort() {
    let expr = PureExpr::Exists {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Seq),
        body: Arc::new(PureExpr::Var("x".to_string(), None)),
        triggers: vec![],
    };
    let field_map = HashMap::new();
    let result = rewrite_named_field_access_expr(&expr, &field_map);
    match result {
        PureExpr::Exists { var_sort, .. } => {
            assert_eq!(
                var_sort,
                Some(ExprSort::Seq),
                "var_sort should be preserved through named field access rewrite"
            );
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

/// End-to-end: var_sort survives all three rewrite passes in sequence.
///
/// Simulates the rewrite_parsed_contract_structure pipeline by running
/// a quantified expression through all three public rewrite functions.
#[test]
fn var_sort_survives_all_three_rewrite_passes() {
    // Quantified expression: forall<i: Int> { __trust_wp_field_inner(x) >= i }
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::LogicFnCall {
                name: "__trust_wp_field_inner".to_string(),
                args: vec![PureExpr::Var("x".to_string(), None)],
            }),
            BinOp::Ge,
            Arc::new(PureExpr::Var("i".to_string(), None)),
        )),
        triggers: vec![],
    };

    // Pass 1: logic method call rewriting (no-op here, no logic methods)
    let logic_methods = HashSet::new();
    let after_pass1 = rewrite_logic_method_calls_expr(&expr, &logic_methods);

    // Pass 2: newtype field access simplification (no-op here, no newtype params)
    let newtype_params = HashSet::new();
    let after_pass2 = simplify_newtype_field_access_expr(&after_pass1, &newtype_params);

    // Pass 3: named field access rewriting (rewrites __trust_wp_field_inner → __trust_wp_tuple_get_0)
    let mut field_map = HashMap::new();
    field_map.insert("inner".to_string(), 0);
    let after_pass3 = rewrite_named_field_access_expr(&after_pass2, &field_map);

    // Verify var_sort survived all three passes
    match after_pass3 {
        PureExpr::Forall {
            var,
            var_sort,
            body,
            ..
        } => {
            assert_eq!(var, "i");
            assert_eq!(
                var_sort,
                Some(ExprSort::Int),
                "var_sort must survive all three rewrite passes"
            );
            // Also verify the field rewrite happened correctly
            match *body {
                PureExpr::BinOp(ref left, BinOp::Ge, _) => match left.as_ref() {
                    PureExpr::LogicFnCall { name, .. } => {
                        assert_eq!(
                            name, "__trust_wp_tuple_get_0",
                            "named field should be rewritten to positional"
                        );
                    }
                    other => panic!("expected LogicFnCall, got {other:?}"),
                },
                ref other => panic!("expected BinOp(_, Ge, _), got {other:?}"),
            }
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}
