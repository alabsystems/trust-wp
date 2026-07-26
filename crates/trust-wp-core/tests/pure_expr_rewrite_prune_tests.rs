// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, PureExpr};

fn call_expr() -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::Var("a".to_string(), None)),
        method: "f".to_string(),
        args: vec![],
    }
}

#[test]
fn rewrite_bottom_up_prune_rewrites_nested_nodes_when_descending() {
    let call = call_expr();
    let expr = PureExpr::BinOp(
        Arc::new(call.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    );

    let rewritten = expr.rewrite_bottom_up_prune(
        |_| true,
        |node| match node {
            PureExpr::MethodCall { .. } => PureExpr::Int(1),
            other => other,
        },
    );

    assert_eq!(
        rewritten,
        PureExpr::BinOp(
            Arc::new(PureExpr::Int(1)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0))
        )
    );
}

#[test]
fn rewrite_bottom_up_prune_skips_quantifier_children() {
    let call = call_expr();
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(call.clone()),
        triggers: vec![vec![call.clone()]],
    };

    let rewritten = expr.rewrite_bottom_up_prune(
        |node| !matches!(node, PureExpr::Forall { .. } | PureExpr::Exists { .. }),
        |node| match node {
            PureExpr::MethodCall { .. } => PureExpr::Int(1),
            other => other,
        },
    );

    assert_eq!(rewritten, expr);
}

#[test]
fn rewrite_bottom_up_prune_still_rewrites_pruned_root() {
    let expr = call_expr();

    let rewritten = expr.rewrite_bottom_up_prune(
        |_| false,
        |node| match node {
            PureExpr::MethodCall { .. } => PureExpr::Int(7),
            other => other,
        },
    );

    assert_eq!(rewritten, PureExpr::Int(7));
}

#[test]
fn rewrite_bottom_up_prune_with_depth_limit_still_rewrites_pruned_root() {
    let expr = call_expr();

    let rewritten = expr.rewrite_bottom_up_prune_with_depth_limit(
        0,
        |_| false,
        |node| match node {
            PureExpr::MethodCall { .. } => PureExpr::Int(7),
            other => other,
        },
    );

    assert_eq!(rewritten, PureExpr::Int(7));
}

#[test]
fn rewrite_bottom_up_prune_with_depth_limit_preserves_too_deep_children() {
    let call = call_expr();
    let expr = PureExpr::BinOp(
        Arc::new(call.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    );

    let rewritten = expr.rewrite_bottom_up_prune_with_depth_limit(
        0,
        |_| true,
        |node| match node {
            PureExpr::MethodCall { .. } => PureExpr::Int(1),
            other => other,
        },
    );

    assert_eq!(rewritten, expr);
}

#[test]
fn rewrite_bottom_up_prune_with_depth_limit_if_changed_returns_none_for_noop() {
    let expr = PureExpr::BinOp(Arc::new(call_expr()), BinOp::Eq, Arc::new(PureExpr::Int(0)));

    let rewritten = expr.rewrite_bottom_up_prune_with_depth_limit_if_changed(8, |_| true, |_| None);

    assert_eq!(rewritten, None);
}

#[test]
fn rewrite_bottom_up_prune_with_depth_limit_if_changed_rewrites_nested_nodes() {
    let expr = PureExpr::BinOp(Arc::new(call_expr()), BinOp::Eq, Arc::new(PureExpr::Int(0)));

    let rewritten = expr
        .rewrite_bottom_up_prune_with_depth_limit_if_changed(
            8,
            |_| true,
            |node| match node {
                PureExpr::MethodCall { .. } => Some(PureExpr::Int(1)),
                _ => None,
            },
        )
        .expect("method-call substitution should report a change");

    assert_eq!(
        rewritten,
        PureExpr::BinOp(
            Arc::new(PureExpr::Int(1)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0))
        )
    );
}
