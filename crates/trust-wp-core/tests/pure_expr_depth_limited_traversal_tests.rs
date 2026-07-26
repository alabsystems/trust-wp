// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{
    BinOp, ExprSort, MatchArm, Pattern, PureExpr, PureExprDepthLimitedTraversalExt,
};

fn arc(expr: PureExpr) -> Arc<PureExpr> {
    Arc::new(expr)
}

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn int(value: i64) -> PureExpr {
    PureExpr::Int(value)
}

#[test]
fn any_recursive_with_depth_limit_finds_nested_node_within_limit() {
    let expr = PureExpr::BinOp(arc(var("x")), BinOp::Add, arc(int(1)));
    assert!(expr.any_recursive_with_depth_limit(1, false, |node| {
        matches!(node, PureExpr::Var(name, _) if name == "x")
    }));
}

#[test]
fn any_recursive_with_depth_limit_fail_open_skips_too_deep_children() {
    let expr = PureExpr::BinOp(arc(var("x")), BinOp::Add, arc(int(1)));
    assert!(!expr.any_recursive_with_depth_limit(0, false, |node| {
        matches!(node, PureExpr::Var(name, _) if name == "x")
    }));
}

#[test]
fn any_recursive_with_depth_limit_fail_closed_returns_true_at_limit() {
    let expr = PureExpr::BinOp(arc(var("x")), BinOp::Add, arc(int(1)));
    assert!(expr.any_recursive_with_depth_limit(0, true, |node| {
        matches!(node, PureExpr::Var(name, _) if name == "x")
    }));
}

#[test]
fn for_each_recursive_with_depth_limit_skips_too_deep_children() {
    let expr = PureExpr::Ite(
        arc(var("cond")),
        arc(PureExpr::MethodCall {
            receiver: arc(var("recv")),
            method: "len".to_string(),
            args: vec![var("arg")],
        }),
        arc(int(0)),
    );
    let mut visited = Vec::new();

    expr.for_each_recursive_with_depth_limit(1, |node| {
        let kind = match node {
            PureExpr::Ite(..) => "ite",
            PureExpr::Var(name, _) => name.as_str(),
            PureExpr::MethodCall { method, .. } => method.as_str(),
            PureExpr::Int(_) => "int",
            other => panic!("unexpected node visited: {other:?}"),
        };
        visited.push(kind.to_string());
    });

    assert_eq!(visited, vec!["ite", "cond", "len", "int"]);
}

#[test]
fn for_each_recursive_with_depth_limit_visits_quantifier_triggers() {
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: arc(var("body")),
        triggers: vec![vec![var("trigger")]],
    };
    let mut visited = Vec::new();

    expr.for_each_recursive_with_depth_limit(1, |node| {
        if let PureExpr::Var(name, _) = node {
            visited.push(name.clone());
        }
    });

    assert_eq!(visited, vec!["body".to_string(), "trigger".to_string()]);
}

#[test]
fn rewrite_bottom_up_with_depth_limit_rewrites_root_at_limit() {
    let expr = PureExpr::Deref(arc(var("x")));
    let result = expr.rewrite_bottom_up_with_depth_limit(0, |node| match node {
        PureExpr::Deref(inner) => inner.as_ref().clone(),
        other => other,
    });
    assert_eq!(result, var("x"));
}

#[test]
fn rewrite_bottom_up_with_depth_limit_preserves_too_deep_children() {
    let expr = PureExpr::BinOp(arc(var("x")), BinOp::Add, arc(int(1)));
    let result = expr.rewrite_bottom_up_with_depth_limit(0, |node| match node {
        PureExpr::Var(name, sort) if name == "x" => PureExpr::Var("y".to_string(), sort),
        other => other,
    });
    assert_eq!(result, expr);
}

#[test]
fn rewrite_bottom_up_with_depth_limit_recurses_through_quantifier_triggers() {
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: arc(int(1)),
        triggers: vec![vec![int(2)]],
    };
    let result = expr.rewrite_bottom_up_with_depth_limit(2, |node| match node {
        PureExpr::Int(value) => int(value * 10),
        other => other,
    });
    match result {
        PureExpr::Forall { body, triggers, .. } => {
            assert_eq!(body.as_ref(), &int(10));
            assert_eq!(triggers[0][0], int(20));
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

// === Exact depth boundary: depth==limit processes; depth==limit+1 skips ===

#[test]
fn any_depth_limit_exact_boundary_depth_equals_limit_processes() {
    // Depth 0: BinOp root. Depth 1: Var("x"), Int(1).
    // With limit=1, both children are visited (depth 1 == limit, not >).
    let expr = PureExpr::BinOp(arc(var("x")), BinOp::Add, arc(int(1)));
    let found =
        expr.any_recursive_with_depth_limit(1, false, |node| matches!(node, PureExpr::Int(1)));
    assert!(found, "depth==limit should still process the node");
}

#[test]
fn any_depth_limit_exact_boundary_depth_exceeds_limit_skips() {
    // Tree: UnOp(Not, BinOp(Var("x"), Add, Int(1)))
    // Depth 0: UnOp. Depth 1: BinOp. Depth 2: Var("x"), Int(1).
    // With limit=1, depth-2 children are NOT visited.
    let inner = PureExpr::BinOp(arc(var("x")), BinOp::Add, arc(int(1)));
    let expr = PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, arc(inner));
    let found =
        expr.any_recursive_with_depth_limit(1, false, |node| matches!(node, PureExpr::Int(1)));
    assert!(!found, "depth > limit should skip (fail-open)");
}

#[test]
fn any_depth_limit_fail_closed_at_exact_overflow() {
    // Same tree as above, but with on_limit=true.
    let inner = PureExpr::BinOp(arc(var("x")), BinOp::Add, arc(int(1)));
    let expr = PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, arc(inner));
    let found = expr.any_recursive_with_depth_limit(1, true, |_| false);
    assert!(
        found,
        "fail-closed should return true when depth exceeds limit"
    );
}

#[test]
fn for_each_depth_limit_exact_boundary_counts() {
    // UnOp(Not, BinOp(Var("x"), Add, Int(1)))
    // Depth 0: UnOp. Depth 1: BinOp. Depth 2: Var, Int.
    // limit=1: visits UnOp(0) and BinOp(1). Skips Var(2) and Int(2).
    let inner = PureExpr::BinOp(arc(var("x")), BinOp::Add, arc(int(1)));
    let expr = PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, arc(inner));
    let mut count = 0;
    expr.for_each_recursive_with_depth_limit(1, |_| count += 1);
    assert_eq!(
        count, 2,
        "limit=1 visits root(0) and child(1), skips depth-2"
    );
}

// === Match arm and Closure in depth-limited traversal ===

#[test]
fn any_depth_limit_enters_match_arm_body() {
    let expr = PureExpr::Match {
        scrutinee: arc(int(0)),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: var("target"),
        }],
    };
    let found = expr.any_recursive_with_depth_limit(
        2,
        false,
        |node| matches!(node, PureExpr::Var(name, _) if name == "target"),
    );
    assert!(found, "should descend into match arm bodies");
}

#[test]
fn any_depth_limit_match_arm_body_skipped_beyond_limit() {
    // Match at depth 0, arm.body at depth 1.
    // With limit=0, only the Match root is checked.
    let expr = PureExpr::Match {
        scrutinee: arc(int(0)),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: var("target"),
        }],
    };
    let found = expr.any_recursive_with_depth_limit(
        0,
        false,
        |node| matches!(node, PureExpr::Var(name, _) if name == "target"),
    );
    assert!(!found, "limit=0 should not descend into match arm body");
}

#[test]
fn any_depth_limit_enters_closure_body() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), Some(ExprSort::Int))],
        body: arc(var("target")),
    };
    let found = expr.any_recursive_with_depth_limit(
        1,
        false,
        |node| matches!(node, PureExpr::Var(name, _) if name == "target"),
    );
    assert!(found, "should descend into closure body");
}

#[test]
fn rewrite_depth_limit_preserves_match_arm_pattern() {
    // Rewrite should only affect arm bodies, never patterns.
    let expr = PureExpr::Match {
        scrutinee: arc(int(0)),
        arms: vec![MatchArm {
            pattern: Pattern::Binding("x".to_string()),
            body: int(1),
        }],
    };
    let result = expr.rewrite_bottom_up_with_depth_limit(2, |node| match node {
        PureExpr::Int(v) => int(v * 10),
        other => other,
    });
    match result {
        PureExpr::Match { scrutinee, arms } => {
            assert_eq!(scrutinee.as_ref(), &int(0));
            assert_eq!(arms[0].pattern, Pattern::Binding("x".to_string()));
            assert_eq!(arms[0].body, int(10));
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn rewrite_depth_limit_let_rewrites_value_and_body() {
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: arc(int(1)),
        body: arc(int(2)),
    };
    let result = expr.rewrite_bottom_up_with_depth_limit(2, |node| match node {
        PureExpr::Int(v) => int(v * 10),
        other => other,
    });
    match result {
        PureExpr::Let { value, body, .. } => {
            assert_eq!(value.as_ref(), &int(10));
            assert_eq!(body.as_ref(), &int(20));
        }
        other => panic!("expected Let, got {other:?}"),
    }
}
