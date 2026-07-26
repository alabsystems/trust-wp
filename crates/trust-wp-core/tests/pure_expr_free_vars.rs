// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, ExprSort, MatchArm, Pattern, PureExpr};

#[test]
fn free_vars_keeps_value_side_let_shadowing() {
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("y".to_string(), None)),
        )),
    };

    let vars = expr.free_vars();

    assert!(
        vars.contains("x"),
        "outer x from let value should remain free"
    );
    assert!(vars.contains("y"), "y from let body should remain free");
}

#[test]
fn free_vars_keeps_outer_var_when_quantifier_shadows_sibling() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Var("x".to_string(), None)),
            triggers: vec![],
        }),
    );

    let vars = expr.free_vars();

    assert!(
        vars.contains("x"),
        "outer x outside the quantifier should remain free"
    );
}

#[test]
fn free_vars_keeps_outer_var_when_quantifier_trigger_shadows_sibling() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Bool(true)),
            triggers: vec![vec![PureExpr::LogicFnCall {
                name: "f".to_string(),
                args: vec![
                    PureExpr::Var("x".to_string(), None),
                    PureExpr::Var("y".to_string(), None),
                ],
            }]],
        }),
    );

    let vars = expr.free_vars();

    assert!(
        vars.contains("x"),
        "outer x outside the quantifier trigger should remain free"
    );
    assert!(vars.contains("y"), "free trigger var y should be collected");
    assert_eq!(
        vars.len(),
        2,
        "only outer x and trigger var y should be free"
    );
}

#[test]
fn free_vars_excludes_quantifier_bound_var_from_trigger() {
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![vec![PureExpr::LogicFnCall {
            name: "f".to_string(),
            args: vec![
                PureExpr::Var("x".to_string(), None),
                PureExpr::Var("y".to_string(), None),
            ],
        }]],
    };

    let vars = expr.free_vars();

    assert!(
        !vars.contains("x"),
        "bound trigger var x should not be free"
    );
    assert!(vars.contains("y"), "free trigger var y should remain free");
    assert_eq!(vars.len(), 1, "only y should remain free");
}

#[test]
fn free_vars_keeps_outer_var_when_closure_param_shadows_sibling() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Closure {
            params: vec![("x".to_string(), None)],
            body: Arc::new(PureExpr::Var("x".to_string(), None)),
        }),
    );

    let vars = expr.free_vars();

    assert!(
        vars.contains("x"),
        "outer x outside the closure should remain free"
    );
}

#[test]
fn free_vars_keeps_outer_var_when_match_arm_shadows_sibling() {
    // x + match y { Some(x) => x + z, _ => 0 }
    // Outer x must remain free despite the Some(x) binding in the arm.
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("y".to_string(), None)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                    },
                    body: PureExpr::BinOp(
                        Arc::new(PureExpr::Var("x".to_string(), None)),
                        BinOp::Add,
                        Arc::new(PureExpr::Var("z".to_string(), None)),
                    ),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    body: PureExpr::Int(0),
                },
            ],
        }),
    );

    let vars = expr.free_vars();

    assert!(
        vars.contains("x"),
        "outer x outside the match arm should remain free"
    );
    assert!(vars.contains("y"), "scrutinee var y should be free");
    assert!(vars.contains("z"), "arm body var z should be free");
    assert_eq!(vars.len(), 3, "only x, y, z should be free");
}

#[test]
fn pattern_binds_name_binding() {
    assert!(Pattern::Binding("x".to_string()).binds_name("x"));
    assert!(!Pattern::Binding("x".to_string()).binds_name("y"));
}

#[test]
fn pattern_binds_name_wildcard_and_literal() {
    assert!(!Pattern::Wildcard.binds_name("x"));
    assert!(!Pattern::Literal(PureExpr::Int(0)).binds_name("x"));
}

#[test]
fn pattern_binds_name_constructor() {
    let pat = Pattern::Constructor {
        name: "Some".to_string(),
        inner: Some(Box::new(Pattern::Binding("x".to_string()))),
    };
    assert!(pat.binds_name("x"));
    assert!(!pat.binds_name("y"));

    let pat_none = Pattern::Constructor {
        name: "None".to_string(),
        inner: None,
    };
    assert!(!pat_none.binds_name("x"));
}

#[test]
fn pattern_binds_name_tuple() {
    let pat = Pattern::Tuple(vec![
        Pattern::Binding("a".to_string()),
        Pattern::Binding("b".to_string()),
    ]);
    assert!(pat.binds_name("a"));
    assert!(pat.binds_name("b"));
    assert!(!pat.binds_name("c"));
}

#[test]
fn any_recursive_visits_quantifier_triggers_and_match_arm_bodies() {
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("xs".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                },
                body: PureExpr::LogicFnCall {
                    name: "want_body".to_string(),
                    args: vec![PureExpr::Var("x".to_string(), None)],
                },
            }],
        }),
        triggers: vec![vec![PureExpr::LogicFnCall {
            name: "want_trigger".to_string(),
            args: vec![PureExpr::Var("i".to_string(), None)],
        }]],
    };

    assert!(expr.any_recursive(
        |node| matches!(node, PureExpr::LogicFnCall { name, .. } if name == "want_body")
    ));
    assert!(expr.any_recursive(
        |node| matches!(node, PureExpr::LogicFnCall { name, .. } if name == "want_trigger")
    ));
}

#[test]
fn for_each_recursive_collects_nested_var_names() {
    let expr = PureExpr::Closure {
        params: vec![("f".to_string(), Some(ExprSort::Int))],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("outer".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "inner".to_string(),
                None,
            )))),
        )),
    };

    let mut vars = Vec::new();
    expr.for_each_recursive(|node| {
        if let PureExpr::Var(name, _) = node {
            vars.push(name.clone());
        }
    });

    assert_eq!(vars, vec!["outer".to_string(), "inner".to_string()]);
}

#[test]
fn rewrite_bottom_up_preserves_metadata_and_skips_match_patterns() {
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Seq),
        body: Arc::new(PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("xs".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Binding("bound".to_string()),
                body: PureExpr::Closure {
                    params: vec![("param".to_string(), Some(ExprSort::Bool))],
                    body: Arc::new(PureExpr::Var("bound".to_string(), None)),
                },
            }],
        }),
        triggers: vec![vec![PureExpr::Var("xs".to_string(), None)]],
    };

    let rewritten = expr.rewrite_bottom_up(|node| match node {
        PureExpr::Var(name, sort) if name == "xs" => PureExpr::Var("ys".to_string(), sort),
        other => other,
    });

    match rewritten {
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            assert_eq!(var, "i");
            assert_eq!(var_sort, Some(ExprSort::Seq));
            assert_eq!(triggers, vec![vec![PureExpr::Var("ys".to_string(), None)]]);
            match body.as_ref() {
                PureExpr::Match { scrutinee, arms } => {
                    assert_eq!(**scrutinee, PureExpr::Var("ys".to_string(), None));
                    assert_eq!(arms.len(), 1);
                    assert_eq!(arms[0].pattern, Pattern::Binding("bound".to_string()));
                    match &arms[0].body {
                        PureExpr::Closure { params, body } => {
                            assert_eq!(params, &vec![("param".to_string(), Some(ExprSort::Bool))]);
                            assert_eq!(**body, PureExpr::Var("bound".to_string(), None));
                        }
                        other => panic!("expected Closure, got {other:?}"),
                    }
                }
                other => panic!("expected Match, got {other:?}"),
            }
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn rewrite_bottom_up_reuses_unchanged_sibling_arc() {
    let shared_left = Arc::new(PureExpr::Var("x".to_string(), None));
    let shared_right = Arc::new(PureExpr::Var("y".to_string(), None));
    let expr = PureExpr::BinOp(
        Arc::clone(&shared_left),
        BinOp::Add,
        Arc::clone(&shared_right),
    );

    let rewritten = expr.rewrite_bottom_up(|node| match node {
        PureExpr::Var(name, sort) if name == "x" => PureExpr::Var("z".to_string(), sort),
        other => other,
    });

    match rewritten {
        PureExpr::BinOp(left, BinOp::Add, right) => {
            assert_eq!(left.as_ref(), &PureExpr::Var("z".to_string(), None));
            assert!(
                !Arc::ptr_eq(&left, &shared_left),
                "rewritten child should allocate a new Arc"
            );
            assert!(
                Arc::ptr_eq(&right, &shared_right),
                "unchanged sibling should reuse its existing Arc"
            );
        }
        other => panic!("expected BinOp(Add), got {other:?}"),
    }
}
