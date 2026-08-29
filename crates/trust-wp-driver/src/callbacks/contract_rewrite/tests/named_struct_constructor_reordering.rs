// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// --- Named struct constructor reordering tests (#1819) ---

/// Regression #1819: struct literal with reversed field order must reorder.
/// Point { y: 1, x: 0 } with field_map {x:0, y:1} → Point(0, 1).
#[test]
fn reorders_named_struct_literal_to_canonical() {
    let mut field_map = HashMap::new();
    field_map.insert("x".to_string(), 0);
    field_map.insert("y".to_string(), 1);

    // Parser output: LogicFnCall { name: "Point{y,x}", args: [1, 0] }
    let expr = PureExpr::LogicFnCall {
        name: "Point{y,x}".to_string(),
        args: vec![PureExpr::Int(1), PureExpr::Int(0)],
    };
    let result = rewrite_named_field_access_expr(&expr, &field_map);
    // After rewrite: LogicFnCall { name: "Point", args: [0, 1] }
    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: "Point".to_string(),
            args: vec![PureExpr::Int(0), PureExpr::Int(1)],
        }
    );
}

/// Regression #1819: struct literal in canonical order produces same result.
#[test]
fn reorders_named_struct_literal_already_canonical() {
    let mut field_map = HashMap::new();
    field_map.insert("x".to_string(), 0);
    field_map.insert("y".to_string(), 1);

    let expr = PureExpr::LogicFnCall {
        name: "Point{x,y}".to_string(),
        args: vec![PureExpr::Int(0), PureExpr::Int(1)],
    };
    let result = rewrite_named_field_access_expr(&expr, &field_map);
    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: "Point".to_string(),
            args: vec![PureExpr::Int(0), PureExpr::Int(1)],
        }
    );
}

/// Regression #1819: unknown field name falls back to source order.
#[test]
fn reorder_named_fields_unknown_field_falls_back() {
    let mut field_map = HashMap::new();
    field_map.insert("x".to_string(), 0);
    // "z" is not in field_map

    let field_names = ["z", "x"];
    let args = vec![PureExpr::Int(99), PureExpr::Int(0)];
    let result = reorder_named_fields_to_positional(&field_names, &args, &field_map);
    // Should fall back to source order (no reordering)
    assert_eq!(result, vec![PureExpr::Int(99), PureExpr::Int(0)]);
}

/// Regression #1819: mismatched arg count falls back to source order.
#[test]
fn reorder_named_fields_mismatched_length_falls_back() {
    let mut field_map = HashMap::new();
    field_map.insert("x".to_string(), 0);
    field_map.insert("y".to_string(), 1);

    let field_names = ["x"];
    let args = vec![PureExpr::Int(0), PureExpr::Int(1)]; // 2 args, 1 name
    let result = reorder_named_fields_to_positional(&field_names, &args, &field_map);
    assert_eq!(result, vec![PureExpr::Int(0), PureExpr::Int(1)]);
}

/// Regression #1819: struct pattern with reversed fields must reorder.
#[test]
fn reorders_named_struct_pattern_to_canonical() {
    use trust_wp_core::formula::Pattern;

    let mut field_map = HashMap::new();
    field_map.insert("x".to_string(), 0);
    field_map.insert("y".to_string(), 1);

    // Parser output: Constructor { name: "Point{y,x}", inner: Tuple([Binding("y"), Binding("x")]) }
    let pattern = Pattern::Constructor {
        name: "Point{y,x}".to_string(),
        inner: Some(Box::new(Pattern::Tuple(vec![
            Pattern::Binding("y".to_string()),
            Pattern::Binding("x".to_string()),
        ]))),
    };
    let result = rewrite_named_struct_pattern(&pattern, &field_map);
    // After rewrite: Constructor { name: "Point", inner: Tuple([Binding("x"), Binding("y")]) }
    assert_eq!(
        result,
        Pattern::Constructor {
            name: "Point".to_string(),
            inner: Some(Box::new(Pattern::Tuple(vec![
                Pattern::Binding("x".to_string()),
                Pattern::Binding("y".to_string()),
            ]))),
        }
    );
}

#[test]
fn rewrite_named_field_access_rewrites_match_patterns_and_bodies_together() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    let mut field_map = HashMap::new();
    field_map.insert("x".to_string(), 0);
    field_map.insert("y".to_string(), 1);

    let expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("p".to_string(), None)),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: "Point{y,x}".to_string(),
                inner: Some(Box::new(Pattern::Tuple(vec![
                    Pattern::Binding("y".to_string()),
                    Pattern::Binding("x".to_string()),
                ]))),
            },
            body: PureExpr::LogicFnCall {
                name: "__trust_wp_field_y".to_string(),
                args: vec![PureExpr::Var("p".to_string(), None)],
            },
        }],
    };

    let result = rewrite_named_field_access_expr(&expr, &field_map);
    assert_eq!(
        result,
        PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("p".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: "Point".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("x".to_string()),
                        Pattern::Binding("y".to_string()),
                    ]))),
                },
                body: PureExpr::LogicFnCall {
                    name: "__trust_wp_tuple_get_1".to_string(),
                    args: vec![PureExpr::Var("p".to_string(), None)],
                },
            }],
        }
    );
}

#[test]
fn rewrite_named_field_access_rewrites_match_quantifier_triggers_and_patterns() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    let mut field_map = HashMap::new();
    field_map.insert("x".to_string(), 0);
    field_map.insert("y".to_string(), 1);

    let expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("p".to_string(), None)),
        arms: vec![MatchArm {
            pattern: Pattern::Constructor {
                name: "Point{y,x}".to_string(),
                inner: Some(Box::new(Pattern::Tuple(vec![
                    Pattern::Binding("y".to_string()),
                    Pattern::Binding("x".to_string()),
                ]))),
            },
            body: PureExpr::Forall {
                var: "i".to_string(),
                var_sort: Some(ExprSort::Int),
                body: Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::LogicFnCall {
                        name: "__trust_wp_field_y".to_string(),
                        args: vec![PureExpr::Var("p".to_string(), None)],
                    }),
                    BinOp::Ge,
                    Arc::new(PureExpr::Var("i".to_string(), None)),
                )),
                triggers: vec![vec![PureExpr::LogicFnCall {
                    name: "__trust_wp_field_x".to_string(),
                    args: vec![PureExpr::Var("p".to_string(), None)],
                }]],
            },
        }],
    };

    let result = rewrite_named_field_access_expr(&expr, &field_map);
    assert_eq!(
        result,
        PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("p".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: "Point".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("x".to_string()),
                        Pattern::Binding("y".to_string()),
                    ]))),
                },
                body: PureExpr::Forall {
                    var: "i".to_string(),
                    var_sort: Some(ExprSort::Int),
                    body: Arc::new(PureExpr::BinOp(
                        Arc::new(PureExpr::LogicFnCall {
                            name: "__trust_wp_tuple_get_1".to_string(),
                            args: vec![PureExpr::Var("p".to_string(), None)],
                        }),
                        BinOp::Ge,
                        Arc::new(PureExpr::Var("i".to_string(), None)),
                    )),
                    triggers: vec![vec![PureExpr::LogicFnCall {
                        name: "__trust_wp_tuple_get_0".to_string(),
                        args: vec![PureExpr::Var("p".to_string(), None)],
                    }]],
                },
            }],
        }
    );
}

/// Regression #1819: single-field struct pattern is not wrapped in Tuple.
#[test]
fn reorders_single_field_struct_pattern() {
    use trust_wp_core::formula::Pattern;

    let mut field_map = HashMap::new();
    field_map.insert("val".to_string(), 0);

    let pattern = Pattern::Constructor {
        name: "Wrapper{val}".to_string(),
        inner: Some(Box::new(Pattern::Binding("v".to_string()))),
    };
    let result = rewrite_named_struct_pattern(&pattern, &field_map);
    assert_eq!(
        result,
        Pattern::Constructor {
            name: "Wrapper".to_string(),
            inner: Some(Box::new(Pattern::Binding("v".to_string()))),
        }
    );
}

/// Regression #1819: three-field reorder with non-trivial permutation.
#[test]
fn reorders_three_field_struct_literal() {
    let mut field_map = HashMap::new();
    field_map.insert("a".to_string(), 0);
    field_map.insert("b".to_string(), 1);
    field_map.insert("c".to_string(), 2);

    // User writes: Triple { c: 2, a: 0, b: 1 }
    let expr = PureExpr::LogicFnCall {
        name: "Triple{c,a,b}".to_string(),
        args: vec![PureExpr::Int(2), PureExpr::Int(0), PureExpr::Int(1)],
    };
    let result = rewrite_named_field_access_expr(&expr, &field_map);
    // Canonical order: Triple(0, 1, 2)
    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: "Triple".to_string(),
            args: vec![PureExpr::Int(0), PureExpr::Int(1), PureExpr::Int(2)],
        }
    );
}
