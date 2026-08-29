// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;

use super::*;

// ── infer_param_datatypes_from_body tests ──────────────────────

#[test]
#[timeout(30000)]
fn test_infer_param_datatypes_direct_var_scrutinee() {
    let logic_fn = simple_logic_fn(
        "dir_to_int",
        vec!["x"],
        match_expr(
            var("x"),
            vec![
                (ctor_pattern("Direction::Left", None), int(1)),
                (ctor_pattern("Direction::Right", None), int(2)),
            ],
        ),
    );
    let result = infer_param_datatypes_from_body(&logic_fn);
    assert!(
        result.contains_key("x"),
        "match x should infer x as Datatype"
    );
    assert_eq!(result["x"].name, "Direction");
}

#[test]
#[timeout(30000)]
fn test_infer_param_datatypes_deref_var_scrutinee() {
    let logic_fn = simple_logic_fn(
        "enum_val",
        vec!["self"],
        match_expr(
            PureExpr::Deref(Arc::new(var("self"))),
            vec![
                (ctor_pattern("MyEnum::A", None), int(1)),
                (ctor_pattern("MyEnum::B", None), int(2)),
            ],
        ),
    );
    let result = infer_param_datatypes_from_body(&logic_fn);
    assert!(
        result.contains_key("self"),
        "match *self should infer self as Datatype"
    );
    assert_eq!(result["self"].name, "MyEnum");
}

#[test]
#[timeout(30000)]
fn test_infer_param_datatypes_option_filtered_out() {
    let logic_fn = simple_logic_fn(
        "option_fn",
        vec!["x"],
        match_expr(
            var("x"),
            vec![
                (
                    ctor_pattern("Some", Some(Pattern::Binding("v".to_string()))),
                    var("v"),
                ),
                (ctor_pattern("None", None), int(0)),
            ],
        ),
    );
    let result = infer_param_datatypes_from_body(&logic_fn);
    assert!(
        result.is_empty(),
        "Option should be filtered out as non-UserDefined"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_param_datatypes_result_filtered_out() {
    let logic_fn = simple_logic_fn(
        "result_fn",
        vec!["x"],
        match_expr(
            var("x"),
            vec![
                (
                    ctor_pattern("Ok", Some(Pattern::Binding("v".to_string()))),
                    var("v"),
                ),
                (
                    ctor_pattern("Err", Some(Pattern::Binding("e".to_string()))),
                    int(0),
                ),
            ],
        ),
    );
    let result = infer_param_datatypes_from_body(&logic_fn);
    assert!(
        result.is_empty(),
        "Result should be filtered out as non-UserDefined"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_param_datatypes_non_param_scrutinee_ignored() {
    let logic_fn = simple_logic_fn(
        "non_param",
        vec!["x"],
        match_expr(
            var("local_var"),
            vec![(ctor_pattern("MyType::A", None), int(1))],
        ),
    );
    let result = infer_param_datatypes_from_body(&logic_fn);
    assert!(
        result.is_empty(),
        "non-param scrutinee should not be inferred"
    );
}

#[test]
#[timeout(30000)]
fn test_infer_param_datatypes_in_requires_clause() {
    let mut logic_fn = simple_logic_fn("color_fn", vec!["x"], int(0));
    logic_fn.requires_mut().push(match_expr(
        var("x"),
        vec![
            (ctor_pattern("Color::Red", None), PureExpr::Bool(true)),
            (ctor_pattern("Color::Blue", None), PureExpr::Bool(true)),
        ],
    ));
    let result = infer_param_datatypes_from_body(&logic_fn);
    assert!(
        result.contains_key("x"),
        "match in requires should infer param datatype"
    );
    assert_eq!(result["x"].name, "Color");
}

#[test]
#[timeout(30000)]
fn test_infer_param_datatypes_first_match_wins() {
    let logic_fn = simple_logic_fn(
        "double_match",
        vec!["x"],
        PureExpr::BinOp(
            Arc::new(match_expr(
                var("x"),
                vec![
                    (ctor_pattern("TypeA::Foo", None), int(1)),
                    (ctor_pattern("TypeA::Bar", None), int(2)),
                ],
            )),
            trust_wp_core::formula::BinOp::Add,
            Arc::new(match_expr(
                var("x"),
                vec![(ctor_pattern("TypeB::Baz", None), int(3))],
            )),
        ),
    );
    let result = infer_param_datatypes_from_body(&logic_fn);
    assert_eq!(result["x"].name, "TypeA", "first match should win");
}

#[test]
#[timeout(30000)]
fn test_infer_param_datatypes_nested_match_in_arm_body() {
    let logic_fn = simple_logic_fn(
        "nested",
        vec!["x", "y"],
        match_expr(
            var("x"),
            vec![(
                ctor_pattern("TypeA::V1", None),
                match_expr(var("y"), vec![(ctor_pattern("TypeB::W1", None), int(1))]),
            )],
        ),
    );
    let result = infer_param_datatypes_from_body(&logic_fn);
    assert!(result.contains_key("x"), "outer match should infer x");
    assert!(result.contains_key("y"), "nested match should infer y");
    assert_eq!(result["x"].name, "TypeA");
    assert_eq!(result["y"].name, "TypeB");
}

// ── infer_param_datatypes nesting coverage ──────────────────────

#[test]
#[timeout(30000)]
fn test_infer_param_datatypes_in_ite_branch() {
    let logic_fn = simple_logic_fn(
        "ite_match",
        vec!["x"],
        PureExpr::Ite(
            Arc::new(PureExpr::Bool(true)),
            Arc::new(match_expr(
                var("x"),
                vec![
                    (ctor_pattern("Shape::Circle", None), int(1)),
                    (ctor_pattern("Shape::Square", None), int(2)),
                ],
            )),
            Arc::new(int(0)),
        ),
    );
    let result = infer_param_datatypes_from_body(&logic_fn);
    assert!(
        result.contains_key("x"),
        "match inside Ite branch should infer x as Datatype"
    );
    assert_eq!(result["x"].name, "Shape");
}

#[test]
#[timeout(30000)]
fn test_infer_param_datatypes_in_let_body() {
    use trust_wp_core::formula::PureExpr;

    let logic_fn = simple_logic_fn(
        "let_match",
        vec!["x"],
        PureExpr::Let {
            var: "tmp".to_string(),
            value: Arc::new(int(0)),
            body: Arc::new(match_expr(
                var("x"),
                vec![
                    (ctor_pattern("Animal::Cat", None), int(1)),
                    (ctor_pattern("Animal::Dog", None), int(2)),
                ],
            )),
        },
    );
    let result = infer_param_datatypes_from_body(&logic_fn);
    assert!(
        result.contains_key("x"),
        "match inside Let body should infer x as Datatype"
    );
    assert_eq!(result["x"].name, "Animal");
}

#[test]
#[timeout(30000)]
fn test_infer_param_datatypes_in_closure() {
    let logic_fn = simple_logic_fn(
        "closure_match",
        vec!["x"],
        PureExpr::Closure {
            params: vec![("_".to_string(), None)],
            body: Arc::new(match_expr(
                var("x"),
                vec![
                    (ctor_pattern("Suit::Hearts", None), int(1)),
                    (ctor_pattern("Suit::Spades", None), int(2)),
                ],
            )),
        },
    );
    let result = infer_param_datatypes_from_body(&logic_fn);
    assert!(
        result.contains_key("x"),
        "match inside Closure should infer x as Datatype"
    );
    assert_eq!(result["x"].name, "Suit");
}

#[test]
#[timeout(30000)]
fn test_infer_param_datatypes_in_forall() {
    let logic_fn = simple_logic_fn(
        "forall_match",
        vec!["x"],
        PureExpr::Forall {
            var: "i".to_string(),
            var_sort: None,
            body: Arc::new(match_expr(
                var("x"),
                vec![(ctor_pattern("Mode::Fast", None), PureExpr::Bool(true))],
            )),
            triggers: vec![],
        },
    );
    let result = infer_param_datatypes_from_body(&logic_fn);
    assert!(
        result.contains_key("x"),
        "match inside Forall body should infer x as Datatype"
    );
    assert_eq!(result["x"].name, "Mode");
}
