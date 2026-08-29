// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ── #2189: Recursive ADT heuristic removed — regression tests ─────────
//
// The unsound heuristic at match_enc/mod.rs:124-140 was removed in #2189.
// All user-defined ADT fields now default to Sort::Int because Pattern
// nodes carry no type information. These tests verify the fix.

/// Binary tree: Node(Tree, i32, Tree) — all fields should be Sort::Int.
///
/// Re: #2189 — unsound heuristic removed
#[test]
#[timeout(30000)]
fn test_switch_target_binary_tree_multiple_recursive_fields() {
    use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

    // Tree::Node(left, value, right) + Tree::Leaf
    let arms = vec![
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Tree::Node".to_string(),
                inner: Some(Box::new(Pattern::Tuple(vec![
                    Pattern::Binding("left".to_string()),
                    Pattern::Binding("value".to_string()),
                    Pattern::Binding("right".to_string()),
                ]))),
            },
            body: PureExpr::Int(0),
        },
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Tree::Leaf".to_string(),
                inner: None,
            },
            body: PureExpr::Int(0),
        },
    ];

    let target = SwitchTarget::from_arms(&arms).expect("should produce UserDefined");
    let dt = target.datatype();

    assert_eq!(dt.name, "Tree");

    let node = &dt.constructors[0];
    assert_eq!(node.name, "Node");
    assert_eq!(node.fields.len(), 3);

    // All fields are Sort::Int — no recursive sort heuristic (#2189)
    assert_eq!(node.fields[0].sort, Sort::Int, "left child should be Int");
    assert_eq!(node.fields[1].sort, Sort::Int, "value field should be Int");
    assert_eq!(
        node.fields[2].sort,
        Sort::Int,
        "right child should be Int (recursive heuristic removed, #2189)"
    );
}

/// Reversed recursive field: Cons(List, i32) — all fields should be Sort::Int.
///
/// Re: #2189 — unsound heuristic removed
#[test]
#[timeout(30000)]
fn test_switch_target_reversed_recursive_field_position() {
    use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

    // List2::Cons(next, value) + List2::Nil
    let arms = vec![
        MatchArm {
            pattern: Pattern::Constructor {
                name: "List2::Cons".to_string(),
                inner: Some(Box::new(Pattern::Tuple(vec![
                    Pattern::Binding("next".to_string()),
                    Pattern::Binding("value".to_string()),
                ]))),
            },
            body: PureExpr::Int(0),
        },
        MatchArm {
            pattern: Pattern::Constructor {
                name: "List2::Nil".to_string(),
                inner: None,
            },
            body: PureExpr::Int(0),
        },
    ];

    let target = SwitchTarget::from_arms(&arms).expect("should produce UserDefined");
    let dt = target.datatype();

    assert_eq!(dt.name, "List2");

    let cons = &dt.constructors[0];
    assert_eq!(cons.name, "Cons");
    assert_eq!(cons.fields.len(), 2);

    // All fields Sort::Int — no heuristic to misclassify (#2189)
    assert_eq!(cons.fields[0].sort, Sort::Int, "next field should be Int");
    assert_eq!(cons.fields[1].sort, Sort::Int, "value field should be Int");
}

/// Non-recursive enum with nullary constructor: all fields should be Sort::Int.
///
/// Re: #2189 — unsound heuristic removed, no false positives
#[test]
#[timeout(30000)]
fn test_switch_target_false_positive_non_recursive_with_nullary() {
    use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

    // Expr::Literal (nullary) + Expr::BinOp(lhs, rhs) — NOT recursive
    let arms = vec![
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Expr::Literal".to_string(),
                inner: None,
            },
            body: PureExpr::Int(0),
        },
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Expr::BinOp".to_string(),
                inner: Some(Box::new(Pattern::Tuple(vec![
                    Pattern::Binding("lhs".to_string()),
                    Pattern::Binding("rhs".to_string()),
                ]))),
            },
            body: PureExpr::Int(1),
        },
    ];

    let target = SwitchTarget::from_arms(&arms).expect("should produce UserDefined");
    let dt = target.datatype();

    assert_eq!(dt.name, "Expr");

    let binop = &dt.constructors[1];
    assert_eq!(binop.name, "BinOp");
    assert_eq!(binop.fields.len(), 2);

    // All fields Sort::Int — no false positive (#2189)
    assert_eq!(binop.fields[0].sort, Sort::Int, "lhs should be Int");
    assert_eq!(
        binop.fields[1].sort,
        Sort::Int,
        "rhs should be Int (no false positive, #2189)"
    );
}
