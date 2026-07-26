// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// --- Field access tests ---

#[test]
fn test_parse_named_field() {
    // point.x — named field access
    let expr = parse_ok("point.x");
    assert_eq!(
        expr,
        PureExpr::LogicFnCall {
            name: "__trust_wp_field_x".into(),
            args: vec![PureExpr::Var("point".into(), None)],
        }
    );
}

#[test]
fn test_parse_named_field_in_comparison() {
    // result == point.x — field access in equality
    let expr = parse_ok("result == point.x");
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Eq, _)));
}

#[test]
fn test_parse_chained_field_then_method() {
    // self.data.len() — field access then method call
    let expr = parse_contract("self.data.len()").unwrap();
    if let PureExpr::MethodCall {
        receiver, method, ..
    } = &expr
    {
        assert_eq!(method, "len");
        assert!(matches!(**receiver, PureExpr::LogicFnCall { .. }));
    } else {
        panic!("Expected MethodCall, got {expr:?}");
    }
}

#[test]
fn test_parse_deref_field() {
    // *self.field — dereference + field access
    // Parses as *(self.field) since deref is unary prefix
    let expr = parse_ok("*self.field");
    assert!(matches!(
        expr,
        PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::LogicFnCall { .. })
    ));
}

#[test]
fn test_parse_field_with_view() {
    // self.data@ — field then view
    let expr = parse_ok("self.data@");
    assert!(matches!(
        expr,
        PureExpr::View(inner) if matches!(inner.as_ref(), PureExpr::LogicFnCall { .. })
    ));
}

#[test]
fn test_parse_field_spanned() {
    let input = "point.x";
    let regular = parse_ok(input);
    let spanned = parse_spanned_ok(input);
    assert_eq!(regular, spanned.expr);
}

// --- Tuple field tests ---

#[test]
fn test_parse_tuple_field_0() {
    // x.0 — first field of tuple
    let expr = parse_ok("x.0");
    assert_eq!(
        expr,
        PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![PureExpr::Var("x".into(), None)],
        }
    );
}

#[test]
fn test_parse_tuple_field_1() {
    // x.1 — second field of tuple
    let expr = parse_ok("x.1");
    assert_eq!(
        expr,
        PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(1),
            args: vec![PureExpr::Var("x".into(), None)],
        }
    );
}

#[test]
fn test_parse_tuple_field_in_tuple() {
    // result == (x.1, x.0) — the exact case from issue #504
    let expr = parse_contract("result == (x.1, x.0)").unwrap();
    if let PureExpr::BinOp(left, BinOp::Eq, right) = &expr {
        assert_eq!(**left, PureExpr::Var("result".into(), None));
        assert_eq!(
            **right,
            PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(2),
                args: vec![
                    PureExpr::LogicFnCall {
                        name: tuple_field_logic_fn_name(1),
                        args: vec![PureExpr::Var("x".into(), None)],
                    },
                    PureExpr::LogicFnCall {
                        name: tuple_field_logic_fn_name(0),
                        args: vec![PureExpr::Var("x".into(), None)],
                    },
                ],
            }
        );
    } else {
        panic!("Expected BinOp(Eq), got {expr:?}");
    }
}

#[test]
fn test_parse_tuple_field_chained() {
    // x.0.1 — nested tuple field access
    let expr = parse_ok("x.0.1");
    assert_eq!(
        expr,
        PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(1),
            args: vec![PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(0),
                args: vec![PureExpr::Var("x".into(), None)],
            }],
        }
    );
}

#[test]
fn test_parse_tuple_field_with_view() {
    // x@.0 — view then tuple field access
    let expr = parse_ok("x@.0");
    assert_eq!(
        expr,
        PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![PureExpr::View(Arc::new(PureExpr::Var("x".into(), None)))],
        }
    );
}

#[test]
fn test_parse_tuple_field_in_comparison() {
    // pair.0 > 0 — tuple field in comparison
    let expr = parse_ok("pair.0 > 0");
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Gt, r)
        if matches!(l.as_ref(), PureExpr::LogicFnCall { .. })
        && matches!(r.as_ref(), PureExpr::Int(0))
    ));
}

#[test]
fn test_parse_tuple_field_spanned() {
    // Verify spanned parsing produces same AST
    let input = "x.0";
    let regular = parse_ok(input);
    let spanned = parse_spanned_ok(input);
    assert_eq!(regular, spanned.expr, "AST mismatch for input: {input}");
}

#[test]
fn test_parse_tuple_field_spanned_complex() {
    // Verify spanned parsing for the issue example
    let input = "result == (x.1, x.0)";
    let regular = parse_ok(input);
    let spanned = parse_spanned_ok(input);
    assert_eq!(regular, spanned.expr, "AST mismatch for input: {input}");
}

// --- Indexing tests ---

#[test]
fn test_parse_simple_index() {
    // v[0] — simple integer index
    let expr = parse_ok("v[0]");
    assert_eq!(
        expr,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("v".into(), None)),
            method: "index_logic".into(),
            args: vec![PureExpr::Int(0)],
        }
    );
}

#[test]
fn test_parse_variable_index() {
    // arr[i] — variable index
    let expr = parse_ok("arr[i]");
    assert_eq!(
        expr,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("arr".into(), None)),
            method: "index_logic".into(),
            args: vec![PureExpr::Var("i".into(), None)],
        }
    );
}

#[test]
fn test_parse_index_with_suffix() {
    // v[12usize] — index with type suffix
    let expr = parse_ok("v[12usize]");
    assert_eq!(
        expr,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("v".into(), None)),
            method: "index_logic".into(),
            args: vec![PureExpr::Int(12)],
        }
    );
}

#[test]
fn test_parse_index_in_equality() {
    // result == v[12] — indexing in contract
    let expr = parse_ok("result == v[12]");
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Eq, _)));
}

#[test]
fn test_parse_view_then_index() {
    // v@[i] — view then index
    let expr = parse_ok("v@[i]");
    if let PureExpr::MethodCall {
        receiver, method, ..
    } = &expr
    {
        assert_eq!(method, "index_logic");
        assert!(matches!(**receiver, PureExpr::View(_)));
    } else {
        panic!("Expected MethodCall, got {expr:?}");
    }
}

#[test]
fn test_parse_index_spanned() {
    let input = "v[0]";
    let regular = parse_ok(input);
    let spanned = parse_spanned_ok(input);
    assert_eq!(regular, spanned.expr);
}
