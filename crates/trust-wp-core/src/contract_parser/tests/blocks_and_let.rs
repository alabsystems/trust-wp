// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

#[test]
fn test_parse_simple_block() {
    // { 42 } → Int(42)
    let expr = parse_ok("{ 42 }");
    assert_eq!(expr, PureExpr::Int(42));
}

#[test]
fn test_parse_block_trailing_expr() {
    // { x + 1 } → BinOp(Var(x), Add, Int(1))
    let expr = parse_ok("{ x + 1 }");
    assert_eq!(
        expr,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".into(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )
    );
}

#[test]
fn test_parse_let_binding() {
    // { let x = 2; x } → Let { var: "x", value: Int(2), body: Var("x") }
    let expr = parse_ok("{ let x = 2; x }");
    assert_eq!(
        expr,
        PureExpr::Let {
            var: "x".into(),
            value: Arc::new(PureExpr::Int(2)),
            body: Arc::new(PureExpr::Var("x".into(), None)),
        }
    );
}

#[test]
fn test_parse_nested_let_bindings() {
    // { let x = 1; let y = 2; x + y }
    let expr = parse_ok("{ let x = 1; let y = 2; x + y }");
    assert_eq!(
        expr,
        PureExpr::Let {
            var: "x".into(),
            value: Arc::new(PureExpr::Int(1)),
            body: Arc::new(PureExpr::Let {
                var: "y".into(),
                value: Arc::new(PureExpr::Int(2)),
                body: Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Var("x".into(), None)),
                    BinOp::Add,
                    Arc::new(PureExpr::Var("y".into(), None)),
                )),
            }),
        }
    );
}

#[test]
fn test_parse_let_underscore() {
    // { let _ = f; 2 } → Int(2) (underscore discards value)
    let expr = parse_ok("{ let _ = f; 2 }");
    assert_eq!(expr, PureExpr::Int(2));
}

#[test]
fn test_parse_expr_stmt_discarded() {
    // { f(); 2 } → Int(2) (expression statement discarded)
    let expr = parse_contract("{ f(); 2 }").unwrap();
    assert_eq!(expr, PureExpr::Int(2));
}

#[test]
fn test_parse_block_with_comment() {
    // { // comment\n x } → Var("x")
    let expr = parse_ok("{ // comment\n x }");
    assert_eq!(expr, PureExpr::Var("x".into(), None));
}

#[test]
fn test_parse_semicolon_trailing_unit() {
    // { x; } → unit (semicolon after trailing expr means unit)
    let expr = parse_ok("{ x; }");
    assert_eq!(
        expr,
        PureExpr::LogicFnCall {
            name: "__trust_wp_tuple0".into(),
            args: vec![],
        }
    );
}

#[test]
fn test_parse_empty_block() {
    // { } → unit
    let expr = parse_ok("{ }");
    assert_eq!(
        expr,
        PureExpr::LogicFnCall {
            name: "__trust_wp_tuple0".into(),
            args: vec![],
        }
    );
}

#[test]
fn test_parse_empty_block_no_space() {
    // {} → unit (no space between braces, from HIR extraction)
    let expr = parse_ok("{}");
    assert_eq!(
        expr,
        PureExpr::LogicFnCall {
            name: "__trust_wp_tuple0".into(),
            args: vec![],
        }
    );
}

#[test]
fn test_parse_if_with_path_call_in_branches() {
    // From bug/1342: if-else with qualified function calls in branches.
    // quote! inserts spaces around :: and ().
    let input = "if fset . is_empty () { FSet :: empty () } else { bar (FSet :: empty ()) }";
    let result = parse_contract(input);
    assert!(
        result.is_ok(),
        "if-else with qualified calls should parse: {result:?}"
    );
}

#[test]
fn test_parse_nested_block() {
    // { let x = 2; ({ let x = 1; x }, x,) }
    // This is a real Creusot pattern from bug/1239.rs
    let expr = parse_contract("{ let x = 2; ({ let x = 1; x }, x,) }").unwrap();
    // Outer: Let(x=2, body=Tuple(inner_block, Var(x)))
    assert!(matches!(expr, PureExpr::Let { ref var, .. } if var == "x"));
}

#[test]
fn test_parse_let_with_complex_value() {
    // { let r = if x > 0 { x } else { 0 - x }; r }
    let expr = parse_ok("{ let r = if x > 0 { x } else { 0 - x }; r }");
    assert!(matches!(expr, PureExpr::Let { ref var, .. } if var == "r"));
    if let PureExpr::Let { value, body, .. } = expr {
        assert!(matches!(*value, PureExpr::Ite(_, _, _)));
        assert_eq!(*body, PureExpr::Var("r".into(), None));
    }
}

#[test]
fn test_parse_block_error_missing_close() {
    let err = parse_contract("{ x").unwrap_err();
    assert!(
        err.message.contains("'}'"),
        "Expected error about missing '}}', got: {}",
        err.message
    );
}

#[test]
fn test_parse_let_error_missing_eq() {
    let err = parse_contract("{ let x; }").unwrap_err();
    assert!(
        err.message.contains("'='"),
        "Expected error about missing '=', got: {}",
        err.message
    );
}

#[test]
fn test_parse_let_error_missing_semicolon() {
    let err = parse_contract("{ let x = 1 }").unwrap_err();
    assert!(
        err.message.contains("';'"),
        "Expected error about missing ';', got: {}",
        err.message
    );
}

#[test]
fn test_parse_let_with_type_annotation() {
    // `let x: u8 = 42; x` — type annotation is consumed and ignored
    let result = parse_contract("{ let x: u8 = 42; x }");
    assert!(
        result.is_ok(),
        "let with type annotation should parse: {result:?}"
    );
    let expr = result.unwrap();
    assert!(matches!(expr, PureExpr::Let { ref var, .. } if var == "x"));
}

#[test]
fn test_parse_let_with_reference_type_annotation() {
    // `let r: &Vec<u8> = v; r@.len()` — complex type with generics
    let result = parse_contract("{ let r: &Vec<u8> = v; r@.len() }");
    assert!(
        result.is_ok(),
        "let with reference type annotation should parse: {result:?}"
    );
}

// --- let-else tests (RFC 3137) ---

/// `let Some(x) = opt else { 0 }; x` desugars to a Match with two arms.
/// First arm binds the rest-of-block under the matched pattern; wildcard
/// carries the else block. Mirrors `if let ... else { ... }` desugaring.
#[test]
fn test_parse_let_else_basic() {
    let expr = parse_ok("{ let Some(x) = opt else { 0 }; x }");
    let PureExpr::Match { scrutinee, arms } = &expr else {
        panic!("expected Match expression, got {expr:?}");
    };
    assert_eq!(scrutinee.as_ref(), &PureExpr::Var("opt".into(), None));
    assert_eq!(arms.len(), 2);
    assert!(
        matches!(&arms[0].pattern, Pattern::Constructor { name, inner: Some(inner) }
            if name == "Some" && matches!(inner.as_ref(), Pattern::Binding(b) if b == "x")),
        "expected Some(x) pattern, got {:?}",
        arms[0].pattern
    );
    // Body of the matched arm is the rest of the block: `x`
    assert_eq!(arms[0].body, PureExpr::Var("x".into(), None));
    // Wildcard arm carries the else-block body
    assert_eq!(arms[1].pattern, Pattern::Wildcard);
    assert_eq!(arms[1].body, PureExpr::Int(0));
}

/// `let Ok(v) = res else { 0 }; v + 1` carries the trailing expression
/// `v + 1` as the matched-arm body.
#[test]
fn test_parse_let_else_carries_trailing_expr() {
    let expr = parse_ok("{ let Ok(v) = res else { 0 }; v + 1 }");
    let PureExpr::Match { scrutinee, arms } = &expr else {
        panic!("expected Match, got {expr:?}");
    };
    assert_eq!(scrutinee.as_ref(), &PureExpr::Var("res".into(), None));
    assert_eq!(arms.len(), 2);
    // First arm: Ok(v) => v + 1
    assert!(matches!(
        &arms[0].pattern,
        Pattern::Constructor { name, inner: Some(_) } if name == "Ok"
    ));
    assert_eq!(
        arms[0].body,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("v".into(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )
    );
    // Wildcard arm: else { 0 }
    assert_eq!(arms[1].pattern, Pattern::Wildcard);
    assert_eq!(arms[1].body, PureExpr::Int(0));
}

/// `let (a, b) = pair else { 0 }; a` — tuple pattern in let-else.
#[test]
fn test_parse_let_else_tuple_pattern() {
    let expr = parse_ok("{ let (a, b) = pair else { 0 }; a }");
    let PureExpr::Match { scrutinee, arms } = &expr else {
        panic!("expected Match, got {expr:?}");
    };
    assert_eq!(scrutinee.as_ref(), &PureExpr::Var("pair".into(), None));
    assert_eq!(arms.len(), 2);
    assert!(matches!(&arms[0].pattern, Pattern::Tuple(elems)
        if elems.len() == 2
            && matches!(&elems[0], Pattern::Binding(s) if s == "a")
            && matches!(&elems[1], Pattern::Binding(s) if s == "b")));
    assert_eq!(arms[0].body, PureExpr::Var("a".into(), None));
    assert_eq!(arms[1].pattern, Pattern::Wildcard);
    assert_eq!(arms[1].body, PureExpr::Int(0));
}

/// `let mut Some(x) = opt else { 0 }; x` — `mut` qualifier is transparent.
#[test]
fn test_parse_let_else_with_mut() {
    let expr = parse_ok("{ let mut x = opt else { 0 }; x }");
    let PureExpr::Match { scrutinee, arms } = &expr else {
        panic!("expected Match, got {expr:?}");
    };
    assert_eq!(scrutinee.as_ref(), &PureExpr::Var("opt".into(), None));
    assert_eq!(arms.len(), 2);
    assert!(matches!(&arms[0].pattern, Pattern::Binding(name) if name == "x"));
    assert_eq!(arms[0].body, PureExpr::Var("x".into(), None));
    assert_eq!(arms[1].pattern, Pattern::Wildcard);
    assert_eq!(arms[1].body, PureExpr::Int(0));
}

/// `let Some(x): Option<i32> = opt else { 0 }; x` — type annotation
/// before `=` is consumed and discarded, let-else still parses.
#[test]
fn test_parse_let_else_with_type_annotation() {
    let expr = parse_ok("{ let x: i32 = opt else { 0 }; x }");
    let PureExpr::Match { arms, .. } = &expr else {
        panic!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
    assert!(matches!(&arms[0].pattern, Pattern::Binding(name) if name == "x"));
    assert_eq!(arms[1].pattern, Pattern::Wildcard);
}

/// `let Some(x) = opt else { panic_block };` followed by trailing
/// expression — verifies the else block can contain a more complex body.
#[test]
fn test_parse_let_else_complex_else_body() {
    let expr = parse_ok("{ let Some(x) = opt else { 1 + 2 }; x }");
    let PureExpr::Match { arms, .. } = &expr else {
        panic!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
    // Else body should be `1 + 2`
    assert_eq!(
        arms[1].body,
        PureExpr::BinOp(
            Arc::new(PureExpr::Int(1)),
            BinOp::Add,
            Arc::new(PureExpr::Int(2)),
        )
    );
}

/// Nested let-else: outer `let Some(x) = opt else { 0 };` followed by
/// inner `let Some(y) = inner else { 1 };` produces nested Match nodes.
#[test]
fn test_parse_let_else_nested() {
    let expr = parse_ok("{ let Some(x) = opt else { 0 }; let Some(y) = inner else { 1 }; x + y }");
    let PureExpr::Match {
        arms: outer_arms, ..
    } = &expr
    else {
        panic!("expected outer Match, got {expr:?}");
    };
    assert_eq!(outer_arms.len(), 2);
    // Outer matched arm body should itself be a Match (inner let-else)
    let PureExpr::Match {
        arms: inner_arms, ..
    } = &outer_arms[0].body
    else {
        panic!(
            "expected inner Match in outer matched arm body, got {:?}",
            outer_arms[0].body
        );
    };
    assert_eq!(inner_arms.len(), 2);
    assert_eq!(inner_arms[1].pattern, Pattern::Wildcard);
    assert_eq!(inner_arms[1].body, PureExpr::Int(1));
}

/// Malformed let-else: missing `{` after `else` — must produce a parse error.
#[test]
fn test_parse_let_else_missing_open_brace_errors() {
    let result = parse_contract("{ let Some(x) = opt else 0; x }");
    assert!(
        result.is_err(),
        "let-else without '{{' after 'else' must error, got: {result:?}"
    );
}

/// Malformed let-else: missing `;` after closing `}` of else block.
#[test]
fn test_parse_let_else_missing_semicolon_errors() {
    let result = parse_contract("{ let Some(x) = opt else { 0 } x }");
    assert!(
        result.is_err(),
        "let-else without ';' after else-block must error, got: {result:?}"
    );
}

/// Malformed let-else: missing `}` to close else block.
#[test]
fn test_parse_let_else_unclosed_block_errors() {
    let result = parse_contract("{ let Some(x) = opt else { 0 ; x }");
    assert!(
        result.is_err(),
        "let-else with unclosed else-block must error, got: {result:?}"
    );
}
