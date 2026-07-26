// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// =============================================================================
// Creusot resolve/deref pattern tests (#1196)
// =============================================================================

#[test]
fn test_parse_final_double_deref_view() {
    // (^**by)@ — Final(Deref(Deref(Var("by")))), then View
    // From closures/09_fnonce_resolve.rs: proof_assert!((^**by)@ == 1)
    let result = parse_contract("(^**by)@");
    assert!(
        result.is_ok(),
        "Failed to parse (^**by)@: {:?}",
        result.as_ref().err()
    );
    let expr = result.unwrap();
    // Should be View(Final(Deref(Deref(Var("by")))))
    match &expr {
        PureExpr::View(inner) => match inner.as_ref() {
            PureExpr::Final(inner2) => match inner2.as_ref() {
                PureExpr::Deref(inner3) => match inner3.as_ref() {
                    PureExpr::Deref(inner4) => match inner4.as_ref() {
                        PureExpr::Var(name, _) => assert_eq!(name, "by"),
                        other => panic!("expected Var(by), got: {other:?}"),
                    },
                    other => panic!("expected Deref, got: {other:?}"),
                },
                other => panic!("expected Deref, got: {other:?}"),
            },
            other => panic!("expected Final, got: {other:?}"),
        },
        other => panic!("expected View, got: {other:?}"),
    }
}

#[test]
fn test_parse_final_double_deref_view_eq() {
    // (^**by)@ == 1 — full expression from 09_fnonce_resolve.rs
    let result = parse_contract("(^**by)@ == 1");
    assert!(
        result.is_ok(),
        "Failed to parse (^**by)@ == 1: {:?}",
        result.as_ref().err()
    );
    let expr = result.unwrap();
    assert!(
        matches!(expr, PureExpr::BinOp(_, BinOp::Eq, _)),
        "expected Eq comparison, got: {expr:?}"
    );
}

#[test]
fn test_parse_final_deref_view() {
    // (^*bx)@ — Final(Deref(Var("bx"))), then View
    let result = parse_contract("(^*bx)@");
    assert!(
        result.is_ok(),
        "Failed to parse (^*bx)@: {:?}",
        result.as_ref().err()
    );
    let expr = result.unwrap();
    // Should be View(Final(Deref(Var("bx"))))
    assert!(
        matches!(&expr, PureExpr::View(inner) if matches!(inner.as_ref(), PureExpr::Final(_))),
        "expected View(Final(...)), got: {expr:?}"
    );
}

#[test]
fn test_parse_postcondition_once_implies_resolve() {
    // f.postcondition_once((), ()) ==> resolve(*xx)
    // From closures/14_move_resolve.rs
    let result = parse_contract("f.postcondition_once((), ()) ==> resolve(*xx)");
    assert!(
        result.is_ok(),
        "Failed to parse postcondition_once ==> resolve: {:?}",
        result.as_ref().err()
    );
    let expr = result.unwrap();
    match &expr {
        PureExpr::BinOp(_, BinOp::Implies, _) => {} // expected
        other => panic!("expected Implies, got: {other:?}"),
    }
}

#[test]
fn test_parse_resolve_with_deref() {
    // resolve(*xx) — resolve as function call with deref argument
    let result = parse_contract("resolve(*xx)");
    assert!(
        result.is_ok(),
        "Failed to parse resolve(*xx): {:?}",
        result.as_ref().err()
    );
    match result.unwrap() {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(name, "resolve");
            assert_eq!(args.len(), 1);
            match &args[0] {
                PureExpr::Deref(inner) => match inner.as_ref() {
                    PureExpr::Var(name, _) => assert_eq!(name, "xx"),
                    other => panic!("expected Var(xx), got: {other:?}"),
                },
                other => panic!("expected Deref, got: {other:?}"),
            }
        }
        other => panic!("expected LogicFnCall, got: {other:?}"),
    }
}

// --- Hex integer literal tests (#1513) ---

#[test]
fn test_parse_hex_integer() {
    assert_eq!(parse_ok("0xFF"), PureExpr::Int(255));
    assert_eq!(parse_ok("0x0"), PureExpr::Int(0));
    assert_eq!(parse_ok("0xC3"), PureExpr::Int(195));
    assert_eq!(parse_ok("0x83"), PureExpr::Int(131));
}

#[test]
fn test_parse_hex_integer_with_suffix() {
    assert_eq!(parse_ok("0xC3u8"), PureExpr::Int(195));
    assert_eq!(parse_ok("0x83u8"), PureExpr::Int(131));
    assert_eq!(parse_ok("0xFFi32"), PureExpr::Int(255));
}

#[test]
fn test_parse_hex_integer_case_insensitive() {
    assert_eq!(parse_ok("0XFF"), PureExpr::Int(255));
    assert_eq!(parse_ok("0xABCDEF"), PureExpr::Int(0x00AB_CDEF));
    assert_eq!(parse_ok("0xabcdef"), PureExpr::Int(0x00ab_cdef));
}

#[test]
fn test_parse_hex_in_expression() {
    // 0xC3u8 == 195 should parse as BinOp(Int(195), Eq, Int(195))
    let result = parse_ok("0xC3u8 == 195");
    assert!(
        matches!(&result, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if **lhs == PureExpr::Int(195) && **rhs == PureExpr::Int(195)),
        "expected BinOp(Eq) with Int(195) on both sides, got: {result:?}"
    );
}

// --- Character literal tests (#1513) ---

#[test]
fn test_parse_char_literal_ascii() {
    assert_eq!(parse_ok("'A'"), PureExpr::Int(65));
    assert_eq!(parse_ok("'a'"), PureExpr::Int(97));
    assert_eq!(parse_ok("'0'"), PureExpr::Int(48));
}

#[test]
fn test_parse_char_literal_escape() {
    assert_eq!(parse_ok("'\\n'"), PureExpr::Int(10));
    assert_eq!(parse_ok("'\\t'"), PureExpr::Int(9));
    assert_eq!(parse_ok("'\\r'"), PureExpr::Int(13));
    assert_eq!(parse_ok("'\\0'"), PureExpr::Int(0));
    assert_eq!(parse_ok("'\\\\'"), PureExpr::Int(92));
}

#[test]
fn test_parse_char_literal_unicode() {
    // 'Ã' is U+00C3 = 195
    assert_eq!(parse_ok("'Ã'"), PureExpr::Int(0xC3));
}

#[test]
fn test_parse_char_literal_in_expression() {
    // 'A' == 65 should parse correctly
    let result = parse_ok("'A' == 65");
    assert!(
        matches!(&result, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if **lhs == PureExpr::Int(65) && **rhs == PureExpr::Int(65)),
        "expected BinOp(Eq) with Int(65) on both sides, got: {result:?}"
    );
}

#[test]
fn test_parse_string_literal_is_rejected() {
    let err = parse_contract("result == \"a\"").unwrap_err();
    assert_eq!(err.message, "expected expression");
}

// ── Range indexing tests (#1513) ──

#[test]
fn test_parse_range_exclusive() {
    // s[0..1] → s.subsequence(0, 1)
    let result = parse_ok("s[0..1]");
    assert_eq!(
        result,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
            method: "subsequence".to_string(),
            args: vec![PureExpr::Int(0), PureExpr::Int(1)],
        }
    );
}

#[test]
fn test_parse_range_inclusive() {
    // s[0..=0] → s.subsequence(0, 0 + 1)
    let result = parse_ok("s[0..=0]");
    assert_eq!(
        result,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
            method: "subsequence".to_string(),
            args: vec![
                PureExpr::Int(0),
                PureExpr::BinOp(
                    Arc::new(PureExpr::Int(0)),
                    BinOp::Add,
                    Arc::new(PureExpr::Int(1)),
                ),
            ],
        }
    );
}

#[test]
fn test_parse_range_from() {
    // s[0..] → s.subsequence(0, s.len())
    let result = parse_ok("s[0..]");
    assert_eq!(
        result,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
            method: "subsequence".to_string(),
            args: vec![
                PureExpr::Int(0),
                PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
                    method: "len".to_string(),
                    args: vec![],
                },
            ],
        }
    );
}

#[test]
fn test_parse_range_to() {
    // s[..0] → s.subsequence(0, 0)
    let result = parse_ok("s[..0]");
    assert_eq!(
        result,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
            method: "subsequence".to_string(),
            args: vec![PureExpr::Int(0), PureExpr::Int(0)],
        }
    );
}

#[test]
fn test_parse_range_to_inclusive() {
    // s[..=0] → s.subsequence(0, 0 + 1)
    let result = parse_ok("s[..=0]");
    assert_eq!(
        result,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
            method: "subsequence".to_string(),
            args: vec![
                PureExpr::Int(0),
                PureExpr::BinOp(
                    Arc::new(PureExpr::Int(0)),
                    BinOp::Add,
                    Arc::new(PureExpr::Int(1)),
                ),
            ],
        }
    );
}

#[test]
fn test_parse_range_full() {
    // s[..] → s.subsequence(0, s.len())
    let result = parse_ok("s[..]");
    assert_eq!(
        result,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
            method: "subsequence".to_string(),
            args: vec![
                PureExpr::Int(0),
                PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
                    method: "len".to_string(),
                    args: vec![],
                },
            ],
        }
    );
}

#[test]
fn test_parse_range_plain_index_still_works() {
    // s[0] → s.index_logic(0) (unchanged behavior)
    let result = parse_ok("s[0]");
    assert_eq!(
        result,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("s".to_string(), None)),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Int(0)],
        }
    );
}

#[test]
fn test_parse_range_in_ensures_clause() {
    // s[0..1].len() == 1 — mimics cc/seq.rs contract
    let result = parse_contract("s[0..1].len() == 1").unwrap();
    assert!(
        matches!(&result, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(&**lhs, PureExpr::MethodCall { method, .. } if method == "len")
            && **rhs == PureExpr::Int(1)),
        "expected s[0..1].len() == 1, got: {result:?}"
    );
}

#[test]
fn test_parse_range_full_equality() {
    // s[..] == s — full range should equal the original
    let result = parse_ok("s[..] == s");
    assert!(
        matches!(&result, PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(&**lhs, PureExpr::MethodCall { method, .. } if method == "subsequence")
            && **rhs == PureExpr::Var("s".to_string(), None)),
        "expected s[..] == s, got: {result:?}"
    );
}

// ── Destructuring let-binding tests (#1513) ──

#[test]
fn test_parse_let_destructure_constructor() {
    // let List(_, ls) = self; ls
    // Desugars to: let ls = __trust_wp_tuple_get_1(self); ls
    let result = parse_contract_body("let List(_, ls) = self; ls").unwrap();
    assert_eq!(
        result,
        PureExpr::Let {
            var: "ls".to_string(),
            value: Arc::new(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(1),
                args: vec![PureExpr::Var("self".to_string(), None)],
            }),
            body: Arc::new(PureExpr::Var("ls".to_string(), None)),
        }
    );
}

#[test]
fn test_parse_let_destructure_two_bindings() {
    // let List(i, ls) = self; i
    // Desugars to:
    //   let i = __trust_wp_tuple_get_0(self);
    //   let ls = __trust_wp_tuple_get_1(self);
    //   i
    let result = parse_contract_body("let List(i, ls) = self; i").unwrap();
    assert_eq!(
        result,
        PureExpr::Let {
            var: "i".to_string(),
            value: Arc::new(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(0),
                args: vec![PureExpr::Var("self".to_string(), None)],
            }),
            body: Arc::new(PureExpr::Let {
                var: "ls".to_string(),
                value: Arc::new(PureExpr::LogicFnCall {
                    name: tuple_field_logic_fn_name(1),
                    args: vec![PureExpr::Var("self".to_string(), None)],
                }),
                body: Arc::new(PureExpr::Var("i".to_string(), None)),
            }),
        }
    );
}

#[test]
fn test_parse_let_destructure_in_block() {
    // Block form: { let List(_, ls) = self; ls }
    let result = parse_contract("{ let List(_, ls) = self; ls }").unwrap();
    assert_eq!(
        result,
        PureExpr::Let {
            var: "ls".to_string(),
            value: Arc::new(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(1),
                args: vec![PureExpr::Var("self".to_string(), None)],
            }),
            body: Arc::new(PureExpr::Var("ls".to_string(), None)),
        }
    );
}

#[test]
fn test_parse_let_mut_binding() {
    // `let mut x = 0; x` — mut is transparent in contract logic
    let result = parse_body_ok("let mut x = 0; x");
    assert_eq!(
        result,
        PureExpr::Let {
            var: "x".to_string(),
            value: Arc::new(PureExpr::Int(0)),
            body: Arc::new(PureExpr::Var("x".to_string(), None)),
        }
    );
}

#[test]
fn test_parse_let_tuple_destructure() {
    // let (a, b) = pair; a
    let result = parse_contract_body("let (a, b) = pair; a").unwrap();
    assert_eq!(
        result,
        PureExpr::Let {
            var: "a".to_string(),
            value: Arc::new(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(0),
                args: vec![PureExpr::Var("pair".to_string(), None)],
            }),
            body: Arc::new(PureExpr::Let {
                var: "b".to_string(),
                value: Arc::new(PureExpr::LogicFnCall {
                    name: tuple_field_logic_fn_name(1),
                    args: vec![PureExpr::Var("pair".to_string(), None)],
                }),
                body: Arc::new(PureExpr::Var("a".to_string(), None)),
            }),
        }
    );
}

#[test]
fn test_parse_let_destructure_with_body_expr() {
    // let List(_, ls) = self; 1 + match ls { ... }
    // Mimics list_index_mut.rs len() logic function
    let result = parse_contract_body(
        "let List(_, ls) = self; 1 + match ls { Some(ls) => ls.len(), None => 0 }",
    )
    .unwrap();
    // Check the outermost structure: Let { var: "ls", value: field1(self), body: 1 + match }
    assert!(
        matches!(&result, PureExpr::Let { var, value, body }
            if var == "ls"
            && matches!(&**value, PureExpr::LogicFnCall { name, args }
                if name == &tuple_field_logic_fn_name(1)
                && args.len() == 1)
            && matches!(&**body, PureExpr::BinOp(_, BinOp::Add, _))),
        "expected let ls = field1(self); 1 + match ..., got: {result:?}"
    );
}

// ====================================================================
// ref / ref mut patterns (#1513)
// ====================================================================

#[test]
fn test_pattern_ref_binding() {
    // match x { Some(ref v) => v, None => 0 }
    let result = parse_contract("match x { Some(ref v) => v, None => 0 }").unwrap();
    match &result {
        PureExpr::Match { arms, .. } => {
            // The ref qualifier is consumed; `ref v` becomes Binding("v")
            assert!(
                matches!(&arms[0].pattern, Pattern::Constructor { name, inner: Some(inner) }
                    if name == "Some"
                    && matches!(&**inner, Pattern::Binding(n) if n == "v")),
                "expected Some(v) pattern, got: {:?}",
                arms[0].pattern
            );
        }
        _ => unreachable!("expected Match, got: {result:?}"),
    }
}

#[test]
fn test_pattern_ref_mut_binding() {
    // match x { Some(ref mut v) => v, None => 0 }
    let result = parse_contract("match x { Some(ref mut v) => v, None => 0 }").unwrap();
    match &result {
        PureExpr::Match { arms, .. } => {
            assert!(
                matches!(&arms[0].pattern, Pattern::Constructor { name, inner: Some(inner) }
                    if name == "Some"
                    && matches!(&**inner, Pattern::Binding(n) if n == "v")),
                "expected Some(v) pattern after ref mut, got: {:?}",
                arms[0].pattern
            );
        }
        _ => unreachable!("expected Match, got: {result:?}"),
    }
}

#[test]
fn test_pattern_mut_binding() {
    // match x { Some(mut v) => v, None => 0 }
    let result = parse_contract("match x { Some(mut v) => v, None => 0 }").unwrap();
    match &result {
        PureExpr::Match { arms, .. } => {
            assert!(
                matches!(&arms[0].pattern, Pattern::Constructor { name, inner: Some(inner) }
                    if name == "Some"
                    && matches!(&**inner, Pattern::Binding(n) if n == "v")),
                "expected Some(v) pattern after mut, got: {:?}",
                arms[0].pattern
            );
        }
        _ => unreachable!("expected Match, got: {result:?}"),
    }
}

// ====================================================================
// .. rest-pattern in struct patterns (#1513)
// ====================================================================

#[test]
fn test_struct_pattern_rest() {
    // match x { B { field1: true, .. } => true, _ => false }
    let result = parse_ok("match x { B { field1 : true, .. } => true, _ => false }");
    match &result {
        PureExpr::Match { arms, .. } => {
            // B { field1: true, .. } → Constructor { name: "B", inner: Literal(true) }
            assert!(
                matches!(&arms[0].pattern, Pattern::Constructor { name, inner: Some(_) }
                    if name == "B"),
                "expected B {{ .. }} constructor, got: {:?}",
                arms[0].pattern
            );
        }
        _ => unreachable!("expected Match, got: {result:?}"),
    }
}

#[test]
fn test_struct_pattern_only_rest() {
    // match x { A { .. } => 1, _ => 0 }
    let result = parse_ok("match x { A { .. } => 1, _ => 0 }");
    match &result {
        PureExpr::Match { arms, .. } => {
            assert!(
                matches!(&arms[0].pattern, Pattern::Constructor { name, inner: None }
                    if name == "A"),
                "expected A {{ .. }} constructor with no fields, got: {:?}",
                arms[0].pattern
            );
        }
        _ => unreachable!("expected Match, got: {result:?}"),
    }
}

// ====================================================================
// ..base struct update syntax in struct literals (#1513)
// ====================================================================

#[test]
fn test_struct_literal_update_syntax() {
    // A { l, ..self } — field `l` shorthand + base `self`
    let result = parse_body_ok("A { l, ..self }");
    match &result {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(name, "A");
            assert_eq!(args.len(), 2);
            assert_eq!(args[0], PureExpr::Var("l".to_string(), None));
            assert_eq!(args[1], PureExpr::Var("self".to_string(), None));
        }
        _ => unreachable!("expected LogicFnCall, got: {result:?}"),
    }
}

#[test]
fn test_struct_literal_update_with_field_expr() {
    // Point { x: 1, ..origin }
    let result = parse_body_ok("Point { x : 1, ..origin }");
    match &result {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(name, "Point");
            assert_eq!(args.len(), 2);
            assert_eq!(args[0], PureExpr::Int(1));
            assert_eq!(args[1], PureExpr::Var("origin".to_string(), None));
        }
        _ => unreachable!("expected LogicFnCall, got: {result:?}"),
    }
}

// ====================================================================
// Destructuring closure parameters (#1513)
// ====================================================================

#[test]
fn test_closure_destructuring_tuple_param() {
    // |(x, y)| x + y == 0
    let result = parse_contract("|(x, y)| x + y == 0").unwrap();
    match &result {
        PureExpr::Closure { params, .. } => {
            assert_eq!(params.len(), 2, "expected 2 params from |(x, y)|");
            assert_eq!(params[0].0, "x");
            assert_eq!(params[1].0, "y");
        }
        _ => unreachable!("expected Closure, got: {result:?}"),
    }
}

#[test]
fn test_closure_destructuring_nested() {
    // |(a, (b, c))| a
    let result = parse_contract("|(a, (b, c))| a").unwrap();
    match &result {
        PureExpr::Closure { params, .. } => {
            assert_eq!(params.len(), 3, "expected 3 params from |(a, (b, c))|");
            assert_eq!(params[0].0, "a");
            assert_eq!(params[1].0, "b");
            assert_eq!(params[2].0, "c");
        }
        _ => unreachable!("expected Closure, got: {result:?}"),
    }
}

// ====================================================================
// use statement skip in block bodies (#1513)
// ====================================================================

#[test]
fn test_block_body_use_statement_skipped() {
    // use crate::B; match x { B { field1: true, .. } => true, _ => false }
    let result = parse_contract_body(
        "use crate::B; match x { B { field1 : true, .. } => true, _ => false }",
    )
    .unwrap();
    assert!(
        matches!(&result, PureExpr::Match { .. }),
        "expected match expression after skipping `use`, got: {result:?}"
    );
}

#[test]
fn test_block_body_multiple_use_statements() {
    // use crate::A; use crate::B; 42
    let result = parse_body_ok("use crate::A; use crate::B; 42");
    assert_eq!(result, PureExpr::Int(42));
}

// ====================================================================
// .. rest-pattern in tuple-struct patterns
// ====================================================================

#[test]
fn test_tuple_struct_pattern_trailing_rest() {
    // match x { Foo(a, ..) => a, _ => 0 }
    // Trailing `..` is consumed; only `a` becomes a binding.
    let result = parse_ok("match x { Foo(a, ..) => a, _ => 0 }");
    match &result {
        PureExpr::Match { arms, .. } => {
            assert!(
                matches!(&arms[0].pattern, Pattern::Constructor { name, inner: Some(inner) }
                    if name == "Foo"
                    && matches!(&**inner, Pattern::Binding(n) if n == "a")),
                "expected Foo(a) constructor after rest, got: {:?}",
                arms[0].pattern
            );
        }
        _ => unreachable!("expected Match, got: {result:?}"),
    }
}

#[test]
fn test_tuple_struct_pattern_only_rest() {
    // match x { Foo(..) => 1, _ => 0 }
    // `..` alone produces a unit constructor (no captured fields).
    let result = parse_ok("match x { Foo(..) => 1, _ => 0 }");
    match &result {
        PureExpr::Match { arms, .. } => {
            assert!(
                matches!(&arms[0].pattern, Pattern::Constructor { name, inner: None }
                    if name == "Foo"),
                "expected Foo(..) as unit constructor, got: {:?}",
                arms[0].pattern
            );
        }
        _ => unreachable!("expected Match, got: {result:?}"),
    }
}

#[test]
fn test_tuple_struct_pattern_leading_rest() {
    // match x { Foo(.., last) => last, _ => 0 }
    let result = parse_ok("match x { Foo(.., last) => last, _ => 0 }");
    match &result {
        PureExpr::Match { arms, .. } => {
            assert!(
                matches!(&arms[0].pattern, Pattern::Constructor { name, inner: Some(inner) }
                    if name == "Foo"
                    && matches!(&**inner, Pattern::Binding(n) if n == "last")),
                "expected Foo(last) after leading rest, got: {:?}",
                arms[0].pattern
            );
        }
        _ => unreachable!("expected Match, got: {result:?}"),
    }
}

#[test]
fn test_tuple_struct_pattern_rest_between_bindings() {
    // match x { Foo(a, .., b) => a, _ => 0 }
    // Two surviving bindings collapse to Pattern::Tuple([a, b]).
    let result = parse_ok("match x { Foo(a, .., b) => a, _ => 0 }");
    match &result {
        PureExpr::Match { arms, .. } => {
            assert_eq!(
                arms[0].pattern,
                Pattern::Constructor {
                    name: "Foo".into(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("a".into()),
                        Pattern::Binding("b".into()),
                    ]))),
                },
                "expected Foo(a, b) tuple after interior rest"
            );
        }
        _ => unreachable!("expected Match, got: {result:?}"),
    }
}

#[test]
fn test_tuple_struct_pattern_multi_arg_with_trailing_rest() {
    // match x { Cons(a, b, ..) => a, _ => 0 }
    let result = parse_ok("match x { Cons(a, b, ..) => a, _ => 0 }");
    match &result {
        PureExpr::Match { arms, .. } => {
            assert_eq!(
                arms[0].pattern,
                Pattern::Constructor {
                    name: "Cons".into(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("a".into()),
                        Pattern::Binding("b".into()),
                    ]))),
                },
                "expected Cons(a, b) with trailing rest dropped"
            );
        }
        _ => unreachable!("expected Match, got: {result:?}"),
    }
}

#[test]
fn test_tuple_struct_pattern_rest_in_let_binding() {
    // let Foo(a, ..) = x; a
    // Rest pattern in let-binding desugars through the same parse_pattern path.
    // The single surviving binding `a` is extracted (either via a constructor
    // projection let-chain or a match, depending on desugaring). All that
    // matters here is that parsing succeeded and `a` is referenced in the body.
    let result = parse_body_ok("let Foo(a, ..) = x; a");
    let dump = format!("{result:?}");
    assert!(
        dump.contains("\"a\""),
        "expected `a` to be bound after let Foo(a, ..), got: {dump}"
    );
}

#[test]
fn test_tuple_struct_pattern_unclosed_after_rest_errors() {
    // Missing closing paren after `..` must surface a parser error, not silently
    // succeed. Use the underlying parse_contract API to inspect the error.
    let err = parse_contract("match x { Foo(a, .. => a, _ => 0 }");
    assert!(
        err.is_err(),
        "expected parse error for unclosed Foo(a, ..), got Ok: {err:?}"
    );
}
