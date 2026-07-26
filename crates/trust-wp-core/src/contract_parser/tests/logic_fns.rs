// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_parse_logic_fn_call_simple() {
    let expr = parse_contract("max(x, y)").unwrap();
    if let PureExpr::LogicFnCall { name, args } = expr {
        assert_eq!(name, "max");
        assert_eq!(args.len(), 2);
        assert!(matches!(&args[0], PureExpr::Var(n, _) if n == "x"));
        assert!(matches!(&args[1], PureExpr::Var(n, _) if n == "y"));
    } else {
        panic!("Expected LogicFnCall, got {expr:?}");
    }
}

#[test]
fn test_parse_logic_fn_call_nullary() {
    let expr = parse_contract("zero()").unwrap();
    if let PureExpr::LogicFnCall { name, args } = expr {
        assert_eq!(name, "zero");
        assert!(args.is_empty());
    } else {
        panic!("Expected LogicFnCall, got {expr:?}");
    }
}

#[test]
fn test_parse_logic_fn_call_with_literals() {
    let expr = parse_contract("abs(-5)").unwrap();
    if let PureExpr::LogicFnCall { name, args } = expr {
        assert_eq!(name, "abs");
        assert_eq!(args.len(), 1);
        assert!(matches!(&args[0], PureExpr::Int(-5)));
    } else {
        panic!("Expected LogicFnCall, got {expr:?}");
    }
}

#[test]
fn test_parse_logic_fn_call_nested() {
    let expr = parse_contract("max(x, abs(y))").unwrap();
    if let PureExpr::LogicFnCall { name, args } = expr {
        assert_eq!(name, "max");
        assert_eq!(args.len(), 2);
        assert!(matches!(&args[0], PureExpr::Var(n, _) if n == "x"));
        assert!(matches!(&args[1], PureExpr::LogicFnCall { .. }));
    } else {
        panic!("Expected LogicFnCall, got {expr:?}");
    }
}

#[test]
fn test_parse_logic_fn_call_in_expression() {
    let expr = parse_contract("max(x, y) > 0").unwrap();
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Gt, r)
        if matches!(l.as_ref(), PureExpr::LogicFnCall { .. })
        && matches!(r.as_ref(), PureExpr::Int(0))
    ));
}

#[test]
fn test_parse_logic_fn_call_with_complex_args() {
    let expr = parse_contract("max(x + 1, y * 2)").unwrap();
    if let PureExpr::LogicFnCall { name, args } = expr {
        assert_eq!(name, "max");
        assert_eq!(args.len(), 2);
        assert!(matches!(&args[0], PureExpr::BinOp(_, BinOp::Add, _)));
        assert!(matches!(&args[1], PureExpr::BinOp(_, BinOp::Mul, _)));
    } else {
        panic!("Expected LogicFnCall, got {expr:?}");
    }
}

#[test]
fn test_parse_logic_fn_call_trailing_comma() {
    let expr = parse_contract("max(x, y,)").unwrap();
    if let PureExpr::LogicFnCall { name, args } = expr {
        assert_eq!(name, "max");
        assert_eq!(args.len(), 2);
    } else {
        panic!("Expected LogicFnCall, got {expr:?}");
    }
}

#[test]
fn test_parse_logic_fn_call_spanned() {
    let spanned = parse_contract_spanned("max(a, b)").unwrap();
    if let PureExpr::LogicFnCall { name, .. } = spanned.expr {
        assert_eq!(name, "max");
        let span = spanned.span.expect("Expected span");
        assert_eq!(span.start, 0);
        assert_eq!(span.end, 9);
    } else {
        panic!("Expected LogicFnCall, got {:?}", spanned.expr);
    }
}

#[test]
fn test_parse_logic_fn_call_qualified_path() {
    // Qualified paths like crate::specs::max should work
    let expr = parse_contract("crate::specs::max(a, b)").unwrap();
    if let PureExpr::LogicFnCall { name, args } = expr {
        assert_eq!(name, "crate::specs::max");
        assert_eq!(args.len(), 2);
    } else {
        panic!("Expected LogicFnCall with qualified path, got {expr:?}");
    }
}

#[test]
fn test_parse_logic_fn_call_unary() {
    // Single argument function call
    let expr = parse_contract("abs(x)").unwrap();
    if let PureExpr::LogicFnCall { name, args } = expr {
        assert_eq!(name, "abs");
        assert_eq!(args.len(), 1);
        assert!(matches!(&args[0], PureExpr::Var(n, _) if n == "x"));
    } else {
        panic!("Expected LogicFnCall, got {expr:?}");
    }
}

#[test]
fn test_parse_logic_fn_call_whitespace_before_paren() {
    // Whitespace before ( is allowed (unlike Rust syntax)
    // This is intentional for contract readability
    let expr = parse_contract("max (x, y)").unwrap();
    if let PureExpr::LogicFnCall { name, args } = expr {
        assert_eq!(name, "max");
        assert_eq!(args.len(), 2);
    } else {
        panic!("Expected LogicFnCall with space before (, got {expr:?}");
    }
}

#[test]
fn test_parse_logic_fn_call_with_const_turbofish_preserves_wrapper_arg() {
    let expr = parse_contract("add_one_logic::<M>()").unwrap();
    if let PureExpr::LogicFnCall { name, args } = expr {
        assert_eq!(name, "add_one_logic");
        assert_eq!(args.len(), 1);
        match &args[0] {
            PureExpr::LogicFnCall {
                name: wrapper_name,
                args: wrapper_args,
            } => {
                assert_eq!(wrapper_name, TURBOFISH_ARG_WRAPPER_NAME);
                assert_eq!(wrapper_args.len(), 1);
                assert!(matches!(
                    &wrapper_args[0],
                    PureExpr::Var(raw, Some(ExprSort::TypeParam(_))) if raw == "M"
                ));
            }
            other => panic!("expected turbofish wrapper arg, got {other:?}"),
        }
    } else {
        panic!("Expected LogicFnCall, got {expr:?}");
    }
}

#[test]
fn test_parse_logic_fn_call_with_const_turbofish_spanned_matches_unspanned() {
    let expr = parse_contract("add_one_logic::<M>()").unwrap();
    let spanned = parse_contract_spanned("add_one_logic::<M>()").unwrap();
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_parse_method_call_on_qualified_function_item() {
    let expr = parse_contract("core::default::Default::default.postcondition((), result)").unwrap();

    if let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    {
        assert!(
            matches!(&*receiver, PureExpr::Var(path, _) if path == "core::default::Default::default")
        );
        assert_eq!(method, "postcondition");
        assert_eq!(args.len(), 2);
        assert!(matches!(&args[1], PureExpr::Var(name, _) if name == "result"));
    } else {
        panic!("Expected MethodCall, got {expr:?}");
    }
}
