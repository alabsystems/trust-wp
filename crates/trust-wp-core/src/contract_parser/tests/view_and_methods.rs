// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

#[test]
fn test_parse_view_simple() {
    // self@ (view of self)
    let expr = parse_ok("self@");
    assert!(
        matches!(&expr, PureExpr::View(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "self"))
    );
}

#[test]
fn test_parse_view_result() {
    // result@ (view of result)
    let expr = parse_ok("result@");
    assert!(
        matches!(&expr, PureExpr::View(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "result"))
    );
}

#[test]
fn test_parse_view_deref() {
    // (*self)@ (view of dereferenced self)
    let expr = parse_contract("(*self)@").unwrap();
    assert!(matches!(expr, PureExpr::View(inner) if matches!(inner.as_ref(), PureExpr::Deref(_))));
}

#[test]
fn test_parse_unparenthesized_view_deref() {
    // *rc@ (Creusot sugar for (*rc)@)
    let expr = parse_contract("*rc@").unwrap();
    assert!(matches!(
        expr,
        PureExpr::View(inner)
            if matches!(inner.as_ref(), PureExpr::Deref(rc)
                if matches!(rc.as_ref(), PureExpr::Var(name, _) if name == "rc"))
    ));
}

#[test]
fn test_parse_view_final() {
    // (^self)@ (view of final value)
    let expr = parse_contract("(^self)@").unwrap();
    assert!(matches!(expr, PureExpr::View(inner) if matches!(inner.as_ref(), PureExpr::Final(_))));
}

#[test]
fn test_parse_unparenthesized_view_final() {
    // ^x@ (Creusot sugar for (^x)@)
    let expr = parse_contract("^x@").unwrap();
    assert!(matches!(
        expr,
        PureExpr::View(inner)
            if matches!(inner.as_ref(), PureExpr::Final(x)
                if matches!(x.as_ref(), PureExpr::Var(name, _) if name == "x"))
    ));
}

#[test]
fn test_parse_method_call_no_args() {
    // self@.len() (method call with no args)
    let expr = parse_contract("self@.len()").unwrap();
    if let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    {
        assert!(matches!(*receiver, PureExpr::View(_)));
        assert_eq!(method, "len");
        assert!(args.is_empty());
    } else {
        panic!("Expected MethodCall, got {expr:?}");
    }
}

#[test]
fn test_parse_method_call_with_args() {
    // self@.index_logic(i) (method call with one arg)
    let expr = parse_contract("self@.index_logic(i)").unwrap();
    if let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    {
        assert!(matches!(*receiver, PureExpr::View(_)));
        assert_eq!(method, "index_logic");
        assert_eq!(args.len(), 1);
        assert!(matches!(args[0], PureExpr::Var(ref name, _) if name == "i"));
    } else {
        panic!("Expected MethodCall, got {expr:?}");
    }
}

#[test]
fn test_parse_method_call_with_singleton_tuple_arg() {
    let expr = parse_contract("f.postcondition((x,), result)").unwrap();
    if let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    {
        assert!(matches!(*receiver, PureExpr::Var(ref name, _) if name == "f"));
        assert_eq!(method, "postcondition");
        assert_eq!(args.len(), 2);
        assert!(matches!(args[0], PureExpr::Var(ref name, _) if name == "x"));
        assert!(matches!(args[1], PureExpr::Var(ref name, _) if name == "result"));
    } else {
        panic!("Expected MethodCall, got {expr:?}");
    }
}

#[test]
fn test_parse_method_call_with_multi_item_tuple_arg() {
    let expr = parse_contract("f.precondition((x, y))").unwrap();
    if let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    {
        assert!(matches!(*receiver, PureExpr::Var(ref name, _) if name == "f"));
        assert_eq!(method, "precondition");
        assert_eq!(args.len(), 1);
        assert_eq!(
            args[0],
            PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(2),
                args: vec![
                    PureExpr::Var("x".into(), None),
                    PureExpr::Var("y".into(), None)
                ],
            }
        );
    } else {
        panic!("Expected MethodCall, got {expr:?}");
    }
}

#[test]
fn test_parse_method_call_trailing_comma() {
    // Trailing comma in argument list should be accepted
    let expr = parse_contract("self@.push_back(value,)").unwrap();
    if let PureExpr::MethodCall { args, .. } = expr {
        assert_eq!(args.len(), 1);
    } else {
        panic!("Expected MethodCall, got {expr:?}");
    }
}

#[test]
fn test_parse_method_call_multiple_args() {
    // seq.get(i, default) (method call with two args)
    let expr = parse_contract("seq.get(i, default)").unwrap();
    if let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    {
        assert!(matches!(*receiver, PureExpr::Var(ref name, _) if name == "seq"));
        assert_eq!(method, "get");
        assert_eq!(args.len(), 2);
    } else {
        panic!("Expected MethodCall, got {expr:?}");
    }
}

#[test]
fn test_parse_chained_method_calls() {
    // self@.push_back(v).len() (chained method calls)
    let expr = parse_contract("self@.push_back(v).len()").unwrap();
    if let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    {
        assert_eq!(method, "len");
        assert!(args.is_empty());
        // receiver should be the push_back call
        assert!(matches!(*receiver, PureExpr::MethodCall { .. }));
    } else {
        panic!("Expected MethodCall, got {expr:?}");
    }
}

#[test]
fn test_parse_view_len_comparison() {
    // result@.len() == 0 (typical Vec::new postcondition)
    let expr = parse_contract("result@.len() == 0").unwrap();
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Eq, _) if matches!(l.as_ref(), PureExpr::MethodCall { .. })
    ));
}

#[test]
fn test_parse_view_push_back() {
    // (^self)@ == self@.push_back(value)
    let expr = parse_contract("(^self)@ == self@.push_back(value)").unwrap();
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Eq, _) if matches!(l.as_ref(), PureExpr::View(_))
    ));
}

#[test]
fn test_parse_logic_fn_call_with_turbofish() {
    let expr = parse_contract("size_of_logic::<bool>() == 1").unwrap();
    let PureExpr::BinOp(left, BinOp::Eq, right) = &expr else {
        panic!("Expected BinOp(Eq), got {expr:?}");
    };
    assert!(matches!(right.as_ref(), PureExpr::Int(1)));
    let PureExpr::LogicFnCall { name, args } = left.as_ref() else {
        panic!("Expected LogicFnCall, got {left:?}");
    };
    assert_eq!(name, "size_of_logic");
    assert_eq!(args.len(), 1);
    assert!(matches!(
        &args[0],
        PureExpr::LogicFnCall {
            name: wrapper_name,
            args: wrapper_args
        } if wrapper_name == TURBOFISH_ARG_WRAPPER_NAME
            && wrapper_args.len() == 1
            && matches!(
                &wrapper_args[0],
                PureExpr::Var(raw, Some(ExprSort::TypeParam(_))) if raw == "bool"
            )
    ));

    let expr = parse_contract("std::mem::size_of::<u64>() == 8").unwrap();
    let PureExpr::BinOp(left, BinOp::Eq, right) = &expr else {
        panic!("Expected BinOp(Eq), got {expr:?}");
    };
    assert!(matches!(right.as_ref(), PureExpr::Int(8)));
    let PureExpr::LogicFnCall { name, args } = left.as_ref() else {
        panic!("Expected LogicFnCall, got {left:?}");
    };
    assert_eq!(name, "std::mem::size_of");
    assert_eq!(args.len(), 1);
    assert!(matches!(
        &args[0],
        PureExpr::LogicFnCall {
            name: wrapper_name,
            args: wrapper_args
        } if wrapper_name == TURBOFISH_ARG_WRAPPER_NAME
            && wrapper_args.len() == 1
            && matches!(
                &wrapper_args[0],
                PureExpr::Var(raw, Some(ExprSort::TypeParam(_))) if raw == "u64"
            )
    ));
}

#[test]
fn test_parse_logic_fn_call_with_whitespace_path_separator() {
    let expr = parse_contract("Self :: f()").unwrap();
    assert_eq!(
        expr,
        PureExpr::LogicFnCall {
            name: "Self::f".into(),
            args: vec![],
        }
    );
}

#[test]
fn test_parse_field_access_without_parens() {
    // self@.len without parens is now parsed as field access (not an error)
    let expr = parse_ok("self@.len");
    assert_eq!(
        expr,
        PureExpr::LogicFnCall {
            name: "__trust_wp_field_len".into(),
            args: vec![PureExpr::View(Arc::new(PureExpr::Var("self".into(), None)))],
        }
    );
}

#[test]
fn test_parse_method_error_unclosed_parens() {
    // Parser tries to parse an expression after '(' and fails at EOF
    let err = parse_contract("self@.len(").unwrap_err();
    assert_eq!(err.message, "expected expression");
}

#[test]
fn test_parse_method_error_missing_name() {
    let err = parse_contract("self@.()").unwrap_err();
    assert_eq!(err.message, "expected method name or tuple index after '.'");
}

#[test]
fn test_spanned_view() {
    // Verify spanned parsing for view operator
    let spanned = parse_spanned_ok("self@");
    assert!(matches!(spanned.expr, PureExpr::View(_)));
    let span = spanned.span.unwrap();
    assert_eq!(span.start, 0);
    assert_eq!(span.end, 5); // "self@" is 5 chars
}

#[test]
fn test_spanned_method_call() {
    // Verify spanned parsing for method call
    let spanned = parse_contract_spanned("self@.len()").unwrap();
    assert!(matches!(spanned.expr, PureExpr::MethodCall { .. }));
    let span = spanned.span.unwrap();
    assert_eq!(span.start, 0);
    assert_eq!(span.end, 11); // "self@.len()" is 11 chars
}

#[test]
fn test_view_with_arithmetic() {
    // self@.len() - 1 (subtraction with method call result)
    let expr = parse_contract("self@.len() - 1").unwrap();
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Sub, _) if matches!(l.as_ref(), PureExpr::MethodCall { .. })
    ));
}

#[test]
fn test_complex_spec() {
    // index@ < self@.len() && *r == self@.index_logic(index@)
    let expr = parse_contract("index@ < self@.len() && r == self@.index_logic(index@)").unwrap();
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::And, _)));
}
