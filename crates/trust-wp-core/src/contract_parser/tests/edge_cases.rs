// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// --- Error tests ---

#[test]
fn test_error_empty_input() {
    let err = parse_contract("").unwrap_err();
    assert_eq!(err.message, "expected expression");
    assert_eq!(err.position, 0);
}

#[test]
fn test_error_whitespace_only() {
    let err = parse_contract("   ").unwrap_err();
    assert_eq!(err.message, "expected expression");
}

#[test]
fn test_error_unmatched_open_paren() {
    let err = parse_contract("(x > 0").unwrap_err();
    assert_eq!(err.message, "expected ')'");
}

#[test]
fn test_error_unmatched_close_paren() {
    let err = parse_contract("x > 0)").unwrap_err();
    assert_eq!(err.message, "unexpected characters after expression");
}

#[test]
fn test_error_old_missing_open_paren() {
    // After #967 fix: `old` without `(` is treated as an identifier,
    // so `old x` parses `old` as Var, then trailing `x` is unexpected.
    let err = parse_contract("old x").unwrap_err();
    assert_eq!(err.message, "unexpected characters after expression");
}

#[test]
fn test_error_old_missing_close_paren() {
    let err = parse_contract("old(x").unwrap_err();
    assert_eq!(err.message, "expected ')' after old expression");
}

#[test]
fn test_error_trailing_operator() {
    let err = parse_contract("x +").unwrap_err();
    assert_eq!(err.message, "expected expression");
}

#[test]
fn test_error_leading_operator() {
    // This tests the backtracking behavior for negation
    // "+ x" should fail as + is binary, not unary
    let err = parse_contract("+ x").unwrap_err();
    assert_eq!(err.message, "expected expression");
}

#[test]
fn test_negative_with_space_backtracking() {
    // "- x" (negative with space) should parse as subtraction from nothing = error
    // or unary negation depending on implementation
    // Current behavior: treated as unary negation after backtracking
    let result = parse_contract("- x");
    // If unary negation is supported without prefix expression, this parses
    // If not, it errors. Test documents current behavior.
    assert!(
        result.is_ok(),
        "- x should parse as unary negation: {:?}",
        result.as_ref().err()
    );
    let expr = result.unwrap();
    assert!(matches!(expr, PureExpr::UnOp(UnOp::Neg, _)));
}

#[test]
fn test_integer_overflow_i64() {
    // i64::MAX + 1 = 9223372036854775808
    // This exceeds i64 range and should produce a clear overflow error
    let err = parse_contract("9223372036854775808").unwrap_err();
    assert!(
        err.message.contains("overflows i64"),
        "expected overflow error, got: {}",
        err.message
    );
}

#[test]
fn test_integer_negative_overflow() {
    // i64::MIN - 1 = -9223372036854775809
    // This exceeds i64 range and should produce a clear overflow error
    let err = parse_contract("-9223372036854775809").unwrap_err();
    assert!(
        err.message.contains("overflows i64"),
        "expected overflow error, got: {}",
        err.message
    );
}

#[test]
fn test_nested_unmatched_parens() {
    let err = parse_contract("((x + y)").unwrap_err();
    assert_eq!(err.message, "expected ')'");
}

#[test]
fn test_missing_operand_binary() {
    let err = parse_contract("x && ").unwrap_err();
    assert_eq!(err.message, "expected expression");
}

#[test]
fn test_double_operator() {
    // "x ++ y" - second + requires operand
    let err = parse_contract("x ++ y").unwrap_err();
    assert_eq!(err.message, "expected expression");
}

// --- Edge case tests ---

#[test]
fn test_parse_nested_deref() {
    // *(*v) - nested dereference parses successfully
    // Note: encoder may reject this but parser accepts it
    let expr = parse_contract("*(*v)").unwrap();
    assert!(matches!(
        expr,
        PureExpr::Deref(d1)
        if matches!(d1.as_ref(), PureExpr::Deref(d2)
            if matches!(d2.as_ref(), PureExpr::Var(name, _) if name == "v"))
    ));
}

#[test]
fn test_parse_multi_segment_path() {
    // std::i32::MAX - multi-segment qualified path
    let expr = parse_ok("std::i32::MAX");
    assert_eq!(expr, PureExpr::Var("std::i32::MAX".into(), None));
}

#[test]
fn test_parse_crate_qualified_path() {
    // crate::Foo::BAR - crate-qualified constant
    let expr = parse_ok("crate::Foo::BAR");
    assert_eq!(expr, PureExpr::Var("crate::Foo::BAR".into(), None));
}

#[test]
fn test_parse_multiple_derefs_in_arithmetic() {
    // *v + *w - two derefs in expression
    let expr = parse_ok("*v + *w");
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Add, r)
        if matches!(l.as_ref(), PureExpr::Deref(_))
        && matches!(r.as_ref(), PureExpr::Deref(_))
    ));
}

#[test]
fn test_parse_mixed_old_final_deref() {
    // ^v == old(*v) + old(*w) - mixed operators
    let expr = parse_contract("^v == old(*v) + old(*w)").unwrap();
    if let PureExpr::BinOp(left, BinOp::Eq, right) = &expr {
        assert!(matches!(**left, PureExpr::Final(_)));
        // right is: old(*v) + old(*w)
        if let PureExpr::BinOp(r_left, BinOp::Add, r_right) = &**right {
            assert!(
                matches!(r_left.as_ref(), PureExpr::Old(inner) if matches!(inner.as_ref(), PureExpr::Deref(_)))
            );
            assert!(
                matches!(r_right.as_ref(), PureExpr::Old(inner) if matches!(inner.as_ref(), PureExpr::Deref(_)))
            );
        } else {
            panic!("Expected BinOp(Add) on right, got {right:?}");
        }
    } else {
        panic!("Expected BinOp(Eq), got {expr:?}");
    }
}

#[test]
fn test_parse_deref_chain() {
    // *(*(*v)) - triple nested deref
    let expr = parse_contract("*(*(*v))").unwrap();
    assert!(matches!(
        expr,
        PureExpr::Deref(d1)
        if matches!(d1.as_ref(), PureExpr::Deref(d2)
            if matches!(d2.as_ref(), PureExpr::Deref(d3)
                if matches!(d3.as_ref(), PureExpr::Var(_, _))))
    ));
}

#[test]
fn test_parse_old_of_deref_chain() {
    // old(*(*v)) - old of nested deref
    let expr = parse_contract("old(*(*v))").unwrap();
    assert!(matches!(
        expr,
        PureExpr::Old(d1)
        if matches!(d1.as_ref(), PureExpr::Deref(d2)
            if matches!(d2.as_ref(), PureExpr::Deref(d3)
                if matches!(d3.as_ref(), PureExpr::Var(_, _))))
    ));
}

#[test]
fn test_parse_final_arithmetic() {
    // ^v - old(*v) - difference between final and initial
    let expr = parse_contract("^v - old(*v)").unwrap();
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Sub, r)
        if matches!(l.as_ref(), PureExpr::Final(_))
        && matches!(r.as_ref(), PureExpr::Old(_))
    ));
}

#[test]
fn test_parse_deref_in_comparison_chain() {
    // *v > 0 && *w < 10 - deref in comparison chain
    let expr = parse_ok("*v > 0 && *w < 10");
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::And, _)));
}

#[test]
fn test_parse_complex_view_method_deref() {
    // (*self)@.len() - deref then view then method
    let expr = parse_contract("(*self)@.len()").unwrap();
    if let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = &expr
    {
        assert_eq!(method, "len");
        assert!(args.is_empty());
        assert!(
            matches!(receiver.as_ref(), PureExpr::View(inner) if matches!(inner.as_ref(), PureExpr::Deref(_)))
        );
    } else {
        panic!("Expected MethodCall, got {expr:?}");
    }
}

#[test]
fn test_parse_final_view_method() {
    // (^self)@.len() - final then view then method
    let expr = parse_contract("(^self)@.len()").unwrap();
    if let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = &expr
    {
        assert_eq!(method, "len");
        assert!(args.is_empty());
        assert!(
            matches!(receiver.as_ref(), PureExpr::View(inner) if matches!(inner.as_ref(), PureExpr::Final(_)))
        );
    } else {
        panic!("Expected MethodCall, got {expr:?}");
    }
}

#[test]
fn test_parse_mul_then_deref() {
    // x * *y - multiplication followed by deref (no space)
    let expr = parse_ok("x * *y");
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Mul, r)
        if matches!(l.as_ref(), PureExpr::Var(_, _))
        && matches!(r.as_ref(), PureExpr::Deref(d) if matches!(d.as_ref(), PureExpr::Var(_, _)))
    ));

    // Without spaces: x**y should also work
    let expr2 = parse_ok("x**y");
    assert!(matches!(
        expr2,
        PureExpr::BinOp(l, BinOp::Mul, r)
        if matches!(l.as_ref(), PureExpr::Var(_, _))
        && matches!(r.as_ref(), PureExpr::Deref(d) if matches!(d.as_ref(), PureExpr::Var(_, _)))
    ));
}

#[test]
fn test_parse_chained_comparison_semantics() {
    // Creusot-style chained comparisons desugar to conjunction:
    // a < b < c  =>  (a < b) && (b < c)
    let expr = parse_ok("a < b < c");
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::And, r)
        if matches!(l.as_ref(), PureExpr::BinOp(_, BinOp::Lt, _))
        && matches!(r.as_ref(), PureExpr::BinOp(_, BinOp::Lt, _))
    ));
}

#[test]
fn test_parse_bitwise_shift_operators() {
    let shl = parse_ok("x << 3");
    assert!(matches!(
        shl,
        PureExpr::BinOp(l, BinOp::Shl, r)
        if matches!(l.as_ref(), PureExpr::Var(_, _))
        && matches!(r.as_ref(), PureExpr::Int(3))
    ));

    let shr = parse_ok("x >> 1");
    assert!(matches!(
        shr,
        PureExpr::BinOp(l, BinOp::Shr, r)
        if matches!(l.as_ref(), PureExpr::Var(_, _))
        && matches!(r.as_ref(), PureExpr::Int(1))
    ));
}

#[test]
fn test_parse_bitwise_binary_operators() {
    let and_expr = parse_ok("x & y");
    assert!(matches!(
        and_expr,
        PureExpr::BinOp(l, BinOp::BitAnd, r)
        if matches!(l.as_ref(), PureExpr::Var(_, _))
        && matches!(r.as_ref(), PureExpr::Var(_, _))
    ));

    let xor_expr = parse_ok("x ^ y");
    assert!(matches!(
        xor_expr,
        PureExpr::BinOp(l, BinOp::BitXor, r)
        if matches!(l.as_ref(), PureExpr::Var(_, _))
        && matches!(r.as_ref(), PureExpr::Var(_, _))
    ));

    let or_expr = parse_ok("x | y");
    assert!(matches!(
        or_expr,
        PureExpr::BinOp(l, BinOp::BitOr, r)
        if matches!(l.as_ref(), PureExpr::Var(_, _))
        && matches!(r.as_ref(), PureExpr::Var(_, _))
    ));
}

#[test]
fn test_parse_bitwise_not_operator() {
    let expr = parse_ok("~x");
    assert!(matches!(
        expr,
        PureExpr::UnOp(UnOp::BitNot, inner)
        if matches!(inner.as_ref(), PureExpr::Var(_, _))
    ));

    let spanned = parse_spanned_ok("~x == -1");
    assert!(matches!(spanned.expr, PureExpr::BinOp(_, BinOp::Eq, _)));
}

#[test]
fn test_parse_bitwise_precedence() {
    // Rust precedence: + binds tighter than <<, and bitwise binds tighter than comparisons.
    let shift = parse_ok("1 + 2 << 3");
    assert!(matches!(
        shift,
        PureExpr::BinOp(l, BinOp::Shl, r)
        if matches!(l.as_ref(), PureExpr::BinOp(_, BinOp::Add, _))
        && matches!(r.as_ref(), PureExpr::Int(3))
    ));

    let cmp = parse_ok("x & y == z");
    assert!(matches!(
        cmp,
        PureExpr::BinOp(l, BinOp::Eq, r)
        if matches!(l.as_ref(), PureExpr::BinOp(_, BinOp::BitAnd, _))
        && matches!(r.as_ref(), PureExpr::Var(_, _))
    ));

    let logical = parse_ok("x | y || z");
    assert!(matches!(
        logical,
        PureExpr::BinOp(l, BinOp::Or, r)
        if matches!(l.as_ref(), PureExpr::BinOp(_, BinOp::BitOr, _))
        && matches!(r.as_ref(), PureExpr::Var(_, _))
    ));
}

#[test]
fn test_parse_nth_bit_from_left_logic_body() {
    // Regression for bug/1575: parser used to fail at `<<` in this logic body.
    let body = "{ let mask: u8 = 1u8 << (7usize - left); x & mask }";
    let parsed = parse_ok(body);
    assert!(matches!(parsed, PureExpr::Let { .. }));
}

#[test]
fn test_parse_bitwise_spanned_equivalence() {
    let input = "(x << 3) & (y >> 1) ^ z | w";
    let regular = parse_ok(input);
    let spanned = parse_spanned_ok(input);
    assert_eq!(regular, spanned.expr);
}
