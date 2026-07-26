#![allow(clippy::approx_constant, clippy::float_cmp)]
// float literals are intentional parser test inputs
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Pearlite parser parity forms added for Creusot replacement:
//! float literals (`missing-float-literal-parse`) and type ascription
//! (`missing-type-ascription-term`).
//!
//! Each parsed form is asserted to land on the exact `PureExpr` the encoder
//! consumes:
//! - float literals produce `PureExpr::Float(FloatBits::from_f64(_))`, which
//!   the ay encoder lowers to an SMT `Real` const via
//!   `pure_encoding`'s `try_real_const(v.to_f64())` (verified by tracing);
//! - type ascriptions are transparent — they return the *inner* expression
//!   unchanged, introducing no new node, so the encoder sees the same tree it
//!   would for the un-ascribed term.

use std::sync::Arc;

use super::*;
use crate::formula::FloatBits;

fn float(v: f64) -> PureExpr {
    PureExpr::Float(FloatBits::from_f64(v))
}

// ---------------------------------------------------------------------------
// Float literals
// ---------------------------------------------------------------------------

#[test]
fn test_parse_float_fractional() {
    assert_eq!(parse_ok("1.5"), float(1.5));
    assert_eq!(parse_ok("0.0"), float(0.0));
    assert_eq!(parse_ok("3.14159"), float(3.14159));
    assert_eq!(parse_ok("100.25"), float(100.25));
}

#[test]
fn test_parse_float_negative() {
    assert_eq!(parse_ok("-1.5"), float(-1.5));
    assert_eq!(parse_ok("-0.5"), float(-0.5));
}

#[test]
fn test_parse_float_exponent() {
    assert_eq!(parse_ok("1e10"), float(1e10));
    assert_eq!(parse_ok("2E3"), float(2e3));
    assert_eq!(parse_ok("1.5e2"), float(1.5e2));
    assert_eq!(parse_ok("3.0e-4"), float(3.0e-4));
    assert_eq!(parse_ok("6.022e+23"), float(6.022e23));
}

#[test]
fn test_parse_float_with_suffix() {
    // f32 / f64 suffixes are discarded — contract floats are mathematical reals.
    assert_eq!(parse_ok("1.5f64"), float(1.5));
    assert_eq!(parse_ok("2.5f32"), float(2.5));
    assert_eq!(parse_ok("1.0f64"), float(1.0));
}

#[test]
fn test_parse_float_underscore_separators() {
    assert_eq!(parse_ok("1_000.5"), float(1000.5));
    assert_eq!(parse_ok("3.141_592"), float(3.141_592));
}

#[test]
fn test_parse_float_in_binop() {
    // `x@ == 1.5` should parse the RHS as a float literal.
    assert_eq!(
        parse_ok("x@ == 1.5"),
        PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var("x".into(), None)))),
            crate::formula::BinOp::Eq,
            Arc::new(float(1.5)),
        )
    );
}

#[test]
fn test_parse_float_spanned() {
    // The span-tracking parser must agree with the unspanned parser.
    let spanned = parse_spanned_ok("1.5");
    assert_eq!(spanned.expr, float(1.5));

    let spanned_neg = parse_spanned_ok("-2.25");
    assert_eq!(spanned_neg.expr, float(-2.25));
}

/// Float-literal parse + structural roundtrip: the parsed `FloatBits` must
/// reproduce the source value bit-exactly via `to_f64`, which is precisely
/// what the encoder feeds to `try_real_const`.
#[test]
fn test_float_roundtrip_to_f64() {
    for src in ["1.5", "0.0", "-3.25", "6.022e23", "2.5f32"] {
        let expr = parse_ok(src);
        match expr {
            PureExpr::Float(bits) => {
                let expected: f64 = src
                    .trim_end_matches("f32")
                    .trim_end_matches("f64")
                    .parse()
                    .unwrap();
                assert_eq!(bits.to_f64(), expected, "roundtrip mismatch for {src:?}");
            }
            other => panic!("expected Float for {src:?}, got {other:?}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Disambiguation: float `.` vs range `..` vs tuple-index / method `.x`
// ---------------------------------------------------------------------------

#[test]
fn test_float_does_not_eat_range() {
    // `s[0..2]` is index/range sugar — the `..` must NOT be read as a float
    // fractional part of `0`.
    let expr = parse_ok("s[0..2]");
    assert_eq!(
        expr,
        PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("s".into(), None)),
            method: "subsequence".into(),
            args: vec![PureExpr::Int(0), PureExpr::Int(2)],
        }
    );
}

#[test]
fn test_tuple_index_still_integer() {
    // `x.0` is a tuple-field access on the variable `x`, NOT the float `x.0`.
    // It is parsed in postfix position on a non-numeric receiver and never
    // reaches the numeric-literal parser.
    let expr = parse_ok("x.0");
    // Tuple field access lowers to a synthetic field logic-fn call.
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            assert!(
                name.contains("tuple") || name.contains("field"),
                "got {name}"
            );
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], PureExpr::Var("x".into(), None));
        }
        other => panic!("expected tuple-field logic-fn call, got {other:?}"),
    }
}

#[test]
fn test_method_call_after_integer_not_float() {
    // `1.method()` — a `.` followed by a non-digit is a method call, not a
    // float. (Edge case; ensures the digit-lookahead guard fires.)
    let expr = parse_ok("1.foo()");
    match expr {
        PureExpr::MethodCall {
            receiver, method, ..
        } => {
            assert_eq!(*receiver, PureExpr::Int(1));
            assert_eq!(method, "foo");
        }
        other => panic!("expected method call on Int(1), got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Type ascription: `(expr : Type)` — transparent, returns the inner expr.
// ---------------------------------------------------------------------------

#[test]
fn test_type_ascription_integer() {
    // `(5 : u32)` → `5`.
    assert_eq!(parse_ok("(5 : u32)"), PureExpr::Int(5));
}

#[test]
fn test_type_ascription_var() {
    // `(x : Int)` → `x`.
    assert_eq!(parse_ok("(x : Int)"), PureExpr::Var("x".into(), None));
}

#[test]
fn test_type_ascription_in_binop() {
    // `(a : u32) == b` → `a == b`. The ascription is discarded.
    assert_eq!(
        parse_ok("(a : u32) == b"),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("a".into(), None)),
            crate::formula::BinOp::Eq,
            Arc::new(PureExpr::Var("b".into(), None)),
        )
    );
}

#[test]
fn test_type_ascription_reference_type() {
    // Ascription to a reference type parses and is discarded.
    assert_eq!(parse_ok("(x : &mut u32)"), PureExpr::Var("x".into(), None));
}

#[test]
fn test_type_ascription_does_not_break_path() {
    // A `::` path separator must NOT be mistaken for an ascription colon.
    // `i32::MAX` should remain a single path variable.
    assert_eq!(parse_ok("i32::MAX"), PureExpr::Var("i32::MAX".into(), None));
}

#[test]
fn test_type_ascription_spanned() {
    // The span-tracking parser must also discard the ascription transparently.
    let spanned = parse_spanned_ok("(x : Int)");
    assert_eq!(spanned.expr, PureExpr::Var("x".into(), None));

    let spanned2 = parse_spanned_ok("(5 : u32) == y");
    assert_eq!(
        spanned2.expr,
        PureExpr::BinOp(
            Arc::new(PureExpr::Int(5)),
            crate::formula::BinOp::Eq,
            Arc::new(PureExpr::Var("y".into(), None)),
        )
    );
}

#[test]
fn test_type_ascription_does_not_break_struct_field() {
    // Struct-literal field colons are consumed before expression parsing, so
    // ascription must not interfere. `Foo { a: x }` keeps its single field.
    let expr = parse_ok("Foo { a: x }");
    match expr {
        PureExpr::LogicFnCall { args, .. } => {
            assert_eq!(args, vec![PureExpr::Var("x".into(), None)]);
        }
        other => panic!("expected struct-literal logic-fn call, got {other:?}"),
    }
}
