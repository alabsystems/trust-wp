// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `SourceSpan`, `SpannedExpr`, and `TrackLevel`.

use trust_wp_core::{
    formula::{PureExpr, SourceSpan, SpannedExpr},
    TrackLevel,
};

// ── SourceSpan ───────────────────────────────────────────────────

#[test]
fn source_span_from_contract() {
    let span = SourceSpan::from_contract(10, 20);
    assert_eq!(span.start, 10);
    assert_eq!(span.end, 20);
    assert_eq!(span.file, None);
    assert_eq!(span.line, None);
    assert_eq!(span.column, None);
}

#[test]
fn source_span_with_location() {
    let span = SourceSpan::with_location("src/main.rs", 42, 5);
    assert_eq!(span.file, Some("src/main.rs".to_string()));
    assert_eq!(span.line, Some(42));
    assert_eq!(span.column, Some(5));
    assert_eq!(span.start, 0);
    assert_eq!(span.end, 0);
}

#[test]
fn source_span_default() {
    let span = SourceSpan::default();
    assert_eq!(span.file, None);
    assert_eq!(span.start, 0);
    assert_eq!(span.end, 0);
    assert_eq!(span.line, None);
    assert_eq!(span.column, None);
}

#[test]
fn source_span_equality() {
    let a = SourceSpan::from_contract(5, 10);
    let b = SourceSpan::from_contract(5, 10);
    assert_eq!(a, b);
}

#[test]
fn source_span_inequality() {
    let a = SourceSpan::from_contract(5, 10);
    let b = SourceSpan::from_contract(5, 15);
    assert_ne!(a, b);
}

#[test]
fn source_span_clone() {
    let a = SourceSpan::with_location("test.rs", 1, 1);
    let b = a.clone();
    assert_eq!(a, b);
}

#[test]
fn source_span_debug() {
    let span = SourceSpan::from_contract(0, 5);
    let dbg = format!("{span:?}");
    assert!(dbg.contains("SourceSpan"), "Debug output: {dbg}");
}

// ── SpannedExpr ──────────────────────────────────────────────────

#[test]
fn spanned_expr_new() {
    let span = SourceSpan::from_contract(0, 10);
    let se = SpannedExpr::new(PureExpr::Int(42), span.clone());
    assert_eq!(se.expr, PureExpr::Int(42));
    assert_eq!(se.span, Some(span));
}

#[test]
fn spanned_expr_unspanned() {
    let se = SpannedExpr::unspanned(PureExpr::Bool(true));
    assert_eq!(se.expr, PureExpr::Bool(true));
    assert_eq!(se.span, None);
}

#[test]
fn spanned_expr_into_expr() {
    let se = SpannedExpr::new(PureExpr::Int(7), SourceSpan::from_contract(0, 1));
    let expr = se.into_expr();
    assert_eq!(expr, PureExpr::Int(7));
}

#[test]
fn spanned_expr_from_pure_expr() {
    let se: SpannedExpr = PureExpr::Bool(false).into();
    assert_eq!(se.expr, PureExpr::Bool(false));
    assert_eq!(se.span, None);
}

#[test]
fn spanned_expr_equality() {
    let a = SpannedExpr::unspanned(PureExpr::Int(1));
    let b = SpannedExpr::unspanned(PureExpr::Int(1));
    assert_eq!(a, b);
}

#[test]
fn spanned_expr_inequality_expr() {
    let a = SpannedExpr::unspanned(PureExpr::Int(1));
    let b = SpannedExpr::unspanned(PureExpr::Int(2));
    assert_ne!(a, b);
}

#[test]
fn spanned_expr_inequality_span() {
    let a = SpannedExpr::new(PureExpr::Int(1), SourceSpan::from_contract(0, 5));
    let b = SpannedExpr::unspanned(PureExpr::Int(1));
    assert_ne!(a, b);
}

#[test]
fn spanned_expr_clone() {
    let a = SpannedExpr::new(PureExpr::Int(42), SourceSpan::from_contract(1, 3));
    let b = a.clone();
    assert_eq!(a, b);
}

// ── TrackLevel ───────────────────────────────────────────────────

#[test]
fn track_level_default_is_auto() {
    assert_eq!(TrackLevel::default(), TrackLevel::Auto);
}

#[test]
fn track_level_all_variants_distinct() {
    let variants = [
        TrackLevel::Auto,
        TrackLevel::Reg,
        TrackLevel::Ptr,
        TrackLevel::Mem,
    ];
    for (i, a) in variants.iter().enumerate() {
        for (j, b) in variants.iter().enumerate() {
            if i == j {
                assert_eq!(a, b);
            } else {
                assert_ne!(a, b, "{a:?} should differ from {b:?}");
            }
        }
    }
}

#[test]
fn track_level_copy() {
    let a = TrackLevel::Mem;
    let b = a;
    assert_eq!(a, b);
}

#[test]
#[allow(clippy::clone_on_copy)]
fn track_level_clone() {
    let a = TrackLevel::Ptr;
    let b = a.clone();
    assert_eq!(a, b);
}

#[test]
fn track_level_debug() {
    assert_eq!(format!("{:?}", TrackLevel::Auto), "Auto");
    assert_eq!(format!("{:?}", TrackLevel::Reg), "Reg");
    assert_eq!(format!("{:?}", TrackLevel::Ptr), "Ptr");
    assert_eq!(format!("{:?}", TrackLevel::Mem), "Mem");
}
