// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for type constant resolution and qualified integer constants.

use std::{collections::HashMap, sync::Arc};

use ay_dpll::api::SolveResult;
use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use super::*;
use crate::AYEncoder;

#[test]
#[timeout(30000)]
fn type_constants_for_int_i32() {
    let map = type_constants_for_int("i32").expect("i32 should have type constants");
    assert_eq!(
        map["Self::MIN"],
        PureExpr::Int(i64::from(i32::MIN)),
        "i32 Self::MIN should be i32::MIN"
    );
    assert_eq!(
        map["Self::MAX"],
        PureExpr::Int(i64::from(i32::MAX)),
        "i32 Self::MAX should be i32::MAX"
    );
}

#[test]
#[timeout(30000)]
fn type_constants_for_int_u8() {
    let map = type_constants_for_int("u8").expect("u8 should have type constants");
    assert_eq!(
        map["Self::MIN"],
        PureExpr::Int(0),
        "u8 Self::MIN should be 0"
    );
    assert_eq!(
        map["Self::MAX"],
        PureExpr::Int(255),
        "u8 Self::MAX should be 255"
    );
}

#[test]
#[timeout(30000)]
fn type_constants_for_int_i64() {
    let map = type_constants_for_int("i64").expect("i64 should have type constants");
    assert_eq!(
        map["Self::MIN"],
        PureExpr::Int(i64::MIN),
        "i64 Self::MIN should be i64::MIN"
    );
    assert_eq!(
        map["Self::MAX"],
        PureExpr::Int(i64::MAX),
        "i64 Self::MAX should be i64::MAX"
    );
}

#[test]
#[timeout(30000)]
fn type_constants_for_int_unknown_returns_none() {
    assert!(
        type_constants_for_int("String").is_none(),
        "String should not have type constants"
    );
    assert!(
        type_constants_for_int("bool").is_none(),
        "bool should not have type constants"
    );
}

#[test]
#[timeout(30000)]
fn encode_var_resolves_type_constant() {
    let mut encoder = AYEncoder::new();
    let mut constants = HashMap::new();
    constants.insert("Self::MIN".to_string(), PureExpr::Int(-128));
    constants.insert("Self::MAX".to_string(), PureExpr::Int(127));
    encoder.set_type_constants(constants);

    let expr = PureExpr::Var("Self::MIN".to_string(), None);
    let term = encoder
        .encode_pure_impl(&expr, None)
        .expect("Self::MIN should encode successfully");
    let expected = encoder.solver.int_const(-128);
    let eq = encoder.solver.eq(term, expected);
    encoder.assert_term(eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Self::MIN == -128 should be SAT when type constants set to i8 range"
    );
}

#[test]
#[timeout(30000)]
fn encode_view_var_resolves_type_constant() {
    let mut encoder = AYEncoder::new();
    let mut constants = HashMap::new();
    constants.insert("Self::MAX".to_string(), PureExpr::Int(127));
    encoder.set_type_constants(constants);

    let expr = PureExpr::View(Arc::new(PureExpr::Var("Self::MAX".to_string(), None)));
    let term = encoder
        .encode_pure_impl(&expr, None)
        .expect("View(Self::MAX) should encode successfully");
    let expected = encoder.solver.int_const(127);
    let eq = encoder.solver.eq(term, expected);
    encoder.assert_term(eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "View(Self::MAX) == 127 should be SAT when type constant is 127"
    );
}

#[test]
#[timeout(30000)]
fn encode_var_without_type_constants_is_uninterpreted() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::Var("Self::MIN".to_string(), None);
    let term = encoder
        .encode_pure_impl(&expr, None)
        .expect("Self::MIN should encode as uninterpreted variable");
    let five = encoder.solver.int_const(5);
    let eq = encoder.solver.eq(term, five);
    encoder.assert_term(eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "uninterpreted Self::MIN == 5 should be SAT (no type constants set)"
    );
}

// ── resolve_qualified_int_constant tests ─────────────────────────────

#[test]
#[timeout(30000)]
fn resolve_qualified_i8_bounds() {
    assert_eq!(
        resolve_qualified_int_constant("i8::MIN"),
        Some(PureExpr::Int(-128)),
        "i8::MIN should resolve to -128"
    );
    assert_eq!(
        resolve_qualified_int_constant("i8::MAX"),
        Some(PureExpr::Int(127)),
        "i8::MAX should resolve to 127"
    );
}

#[test]
#[timeout(30000)]
fn resolve_qualified_i16_bounds() {
    assert_eq!(
        resolve_qualified_int_constant("i16::MIN"),
        Some(PureExpr::Int(-32768)),
        "i16::MIN should resolve to -32768"
    );
    assert_eq!(
        resolve_qualified_int_constant("i16::MAX"),
        Some(PureExpr::Int(32767)),
        "i16::MAX should resolve to 32767"
    );
}

#[test]
#[timeout(30000)]
fn resolve_qualified_i32_bounds() {
    assert_eq!(
        resolve_qualified_int_constant("i32::MIN"),
        Some(PureExpr::Int(i64::from(i32::MIN))),
        "i32::MIN should resolve to i32::MIN as i64"
    );
    assert_eq!(
        resolve_qualified_int_constant("i32::MAX"),
        Some(PureExpr::Int(i64::from(i32::MAX))),
        "i32::MAX should resolve to i32::MAX as i64"
    );
}

#[test]
#[timeout(30000)]
fn resolve_qualified_i64_bounds() {
    assert_eq!(
        resolve_qualified_int_constant("i64::MIN"),
        Some(PureExpr::Int(i64::MIN)),
        "i64::MIN should resolve to i64::MIN"
    );
    assert_eq!(
        resolve_qualified_int_constant("i64::MAX"),
        Some(PureExpr::Int(i64::MAX)),
        "i64::MAX should resolve to i64::MAX"
    );
}

#[test]
#[timeout(30000)]
fn resolve_qualified_isize_matches_type_constants() {
    assert_eq!(
        resolve_qualified_int_constant("isize::MIN"),
        Some(PureExpr::Int(i64::MIN)),
        "isize::MIN should use 64-bit bounds (overwhelmingly common platform)"
    );
    assert_eq!(
        resolve_qualified_int_constant("isize::MAX"),
        Some(PureExpr::Int(i64::MAX)),
        "isize::MAX should use 64-bit bounds (overwhelmingly common platform)"
    );
}

#[test]
#[timeout(30000)]
fn resolve_qualified_i128_exact() {
    use trust_wp_core::formula::int_bounds::signed_bounds_expr;
    let (expected_min, expected_max) = signed_bounds_expr(128);
    assert_eq!(
        resolve_qualified_int_constant("i128::MIN"),
        Some(expected_min),
        "i128::MIN should be exact symbolic expression"
    );
    assert_eq!(
        resolve_qualified_int_constant("i128::MAX"),
        Some(expected_max),
        "i128::MAX should be exact symbolic expression"
    );
}

#[test]
#[timeout(30000)]
fn resolve_qualified_unsigned_min_all_zero() {
    for ty in &["u8", "u16", "u32", "u64", "u128", "usize"] {
        let key = format!("{ty}::MIN");
        assert_eq!(
            resolve_qualified_int_constant(&key),
            Some(PureExpr::Int(0)),
            "{key} should resolve to 0"
        );
    }
}

#[test]
#[timeout(30000)]
fn resolve_qualified_unsigned_max() {
    use trust_wp_core::formula::int_bounds::unsigned_max_expr;
    assert_eq!(
        resolve_qualified_int_constant("u8::MAX"),
        Some(PureExpr::Int(255)),
        "u8::MAX should resolve to 255"
    );
    assert_eq!(
        resolve_qualified_int_constant("u16::MAX"),
        Some(PureExpr::Int(65535)),
        "u16::MAX should resolve to 65535"
    );
    assert_eq!(
        resolve_qualified_int_constant("u32::MAX"),
        Some(PureExpr::Int(i64::from(u32::MAX))),
        "u32::MAX should resolve to u32::MAX as i64"
    );
    assert_eq!(
        resolve_qualified_int_constant("u64::MAX"),
        Some(unsigned_max_expr(64)),
        "u64::MAX should be exact symbolic expression (2^64 - 1)"
    );
    assert_eq!(
        resolve_qualified_int_constant("usize::MAX"),
        Some(unsigned_max_expr(64)),
        "usize::MAX should be exact symbolic expression (2^64 - 1)"
    );
    assert_eq!(
        resolve_qualified_int_constant("u128::MAX"),
        Some(unsigned_max_expr(128)),
        "u128::MAX should be exact symbolic expression (2^128 - 1)"
    );
}

#[test]
#[timeout(30000)]
fn resolve_qualified_isize_usize_consistent_with_type_constants() {
    let isize_map = type_constants_for_int("isize").expect("isize should have type constants");
    assert_eq!(
        resolve_qualified_int_constant("isize::MIN"),
        Some(isize_map["Self::MIN"].clone()),
        "isize::MIN must match type_constants_for_int(\"isize\")[\"Self::MIN\"]"
    );
    assert_eq!(
        resolve_qualified_int_constant("isize::MAX"),
        Some(isize_map["Self::MAX"].clone()),
        "isize::MAX must match type_constants_for_int(\"isize\")[\"Self::MAX\"]"
    );

    let usize_map = type_constants_for_int("usize").expect("usize should have type constants");
    assert_eq!(
        resolve_qualified_int_constant("usize::MIN"),
        Some(usize_map["Self::MIN"].clone()),
        "usize::MIN must match type_constants_for_int(\"usize\")[\"Self::MIN\"]"
    );
    assert_eq!(
        resolve_qualified_int_constant("usize::MAX"),
        Some(usize_map["Self::MAX"].clone()),
        "usize::MAX must match type_constants_for_int(\"usize\")[\"Self::MAX\"]"
    );
}

#[test]
#[timeout(30000)]
fn resolve_qualified_unknown_returns_none() {
    assert_eq!(
        resolve_qualified_int_constant("String::MAX"),
        None,
        "non-integer type String should return None"
    );
    assert_eq!(
        resolve_qualified_int_constant("bool::MIN"),
        None,
        "non-integer type bool should return None"
    );
    assert_eq!(
        resolve_qualified_int_constant("i32"),
        None,
        "bare type name without ::MIN/::MAX should return None"
    );
    assert_eq!(
        resolve_qualified_int_constant("MAX"),
        None,
        "unqualified MAX should return None"
    );
    assert_eq!(
        resolve_qualified_int_constant(""),
        None,
        "empty string should return None"
    );
}

#[test]
#[timeout(30000)]
fn encode_var_resolves_qualified_int_constant() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::Var("u32::MAX".to_string(), None);
    let term = encoder
        .encode_pure_impl(&expr, None)
        .expect("u32::MAX should encode via qualified constant resolution");
    let expected = encoder.solver.int_const(i64::from(u32::MAX));
    let eq = encoder.solver.eq(term, expected);
    encoder.assert_term(eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "u32::MAX == 4294967295 should be SAT via qualified constant resolution"
    );

    let mut enc2 = AYEncoder::new();
    let term2 = enc2
        .encode_pure_impl(&PureExpr::Var("u32::MAX".to_string(), None), None)
        .expect("u32::MAX should encode via qualified constant resolution");
    let zero = enc2.solver.int_const(0);
    let eq2 = enc2.solver.eq(term2, zero);
    enc2.assert_term(eq2);
    assert!(
        matches!(enc2.check_sat(), SolveResult::Unsat(_)),
        "u32::MAX == 0 should be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn encode_view_var_resolves_qualified_int_constant() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::View(Arc::new(PureExpr::Var("i32::MIN".to_string(), None)));
    let term = encoder
        .encode_pure_impl(&expr, None)
        .expect("View(i32::MIN) should encode via qualified constant resolution");
    let expected = encoder.solver.int_const(i64::from(i32::MIN));
    let eq = encoder.solver.eq(term, expected);
    encoder.assert_term(eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "View(i32::MIN) == i32::MIN should be SAT via qualified constant resolution"
    );
}

// ── Wide type symbolic encoding tests (#2315) ────────────────────────
//
// These tests exercise the new PureExpr tree encoding path introduced in
// W3-2352 for types wider than 64 bits (u64::MAX, i128::MIN, etc.).
// The encoder now recursively encodes BinOp trees rather than directly
// calling solver.int_const(), which only accepts i64.

#[test]
#[timeout(30000)]
fn encode_u64_max_symbolic_tree_is_exact() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::Var("u64::MAX".to_string(), None);
    let term = encoder
        .encode_pure_impl(&expr, None)
        .expect("u64::MAX should encode via symbolic BinOp tree");

    // u64::MAX = 2^64 - 1. Assert that the encoded value > i64::MAX
    // (which proves it's not truncated to i64).
    let i64_max = encoder.solver.int_const(i64::MAX);
    let gt = encoder.solver.gt(term, i64_max);
    encoder.assert_term(gt);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "u64::MAX > i64::MAX should be SAT (proves no truncation to i64)"
    );
}

#[test]
#[timeout(30000)]
fn encode_u64_max_not_equal_to_i64_max() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::Var("u64::MAX".to_string(), None);
    let term = encoder
        .encode_pure_impl(&expr, None)
        .expect("u64::MAX should encode");
    let i64_max = encoder.solver.int_const(i64::MAX);
    let eq = encoder.solver.eq(term, i64_max);
    encoder.assert_term(eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "u64::MAX == i64::MAX should be UNSAT (they differ by 2^63)"
    );
}

#[test]
#[timeout(30000)]
fn encode_i128_min_symbolic_tree_is_negative() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::Var("i128::MIN".to_string(), None);
    let term = encoder
        .encode_pure_impl(&expr, None)
        .expect("i128::MIN should encode via symbolic BinOp tree");

    // i128::MIN = -2^127. Assert it's less than i64::MIN.
    let i64_min = encoder.solver.int_const(i64::MIN);
    let lt = encoder.solver.lt(term, i64_min);
    encoder.assert_term(lt);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "i128::MIN < i64::MIN should be SAT (proves no truncation to i64)"
    );
}

#[test]
#[timeout(30000)]
fn encode_u128_max_symbolic_tree_gt_u64_max() {
    let mut encoder = AYEncoder::new();
    let u128_expr = PureExpr::Var("u128::MAX".to_string(), None);
    let u128_term = encoder
        .encode_pure_impl(&u128_expr, None)
        .expect("u128::MAX should encode");
    let u64_expr = PureExpr::Var("u64::MAX".to_string(), None);
    let u64_term = encoder
        .encode_pure_impl(&u64_expr, None)
        .expect("u64::MAX should encode");

    let gt = encoder.solver.gt(u128_term, u64_term);
    encoder.assert_term(gt);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "u128::MAX > u64::MAX should be SAT"
    );
}

#[test]
#[timeout(30000)]
fn encode_type_constants_wide_pureexpr_through_encoder() {
    use trust_wp_core::formula::int_bounds::unsigned_max_expr;
    let mut encoder = AYEncoder::new();
    let mut constants = HashMap::new();
    constants.insert("Self::MIN".to_string(), PureExpr::Int(0));
    constants.insert("Self::MAX".to_string(), unsigned_max_expr(64));
    encoder.set_type_constants(constants);

    // Encode Self::MAX through the type_constants path (vars.rs).
    let expr = PureExpr::Var("Self::MAX".to_string(), None);
    let term = encoder
        .encode_pure_impl(&expr, None)
        .expect("Self::MAX with u64 PureExpr tree should encode");

    // Verify it's greater than i64::MAX.
    let i64_max = encoder.solver.int_const(i64::MAX);
    let gt = encoder.solver.gt(term, i64_max);
    encoder.assert_term(gt);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "Self::MAX (u64) > i64::MAX should be SAT when type_constants use symbolic PureExpr"
    );
}

#[test]
#[timeout(30000)]
fn encode_view_u64_max_symbolic_tree_is_exact() {
    let mut encoder = AYEncoder::new();
    let expr = PureExpr::View(Arc::new(PureExpr::Var("u64::MAX".to_string(), None)));
    let term = encoder
        .encode_pure_impl(&expr, None)
        .expect("View(u64::MAX) should encode via symbolic tree");

    let i64_max = encoder.solver.int_const(i64::MAX);
    let gt = encoder.solver.gt(term, i64_max);
    encoder.assert_term(gt);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "View(u64::MAX) > i64::MAX should be SAT (proves View path also uses exact encoding)"
    );
}
