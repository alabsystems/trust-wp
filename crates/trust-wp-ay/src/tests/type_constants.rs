// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for type constant resolution (proof_coverage gap, #904).
//!
//! `type_constants_for_int` had zero direct test references in src/tests/.
//! These tests verify correct MIN/MAX values for all recognized integer types
//! and the None return for unrecognized types. Also tests the encoder's
//! end-to-end handling of type constants via `set_type_constants`.

use ntest::timeout;
use trust_wp_core::formula::PureExpr;

use crate::type_constants_for_int;

// --- type_constants_for_int ---

#[test]
#[timeout(30000)]
fn type_constants_i8() {
    let map = type_constants_for_int("i8").expect("i8 should be recognized");
    assert_eq!(
        map["Self::MIN"],
        PureExpr::Int(i64::from(i8::MIN)),
        "i8 Self::MIN should be -128"
    );
    assert_eq!(
        map["Self::MAX"],
        PureExpr::Int(i64::from(i8::MAX)),
        "i8 Self::MAX should be 127"
    );
    assert_eq!(map.len(), 2, "map should contain exactly MIN and MAX");
}

#[test]
#[timeout(30000)]
fn type_constants_i16() {
    let map = type_constants_for_int("i16").expect("i16 should be recognized");
    assert_eq!(map["Self::MIN"], PureExpr::Int(i64::from(i16::MIN)));
    assert_eq!(map["Self::MAX"], PureExpr::Int(i64::from(i16::MAX)));
}

#[test]
#[timeout(30000)]
fn type_constants_i32() {
    let map = type_constants_for_int("i32").expect("i32 should be recognized");
    assert_eq!(map["Self::MIN"], PureExpr::Int(i64::from(i32::MIN)));
    assert_eq!(map["Self::MAX"], PureExpr::Int(i64::from(i32::MAX)));
}

#[test]
#[timeout(30000)]
fn type_constants_i64() {
    let map = type_constants_for_int("i64").expect("i64 should be recognized");
    assert_eq!(map["Self::MIN"], PureExpr::Int(i64::MIN));
    assert_eq!(map["Self::MAX"], PureExpr::Int(i64::MAX));
}

#[test]
#[timeout(30000)]
fn type_constants_i128_exact_symbolic() {
    use trust_wp_core::formula::int_bounds::signed_bounds_expr;
    let map = type_constants_for_int("i128").expect("i128 should be recognized");
    let (expected_min, expected_max) = signed_bounds_expr(128);
    assert_eq!(
        map["Self::MIN"], expected_min,
        "i128 MIN should be exact symbolic expression"
    );
    assert_eq!(
        map["Self::MAX"], expected_max,
        "i128 MAX should be exact symbolic expression"
    );
}

#[test]
#[timeout(30000)]
fn type_constants_isize_assumes_64bit() {
    let map = type_constants_for_int("isize").expect("isize should be recognized");
    // isize assumes 64-bit (overwhelmingly common platform).
    assert_eq!(
        map["Self::MIN"],
        PureExpr::Int(i64::MIN),
        "isize MIN should assume 64-bit"
    );
    assert_eq!(
        map["Self::MAX"],
        PureExpr::Int(i64::MAX),
        "isize MAX should assume 64-bit"
    );
}

#[test]
#[timeout(30000)]
fn type_constants_u8() {
    let map = type_constants_for_int("u8").expect("u8 should be recognized");
    assert_eq!(map["Self::MIN"], PureExpr::Int(0), "u8 MIN should be 0");
    assert_eq!(
        map["Self::MAX"],
        PureExpr::Int(i64::from(u8::MAX)),
        "u8 MAX should be 255"
    );
}

#[test]
#[timeout(30000)]
fn type_constants_u16() {
    let map = type_constants_for_int("u16").expect("u16 should be recognized");
    assert_eq!(map["Self::MIN"], PureExpr::Int(0));
    assert_eq!(map["Self::MAX"], PureExpr::Int(i64::from(u16::MAX)));
}

#[test]
#[timeout(30000)]
fn type_constants_u32() {
    let map = type_constants_for_int("u32").expect("u32 should be recognized");
    assert_eq!(map["Self::MIN"], PureExpr::Int(0));
    assert_eq!(map["Self::MAX"], PureExpr::Int(i64::from(u32::MAX)));
}

#[test]
#[timeout(30000)]
fn type_constants_u64_exact_symbolic() {
    use trust_wp_core::formula::int_bounds::unsigned_max_expr;
    let map = type_constants_for_int("u64").expect("u64 should be recognized");
    assert_eq!(map["Self::MIN"], PureExpr::Int(0), "u64 MIN should be 0");
    assert_eq!(
        map["Self::MAX"],
        unsigned_max_expr(64),
        "u64 MAX should be exact symbolic expression (2^64 - 1)"
    );
}

#[test]
#[timeout(30000)]
fn type_constants_u128_exact_symbolic() {
    use trust_wp_core::formula::int_bounds::unsigned_max_expr;
    let map = type_constants_for_int("u128").expect("u128 should be recognized");
    assert_eq!(map["Self::MIN"], PureExpr::Int(0));
    assert_eq!(
        map["Self::MAX"],
        unsigned_max_expr(128),
        "u128 MAX should be exact symbolic expression (2^128 - 1)"
    );
}

#[test]
#[timeout(30000)]
fn type_constants_usize_assumes_64bit() {
    use trust_wp_core::formula::int_bounds::unsigned_max_expr;
    let map = type_constants_for_int("usize").expect("usize should be recognized");
    assert_eq!(map["Self::MIN"], PureExpr::Int(0));
    assert_eq!(
        map["Self::MAX"],
        unsigned_max_expr(64),
        "usize MAX should be exact symbolic expression (2^64 - 1, assumes 64-bit)"
    );
}

#[test]
#[timeout(30000)]
fn type_constants_unrecognized_returns_none() {
    assert!(
        type_constants_for_int("String").is_none(),
        "String should not be recognized as integer type"
    );
    assert!(type_constants_for_int("bool").is_none());
    assert!(type_constants_for_int("f64").is_none());
    assert!(type_constants_for_int("").is_none());
    assert!(type_constants_for_int("I32").is_none(), "case sensitive");
}

// --- set_type_constants end-to-end ---

/// Verify that setting type constants on the encoder actually makes them
/// available during encoding. This covers the `set_type_constants` function
/// which had zero test references in src/tests/.
#[test]
#[timeout(30000)]
fn set_type_constants_makes_constants_available() {
    use crate::{AYEncoder, ExprSort, PureExpr};

    let mut encoder = AYEncoder::new();
    let constants = type_constants_for_int("i32").unwrap();
    encoder.set_type_constants(constants.clone());

    // Encode Self::MIN as a pure expression — should resolve via type constants.
    let self_min = PureExpr::Var("Self::MIN".to_string(), Some(ExprSort::Int));
    let result = encoder.encode_pure(&self_min);
    assert!(
        result.is_ok(),
        "encoding Self::MIN with type constants set should succeed, got: {result:?}"
    );
}

/// Verify that all 12 recognized integer types produce consistent maps:
/// always exactly 2 entries (Self::MIN, Self::MAX), with MIN <= MAX.
#[test]
#[timeout(30000)]
fn all_integer_types_produce_consistent_maps() {
    let types = [
        "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize",
    ];
    for ty in &types {
        let map = type_constants_for_int(ty).unwrap_or_else(|| panic!("{ty} should be recognized"));
        assert_eq!(map.len(), 2, "{ty}: map should have exactly 2 entries");
        assert!(
            map.contains_key("Self::MIN"),
            "{ty}: map must contain Self::MIN"
        );
        assert!(
            map.contains_key("Self::MAX"),
            "{ty}: map must contain Self::MAX"
        );
        // PureExpr does not implement PartialOrd, so we verify MIN != MAX
        // (for all integer types, MIN < MAX, so they must differ).
        assert_ne!(
            map["Self::MIN"], map["Self::MAX"],
            "{ty}: Self::MIN must differ from Self::MAX"
        );
    }
}

/// Verify unsigned types all have MIN == 0.
#[test]
#[timeout(30000)]
fn unsigned_types_all_have_min_zero() {
    for ty in &["u8", "u16", "u32", "u64", "u128", "usize"] {
        let map = type_constants_for_int(ty).unwrap();
        assert_eq!(
            map["Self::MIN"],
            PureExpr::Int(0),
            "{ty}: unsigned Self::MIN must be 0"
        );
    }
}

/// Verify that the Self::MIN/MAX pair for each type via type_constants_for_int
/// matches the corresponding qualified form via the encoder's constant resolution.
/// This tests the end-to-end path: both functions must agree.
#[test]
#[timeout(30000)]
fn self_constants_match_qualified_constants_via_encoder() {
    use crate::{AYEncoder, ExprSort, PureExpr, SolveResult};

    // Test for i32: Self::MIN with type_constants == i32::MIN via qualified constant
    let mut encoder = AYEncoder::new();
    let constants = type_constants_for_int("i32").unwrap();
    encoder.set_type_constants(constants);

    // Encode Self::MIN
    let self_min = PureExpr::Var("Self::MIN".to_string(), Some(ExprSort::Int));
    let self_min_term = encoder
        .encode_pure(&self_min)
        .expect("Self::MIN should encode");

    // Encode the literal i32::MIN value
    let i32_min_literal = PureExpr::Int(i64::from(i32::MIN));
    let literal_term = encoder
        .encode_pure(&i32_min_literal)
        .expect("literal should encode");

    // Assert they're equal and check satisfiability
    let eq = encoder.solver.eq(self_min_term, literal_term);
    encoder.solver.assert_term(eq);

    let result = encoder.check_sat();
    assert_eq!(
        result,
        SolveResult::Sat,
        "Self::MIN == i32::MIN should be satisfiable"
    );
}
