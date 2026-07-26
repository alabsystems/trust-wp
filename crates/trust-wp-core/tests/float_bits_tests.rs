// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `FloatBits` — IEEE 754 bit-pattern wrapper.

#![allow(clippy::float_cmp, clippy::approx_constant)]

use trust_wp_core::formula::FloatBits;

#[test]
fn roundtrip_f64_zero() {
    let fb = FloatBits::from_f64(0.0);
    assert_eq!(fb.to_f64(), 0.0);
}

#[test]
fn roundtrip_f64_positive() {
    let fb = FloatBits::from_f64(3.14);
    assert!((fb.to_f64() - 3.14).abs() < f64::EPSILON);
}

#[test]
fn roundtrip_f64_negative() {
    let fb = FloatBits::from_f64(-2.718);
    assert!((fb.to_f64() - (-2.718)).abs() < f64::EPSILON);
}

#[test]
fn roundtrip_f32_via_promotion() {
    let fb = FloatBits::from_f32(1.5_f32);
    assert_eq!(fb.to_f64(), 1.5);
}

#[test]
fn f32_promotion_is_lossless() {
    let val: f32 = 0.1;
    let fb = FloatBits::from_f32(val);
    assert_eq!(fb.to_f64(), f64::from(val));
}

#[test]
fn equality_same_value() {
    let a = FloatBits::from_f64(42.0);
    let b = FloatBits::from_f64(42.0);
    assert_eq!(a, b);
}

#[test]
fn inequality_different_values() {
    let a = FloatBits::from_f64(1.0);
    let b = FloatBits::from_f64(2.0);
    assert_ne!(a, b);
}

#[test]
fn nan_is_representable_and_equal_to_itself() {
    let a = FloatBits::from_f64(f64::NAN);
    let b = FloatBits::from_f64(f64::NAN);
    assert_eq!(a, b, "bit-level NaN equality");
}

#[test]
fn infinity_roundtrip() {
    let fb = FloatBits::from_f64(f64::INFINITY);
    assert_eq!(fb.to_f64(), f64::INFINITY);
}

#[test]
fn neg_infinity_roundtrip() {
    let fb = FloatBits::from_f64(f64::NEG_INFINITY);
    assert_eq!(fb.to_f64(), f64::NEG_INFINITY);
}

#[test]
fn positive_and_negative_zero_differ() {
    let pos = FloatBits::from_f64(0.0);
    let neg = FloatBits::from_f64(-0.0);
    assert_ne!(pos, neg, "+0.0 and -0.0 should have different bit patterns");
}

#[test]
fn hash_consistency() {
    use std::collections::HashSet;
    let mut set = HashSet::new();
    set.insert(FloatBits::from_f64(1.0));
    set.insert(FloatBits::from_f64(1.0));
    assert_eq!(
        set.len(),
        1,
        "identical values should deduplicate in HashSet"
    );
}

#[test]
fn display_renders_value() {
    let fb = FloatBits::from_f64(2.5);
    assert_eq!(format!("{fb}"), "2.5");
}

#[test]
fn display_renders_integer_float() {
    let fb = FloatBits::from_f64(100.0);
    assert_eq!(format!("{fb}"), "100");
}

#[test]
fn clone_and_copy() {
    let fb = FloatBits::from_f64(9.8);
    let cloned = fb;
    assert_eq!(fb, cloned);
}
