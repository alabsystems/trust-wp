// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust_wp_core::formula::int_bounds`.
//!
//! Tests correctness of `pow2_expr`, `unsigned_max_expr`, and
//! `signed_bounds_expr` across all Rust integer width boundaries.

use trust_wp_core::formula::{
    int_bounds::{pow2_expr, signed_bounds_expr, unsigned_max_expr},
    BinOp, PureExpr,
};

/// Evaluate a `PureExpr` arithmetic tree to `i128` for test verification.
/// Only valid for trees whose mathematical value fits in `i128`.
fn eval_i128(expr: &PureExpr) -> i128 {
    match expr {
        PureExpr::Int(n) => i128::from(*n),
        PureExpr::BinOp(l, op, r) => {
            let lv = eval_i128(l);
            let rv = eval_i128(r);
            match op {
                BinOp::Add => lv.checked_add(rv).expect("overflow in eval"),
                BinOp::Sub => lv.checked_sub(rv).expect("overflow in eval"),
                BinOp::Mul => lv.checked_mul(rv).expect("overflow in eval"),
                _ => panic!("unexpected op in int_bounds expr: {op:?}"),
            }
        }
        other => panic!("unexpected expr in int_bounds: {other:?}"),
    }
}

// ── pow2_expr ────────────────────────────────────────

#[test]
fn pow2_base_cases() {
    assert_eq!(pow2_expr(0), PureExpr::Int(1));
    assert_eq!(pow2_expr(1), PureExpr::Int(2));
}

#[test]
fn pow2_small_values_exact() {
    for exp in 0..=20 {
        let expected = 1_i128 << exp;
        assert_eq!(
            eval_i128(&pow2_expr(exp)),
            expected,
            "pow2_expr({exp}) should evaluate to 2^{exp} = {expected}"
        );
    }
}

#[test]
fn pow2_at_63_and_64() {
    assert_eq!(eval_i128(&pow2_expr(63)), 1_i128 << 63);
    assert_eq!(eval_i128(&pow2_expr(64)), 1_i128 << 64);
}

#[test]
fn pow2_at_126_max_evaluable() {
    assert_eq!(eval_i128(&pow2_expr(126)), 1_i128 << 126);
}

#[test]
fn pow2_recursive_produces_binop_tree() {
    // exp >= 2 should produce BinOp(Mul) trees, not Int literals
    let expr = pow2_expr(2);
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Mul, _)));
}

#[test]
fn pow2_odd_exp_wraps_with_times_two() {
    // Odd exponents: BinOp(Int(2), Mul, squared_half)
    let expr = pow2_expr(3);
    match &expr {
        PureExpr::BinOp(l, BinOp::Mul, _) => {
            assert_eq!(**l, PureExpr::Int(2));
        }
        other => panic!("pow2_expr(3) should be 2 * (...), got {other:?}"),
    }
}

#[test]
fn pow2_logarithmic_depth() {
    // pow2_expr(128) should have depth ~7 (log2(128)), not 128.
    fn depth(expr: &PureExpr) -> usize {
        match expr {
            PureExpr::BinOp(l, _, r) => 1 + depth(l).max(depth(r)),
            _ => 0,
        }
    }
    let d = depth(&pow2_expr(128));
    assert!(
        d <= 15,
        "pow2_expr(128) depth should be logarithmic, got {d}"
    );
}

// ── unsigned_max_expr ────────────────────────────────

#[test]
fn unsigned_max_zero_bits() {
    assert_eq!(unsigned_max_expr(0), PureExpr::Int(0));
}

#[test]
fn unsigned_max_standard_rust_types() {
    assert_eq!(eval_i128(&unsigned_max_expr(8)), i128::from(u8::MAX));
    assert_eq!(eval_i128(&unsigned_max_expr(16)), i128::from(u16::MAX));
    assert_eq!(eval_i128(&unsigned_max_expr(32)), i128::from(u32::MAX));
}

#[test]
fn unsigned_max_literal_up_to_63() {
    for bits in 1..=63 {
        match unsigned_max_expr(bits) {
            PureExpr::Int(n) => {
                let expected = (1_i128 << bits) - 1;
                assert_eq!(
                    i128::from(n),
                    expected,
                    "unsigned_max_expr({bits}) literal value"
                );
            }
            other => panic!("unsigned_max_expr({bits}) should be Int literal, got {other:?}"),
        }
    }
}

#[test]
fn unsigned_max_symbolic_at_64() {
    let expr = unsigned_max_expr(64);
    match &expr {
        PureExpr::BinOp(_, BinOp::Sub, rhs) => {
            assert_eq!(**rhs, PureExpr::Int(1), "u64 max should be pow2(64) - 1");
        }
        other => panic!("unsigned_max_expr(64) should be symbolic BinOp, got {other:?}"),
    }
    assert_eq!(eval_i128(&expr), i128::from(u64::MAX));
}

#[test]
fn unsigned_max_128_is_symbolic() {
    let expr = unsigned_max_expr(128);
    match &expr {
        PureExpr::BinOp(_, BinOp::Sub, rhs) => {
            assert_eq!(**rhs, PureExpr::Int(1), "u128 max should be pow2(128) - 1");
        }
        other => panic!("unsigned_max_expr(128) should be symbolic BinOp, got {other:?}"),
    }
}

// ── signed_bounds_expr ───────────────────────────────

#[test]
fn signed_bounds_zero_bits() {
    assert_eq!(signed_bounds_expr(0), (PureExpr::Int(0), PureExpr::Int(0)));
}

#[test]
fn signed_bounds_8() {
    let (min, max) = signed_bounds_expr(8);
    assert_eq!(min, PureExpr::Int(i64::from(i8::MIN)));
    assert_eq!(max, PureExpr::Int(i64::from(i8::MAX)));
}

#[test]
fn signed_bounds_16() {
    let (min, max) = signed_bounds_expr(16);
    assert_eq!(min, PureExpr::Int(i64::from(i16::MIN)));
    assert_eq!(max, PureExpr::Int(i64::from(i16::MAX)));
}

#[test]
fn signed_bounds_32() {
    let (min, max) = signed_bounds_expr(32);
    assert_eq!(min, PureExpr::Int(i64::from(i32::MIN)));
    assert_eq!(max, PureExpr::Int(i64::from(i32::MAX)));
}

#[test]
fn signed_bounds_64_special_case() {
    let (min, max) = signed_bounds_expr(64);
    assert_eq!(min, PureExpr::Int(i64::MIN));
    assert_eq!(max, PureExpr::Int(i64::MAX));
}

#[test]
fn signed_bounds_literal_for_small_widths() {
    for bits in 1..=63 {
        let (min, max) = signed_bounds_expr(bits);
        let expected_min = -(1_i128 << (bits - 1));
        let expected_max = (1_i128 << (bits - 1)) - 1;
        match (&min, &max) {
            (PureExpr::Int(m), PureExpr::Int(x)) => {
                assert_eq!(
                    i128::from(*m),
                    expected_min,
                    "signed_bounds_expr({bits}) min"
                );
                assert_eq!(
                    i128::from(*x),
                    expected_max,
                    "signed_bounds_expr({bits}) max"
                );
            }
            _ => panic!("signed_bounds_expr({bits}) should return Int literals for bits<=63"),
        }
    }
}

#[test]
fn signed_bounds_128_symbolic_structure() {
    let (min, max) = signed_bounds_expr(128);
    // min = 0 - pow2(127)
    match &min {
        PureExpr::BinOp(l, BinOp::Sub, _) => {
            assert_eq!(**l, PureExpr::Int(0), "i128 min should be 0 - pow2(127)");
        }
        other => panic!("i128 min should be BinOp(0, Sub, ...), got {other:?}"),
    }
    // max = pow2(127) - 1
    match &max {
        PureExpr::BinOp(_, BinOp::Sub, r) => {
            assert_eq!(**r, PureExpr::Int(1), "i128 max should be pow2(127) - 1");
        }
        other => panic!("i128 max should be BinOp(..., Sub, 1), got {other:?}"),
    }
}

#[test]
fn signed_bounds_eval_standard_types() {
    // Verify eval matches Rust's actual bounds for types that fit in i128
    for bits in [8u32, 16, 32, 63] {
        let (min, max) = signed_bounds_expr(bits);
        let expected_min = -(1_i128 << (bits - 1));
        let expected_max = (1_i128 << (bits - 1)) - 1;
        assert_eq!(
            eval_i128(&min),
            expected_min,
            "signed_bounds_expr({bits}) min eval"
        );
        assert_eq!(
            eval_i128(&max),
            expected_max,
            "signed_bounds_expr({bits}) max eval"
        );
    }
}

// ── cross-function consistency ───────────────────────

#[test]
fn unsigned_max_equals_pow2_minus_one_for_evaluable_widths() {
    for bits in [1, 8, 16, 32, 63, 64] {
        let max_val = eval_i128(&unsigned_max_expr(bits));
        let pow2_val = eval_i128(&pow2_expr(bits));
        assert_eq!(
            max_val,
            pow2_val - 1,
            "unsigned_max_expr({bits}) should equal pow2_expr({bits}) - 1"
        );
    }
}

#[test]
fn signed_bounds_min_max_span_equals_pow2() {
    for bits in [8u32, 16, 32, 63] {
        let (min, max) = signed_bounds_expr(bits);
        let span = eval_i128(&max) - eval_i128(&min);
        let expected_span = eval_i128(&pow2_expr(bits)) - 1;
        assert_eq!(
            span, expected_span,
            "signed range for {bits}-bit should span 2^{bits} - 1"
        );
    }
}
