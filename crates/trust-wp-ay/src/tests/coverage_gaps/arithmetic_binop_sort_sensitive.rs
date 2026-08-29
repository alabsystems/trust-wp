// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort-sensitive regression tests for arithmetic and bitwise binops.

use ay_dpll::api::Sort;
use ntest::timeout;

use super::*;

/// Arithmetic operators with non-Int operands must coerce instead of panicking.
#[test]
#[timeout(30000)]
fn test_arithmetic_ops_non_int_sort_no_panic() {
    for op in [BinOp::Add, BinOp::Sub, BinOp::Mul] {
        let mut encoder = AYEncoder::new();
        let x = var_with_sort(
            "x",
            ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("X")),
        );
        let expr = binop(x.clone(), op, x);

        let result = encoder.encode_pure(&expr);
        assert!(
            result.is_ok(),
            "{op:?} on non-Int-sorted operands should encode without panic, got: {result:?}"
        );

        let term_sort = encoder.solver.get_sort(result.unwrap());
        assert_eq!(term_sort, Sort::Int, "{op:?} result must be Int-sorted");
    }
}

/// Div/Mod with non-Int operands must coerce and still collect nonzero obligations.
#[test]
#[timeout(30000)]
fn test_div_mod_non_int_sort_no_panic() {
    for op in [BinOp::Div, BinOp::Mod] {
        let mut encoder = AYEncoder::new();
        let x = var_with_sort(
            "x",
            ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("X")),
        );
        let expr = binop(x.clone(), op, x);

        let result = encoder.encode_pure(&expr);
        assert!(
            result.is_ok(),
            "{op:?} on non-Int-sorted operands should encode without panic, got: {result:?}"
        );

        let term_sort = encoder.solver.get_sort(result.unwrap());
        assert_eq!(term_sort, Sort::Int, "{op:?} result must be Int-sorted");
        assert_eq!(
            encoder.division_obligations_for_test().len(),
            1,
            "{op:?} should still record one nonzero-divisor obligation after coercion"
        );
    }
}

/// Bitwise UF fallback must coerce non-Int operands before `solver.apply()`.
#[test]
#[timeout(30000)]
fn test_bitwise_ops_non_int_sort_no_panic() {
    for op in [
        BinOp::Shl,
        BinOp::Shr,
        BinOp::BitAnd,
        BinOp::BitXor,
        BinOp::BitOr,
    ] {
        let mut encoder = AYEncoder::new();
        let x = var_with_sort(
            "x",
            ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("X")),
        );
        let expr = binop(x.clone(), op, x);

        let result = encoder.encode_pure(&expr);
        assert!(
            result.is_ok(),
            "{op:?} on non-Int-sorted operands should encode without panic, got: {result:?}"
        );

        let term_sort = encoder.solver.get_sort(result.unwrap());
        assert_eq!(term_sort, Sort::Int, "{op:?} result must be Int-sorted");
    }
}
