// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ntest::timeout;

use super::*;

// =========================================================================
// Float-to-int floor builtin (#1802)
// =========================================================================

/// Builtin floor dispatch returns Sort::Int for a positive finite input.
#[test]
#[timeout(30000)]
fn test_floor_builtin_positive_truncation() {
    use ay_dpll::api::{SolveResult, Sort};
    use trust_wp_core::formula::{
        internal::builtins::REAL_TO_INT_FLOOR_LOGIC_FN, FloatBits, PureExpr,
    };

    let mut encoder = AYEncoder::new();
    // floor(3.7) should equal 3
    let floor_call = logic_fn_call(
        REAL_TO_INT_FLOOR_LOGIC_FN,
        vec![PureExpr::Float(FloatBits::from_f64(3.7))],
    );
    let floor_term = encoder
        .encode_pure(&floor_call)
        .expect("floor builtin should encode");
    let sort = encoder.solver.get_sort(floor_term);
    assert_eq!(sort, Sort::Int, "floor should return Int sort");

    // Assert floor(3.7) == 3 and check satisfiability
    let three = encoder.solver.int_const(3);
    let eq = encoder.solver.eq(floor_term, three);
    encoder.assert_term(eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "floor(3.7) == 3 should be satisfiable"
    );
}

/// Negative truncation: floor(-3.7) == -4, so -floor(-3.7) == 4.
/// Truncation toward zero of -3.7 is -3 (not -4).
#[test]
#[timeout(30000)]
fn test_floor_builtin_negative_truncation() {
    use ay_dpll::api::SolveResult;
    use trust_wp_core::formula::{
        internal::builtins::REAL_TO_INT_FLOOR_LOGIC_FN, FloatBits, PureExpr,
    };

    let mut encoder = AYEncoder::new();
    // Build: -floor(-(-3.7)) = -floor(3.7) — wait, we want trunc_zero(-3.7)
    // trunc_zero(-3.7) = -floor(-(-3.7)) = -floor(3.7) = -3
    // Simpler: just test floor(-3.7) == -4
    let floor_neg = logic_fn_call(
        REAL_TO_INT_FLOOR_LOGIC_FN,
        vec![PureExpr::Float(FloatBits::from_f64(-3.7))],
    );
    let floor_term = encoder
        .encode_pure(&floor_neg)
        .expect("floor(-3.7) should encode");

    // floor(-3.7) should be -4 (floor rounds toward negative infinity)
    let neg_four = encoder.solver.int_const(-4);
    let eq = encoder.solver.eq(floor_term, neg_four);
    encoder.assert_term(eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "floor(-3.7) == -4 should be satisfiable"
    );
}

/// Sort inference for floor builtin should return Int without incrementing
/// the SortFallbackToIntFromLogicFn unsoundness counter.
#[test]
#[timeout(30000)]
fn test_floor_builtin_sort_inference_no_unsoundness() {
    use ay_dpll::api::Sort;
    use trust_wp_core::formula::{
        internal::builtins::REAL_TO_INT_FLOOR_LOGIC_FN, FloatBits, PureExpr,
    };

    let floor_call = logic_fn_call(
        REAL_TO_INT_FLOOR_LOGIC_FN,
        vec![PureExpr::Float(FloatBits::from_f64(1.0))],
    );
    let sort = crate::encoder::sort_context::infer_expr_sort(&floor_call);
    assert_eq!(sort, Sort::Int, "floor builtin should infer as Sort::Int");
}

/// Full float-to-int lowering with clamp: 200.7 as i8 should clamp to 127.
/// Exercises the complete PureExpr tree that `lower_float_to_int` produces,
/// verifying the encoder handles Let + Ite + floor + clamp end-to-end.
#[test]
#[timeout(30000)]
fn test_float_to_int_clamp_signed_overflow() {
    use ay_dpll::api::SolveResult;
    use trust_wp_core::formula::{
        internal::builtins::REAL_TO_INT_FLOOR_LOGIC_FN, BinOp, ExprSort, FloatBits, PureExpr, UnOp,
    };

    // Build the same tree that lower_float_to_int produces for i8 bounds.
    let x = PureExpr::Float(FloatBits::from_f64(200.7));
    let zero = PureExpr::Float(FloatBits::from_f64(0.0));
    let floor = |e| PureExpr::LogicFnCall {
        name: REAL_TO_INT_FLOOR_LOGIC_FN.to_string(),
        args: vec![e],
    };

    // trunc_zero(x) = ite(x >= 0, floor(x), -floor(-x))
    let trunc = PureExpr::Ite(
        Arc::new(PureExpr::BinOp(
            Arc::new(x.clone()),
            BinOp::Ge,
            Arc::new(zero),
        )),
        Arc::new(floor(x.clone())),
        Arc::new(PureExpr::UnOp(
            UnOp::Neg,
            Arc::new(floor(PureExpr::UnOp(UnOp::Neg, Arc::new(x)))),
        )),
    );

    let trunc_var = "__trust_wp_float_to_int_trunc".to_string();
    let trunc_ref = PureExpr::Var(trunc_var.clone(), Some(ExprSort::Int));
    let min = PureExpr::Int(-128);
    let max = PureExpr::Int(127);

    // clamp(t, min, max) = ite(t < min, min, ite(t > max, max, t))
    let clamp = PureExpr::Ite(
        Arc::new(PureExpr::BinOp(
            Arc::new(trunc_ref.clone()),
            BinOp::Lt,
            Arc::new(min.clone()),
        )),
        Arc::new(min),
        Arc::new(PureExpr::Ite(
            Arc::new(PureExpr::BinOp(
                Arc::new(trunc_ref.clone()),
                BinOp::Gt,
                Arc::new(max.clone()),
            )),
            Arc::new(max),
            Arc::new(trunc_ref),
        )),
    );

    let full_expr = PureExpr::Let {
        var: trunc_var,
        value: Arc::new(trunc),
        body: Arc::new(clamp),
    };

    let mut encoder = AYEncoder::new();
    let result = encoder
        .encode_pure(&full_expr)
        .expect("full float-to-int expression should encode");

    // 200.7 → trunc_zero = 200 → clamp(-128, 127) = 127
    let expected = encoder.solver.int_const(127);
    let eq = encoder.solver.eq(result, expected);
    encoder.assert_term(eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "200.7 as i8 should clamp to 127"
    );
}

/// Unsigned clamp: -5.3 as u8 should clamp to 0.
#[test]
#[timeout(30000)]
fn test_float_to_int_clamp_unsigned_negative() {
    use ay_dpll::api::SolveResult;
    use trust_wp_core::formula::{
        internal::builtins::REAL_TO_INT_FLOOR_LOGIC_FN, BinOp, ExprSort, FloatBits, PureExpr, UnOp,
    };

    let x = PureExpr::Float(FloatBits::from_f64(-5.3));
    let zero_f = PureExpr::Float(FloatBits::from_f64(0.0));
    let floor = |e| PureExpr::LogicFnCall {
        name: REAL_TO_INT_FLOOR_LOGIC_FN.to_string(),
        args: vec![e],
    };

    let trunc = PureExpr::Ite(
        Arc::new(PureExpr::BinOp(
            Arc::new(x.clone()),
            BinOp::Ge,
            Arc::new(zero_f),
        )),
        Arc::new(floor(x.clone())),
        Arc::new(PureExpr::UnOp(
            UnOp::Neg,
            Arc::new(floor(PureExpr::UnOp(UnOp::Neg, Arc::new(x)))),
        )),
    );

    let trunc_var = "__trust_wp_float_to_int_trunc".to_string();
    let trunc_ref = PureExpr::Var(trunc_var.clone(), Some(ExprSort::Int));
    let zero_i = PureExpr::Int(0);
    let max = PureExpr::Int(255);

    // unsigned clamp: ite(t < 0, 0, ite(t > 255, 255, t))
    let clamp = PureExpr::Ite(
        Arc::new(PureExpr::BinOp(
            Arc::new(trunc_ref.clone()),
            BinOp::Lt,
            Arc::new(zero_i.clone()),
        )),
        Arc::new(zero_i),
        Arc::new(PureExpr::Ite(
            Arc::new(PureExpr::BinOp(
                Arc::new(trunc_ref.clone()),
                BinOp::Gt,
                Arc::new(max.clone()),
            )),
            Arc::new(max),
            Arc::new(trunc_ref),
        )),
    );

    let full_expr = PureExpr::Let {
        var: trunc_var,
        value: Arc::new(trunc),
        body: Arc::new(clamp),
    };

    let mut encoder = AYEncoder::new();
    let result = encoder
        .encode_pure(&full_expr)
        .expect("full float-to-int expression should encode");

    // -5.3 → trunc_zero = -5 → clamp(0, 255) = 0
    let expected = encoder.solver.int_const(0);
    let eq = encoder.solver.eq(result, expected);
    encoder.assert_term(eq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "-5.3 as u8 should clamp to 0"
    );
}
