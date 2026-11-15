// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IEEE-754 float encoding: literals, the reserved `__trust_wp_ieee_*` calls
//! and the refusal of every other float operator.
//!
//! Validity is checked the way the verifier checks it: the NEGATION of the
//! claim is asserted and must be `Unsat`.

use ntest::timeout;
use trust_wp_core::formula::{
    ieee::{IeeeFn, IeeeOp},
    BinOp, ExprSort, FloatBits, FloatWidth, PureExpr, UnOp,
};

use super::*;

fn ieee(op: IeeeOp, width: FloatWidth, args: Vec<PureExpr>) -> PureExpr {
    logic_fn_call(&IeeeFn::new(op, width).name(), args)
}

fn f64_lit(v: f64) -> PureExpr {
    PureExpr::Float(FloatBits::from_f64(v))
}

fn f64_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(ExprSort::Float(FloatWidth::F64)))
}

fn f32_var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), Some(ExprSort::Float(FloatWidth::F32)))
}

fn not(e: PureExpr) -> PureExpr {
    PureExpr::UnOp(UnOp::Not, std::sync::Arc::new(e))
}

fn eq(l: PureExpr, r: PureExpr) -> PureExpr {
    PureExpr::BinOp(std::sync::Arc::new(l), BinOp::Eq, std::sync::Arc::new(r))
}

/// Assert `!claim`; `true` when the solver answers `Unsat` (the claim is valid).
/// The encoder is `Logic::All`, the logic verification selects for any goal
/// that mentions a float (`verify/setup/requirements.rs`).
fn valid(claim: &PureExpr) -> bool {
    let mut encoder = AYEncoder::new_all();
    let term = encoder
        .encode_pure(&not(claim.clone()))
        .expect("claim encodes");
    encoder.assert_term(term);
    matches!(encoder.check_sat(), ay_dpll::api::SolveResult::Unsat(_))
}

fn refused(expr: &PureExpr) -> bool {
    AYEncoder::new_all().encode_pure(expr).is_err()
}

#[test]
#[timeout(60000)]
fn a_float_literal_has_its_format_sort() {
    use ay_dpll::api::Sort;
    let mut encoder = AYEncoder::new_all();
    let wide = encoder.encode_pure(&f64_lit(1.5)).expect("f64 literal");
    assert_eq!(encoder.solver.get_sort(wide), Sort::FloatingPoint(11, 53));
    let narrow = encoder
        .encode_pure(&PureExpr::Float(FloatBits::from_f32(1.5)))
        .expect("f32 literal");
    assert_eq!(encoder.solver.get_sort(narrow), Sort::FloatingPoint(8, 24));
}

#[test]
#[timeout(60000)]
fn ieee_equality_is_not_reflexive_but_logical_equality_is() {
    let x = f64_var("x");
    let ieee_eq = ieee(IeeeOp::Eq, FloatWidth::F64, vec![x.clone(), x.clone()]);
    assert!(!valid(&ieee_eq), "x == x is false at NaN");
    let not_nan = not(ieee(IeeeOp::IsNan, FloatWidth::F64, vec![x.clone()]));
    let guarded = PureExpr::BinOp(
        std::sync::Arc::new(not_nan),
        BinOp::Implies,
        std::sync::Arc::new(ieee_eq),
    );
    assert!(valid(&guarded), "!x.is_nan() ==> x == x");
    assert!(
        valid(&eq(x.clone(), x)),
        "logical equality of a value with itself"
    );
}

#[test]
#[timeout(60000)]
fn signed_zeros_are_ieee_equal_and_logically_distinct() {
    let ieee_eq = ieee(
        IeeeOp::Eq,
        FloatWidth::F64,
        vec![f64_lit(0.0), f64_lit(-0.0)],
    );
    assert!(valid(&ieee_eq), "0.0 == -0.0 under IEEE-754");
    assert!(
        valid(&not(eq(f64_lit(0.0), f64_lit(-0.0)))),
        "+0 and -0 are two values"
    );
}

#[test]
#[timeout(60000)]
fn arithmetic_rounds_to_nearest_even() {
    let sum = ieee(
        IeeeOp::Add,
        FloatWidth::F64,
        vec![f64_lit(1.0e16), f64_lit(1.0)],
    );
    let absorbed = ieee(IeeeOp::Eq, FloatWidth::F64, vec![sum, f64_lit(1.0e16)]);
    assert!(valid(&absorbed), "1e16 + 1.0 rounds back to 1e16");
    let zero_div = ieee(
        IeeeOp::Div,
        FloatWidth::F64,
        vec![f64_lit(0.0), f64_lit(0.0)],
    );
    assert!(valid(&ieee(IeeeOp::IsNan, FloatWidth::F64, vec![zero_div])));
}

/// `as` between a float and an integer is an uninterpreted function of its
/// operand: deterministic (the same operand converts to the same value), and
/// nothing else is claimed — in particular no value is decided, right or wrong.
#[test]
#[timeout(60000)]
fn float_int_casts_are_functions_of_their_operand_and_nothing_more() {
    let to_u8 = |arg: PureExpr| {
        ieee(
            IeeeOp::ToInt {
                signed: false,
                bits: 8,
            },
            FloatWidth::F64,
            vec![arg],
        )
    };
    let x = f64_var("x");
    assert!(
        valid(&eq(to_u8(x.clone()), to_u8(x))),
        "a cast is deterministic"
    );
    assert!(!valid(&eq(to_u8(f64_lit(f64::NAN)), PureExpr::Int(0))));
    assert!(!valid(&eq(to_u8(f64_lit(300.0)), PureExpr::Int(0))));
    let from_i64 = |arg: PureExpr| {
        ieee(
            IeeeOp::FromInt {
                signed: true,
                bits: 64,
            },
            FloatWidth::F64,
            vec![arg],
        )
    };
    let n = PureExpr::Var("n".to_string(), Some(ExprSort::Int));
    assert!(valid(&eq(from_i64(n.clone()), from_i64(n))));
    assert!(!valid(&eq(from_i64(PureExpr::Int(2)), f64_lit(3.0))));
    assert!(
        refused(&from_i64(f64_lit(1.0))),
        "the integer operand must be an integer"
    );
}

#[test]
#[timeout(60000)]
fn narrowing_rounds_and_widening_is_exact() {
    let narrowed = ieee(
        IeeeOp::ToFloat(FloatWidth::F32),
        FloatWidth::F64,
        vec![f64_lit(0.1)],
    );
    assert!(valid(&eq(
        narrowed,
        PureExpr::Float(FloatBits::from_f32(0.1))
    )));
    let widened = ieee(
        IeeeOp::ToFloat(FloatWidth::F64),
        FloatWidth::F32,
        vec![PureExpr::Float(FloatBits::from_f32(0.1))],
    );
    assert!(valid(&eq(widened.clone(), f64_lit(f64::from(0.1_f32)))));
    assert!(
        !valid(&eq(widened, f64_lit(0.1))),
        "0.1f32 widened is not 0.1f64"
    );
}

#[test]
#[timeout(60000)]
fn a_float_under_any_other_operator_is_refused() {
    let x = f64_var("x");
    for op in [
        BinOp::Lt,
        BinOp::Le,
        BinOp::Add,
        BinOp::Mul,
        BinOp::Div,
        BinOp::Mod,
    ] {
        let expr = PureExpr::BinOp(
            std::sync::Arc::new(x.clone()),
            op,
            std::sync::Arc::new(f64_var("y")),
        );
        assert!(refused(&expr), "{op:?} over floats must be refused");
    }
    assert!(refused(&PureExpr::UnOp(
        UnOp::Neg,
        std::sync::Arc::new(x.clone())
    )));
    // Logical equality across two formats is not a relation on values.
    assert!(refused(&eq(x, f32_var("y"))));
}

#[test]
#[timeout(60000)]
fn an_ieee_operand_of_another_sort_is_refused() {
    let int_operand = ieee(
        IeeeOp::Eq,
        FloatWidth::F64,
        vec![
            PureExpr::Var("n".to_string(), Some(ExprSort::Int)),
            f64_lit(1.0),
        ],
    );
    assert!(refused(&int_operand));
    let wrong_format = ieee(
        IeeeOp::Lt,
        FloatWidth::F64,
        vec![f32_var("x"), f64_lit(1.0)],
    );
    assert!(refused(&wrong_format));
}

#[test]
#[timeout(60000)]
fn an_unsuffixed_literal_takes_its_peers_format_and_a_suffixed_one_keeps_its_own() {
    let x = f32_var("x");
    let exact = eq(
        x.clone(),
        PureExpr::Float(FloatBits::unsuffixed("0.5").unwrap()),
    );
    assert!(AYEncoder::new_all().encode_pure(&exact).is_ok());
    let tenth = eq(
        x.clone(),
        PureExpr::Float(FloatBits::unsuffixed("0.1").unwrap()),
    );
    assert!(AYEncoder::new_all().encode_pure(&tenth).is_ok());
    let wide = eq(x, PureExpr::Float(FloatBits::from_f64(0.1)));
    assert!(refused(&wide), "an f64 literal is never compared at f32");
}
