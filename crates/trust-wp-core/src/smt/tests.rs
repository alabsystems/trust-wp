// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for SMT encoding.

use std::sync::Arc;

use super::*;
use crate::formula::{BinOp, Formula, PureExpr, UnOp};

#[test]
fn test_expr_to_smt_int() {
    assert_eq!(expr_to_smt(&PureExpr::Int(42)), "42");
    assert_eq!(expr_to_smt(&PureExpr::Int(-42)), "(- 42)");
    assert_eq!(
        expr_to_smt(&PureExpr::Int(i64::MIN)),
        "(- 9223372036854775808)"
    );
}

#[test]
fn test_expr_to_smt_var() {
    assert_eq!(expr_to_smt(&PureExpr::Var("x".into(), None)), "x");
    assert_eq!(
        expr_to_smt(&PureExpr::Var("i32::MIN".into(), None)),
        "(- 2147483648)"
    );
}

#[test]
fn test_expr_to_smt_all_int_constants() {
    // Signed integer bounds
    assert_eq!(
        expr_to_smt(&PureExpr::Var("i8::MIN".into(), None)),
        "(- 128)"
    );
    assert_eq!(expr_to_smt(&PureExpr::Var("i8::MAX".into(), None)), "127");
    assert_eq!(
        expr_to_smt(&PureExpr::Var("i16::MIN".into(), None)),
        "(- 32768)"
    );
    assert_eq!(
        expr_to_smt(&PureExpr::Var("i16::MAX".into(), None)),
        "32767"
    );
    assert_eq!(
        expr_to_smt(&PureExpr::Var("i32::MAX".into(), None)),
        "2147483647"
    );
    assert_eq!(
        expr_to_smt(&PureExpr::Var("i64::MAX".into(), None)),
        "9223372036854775807"
    );
    // i128 bounds (arbitrary precision in SMT-LIB)
    assert_eq!(
        expr_to_smt(&PureExpr::Var("i128::MIN".into(), None)),
        "(- 170141183460469231731687303715884105728)"
    );
    assert_eq!(
        expr_to_smt(&PureExpr::Var("i128::MAX".into(), None)),
        "170141183460469231731687303715884105727"
    );

    // Unsigned integer bounds
    assert_eq!(expr_to_smt(&PureExpr::Var("u8::MIN".into(), None)), "0");
    assert_eq!(expr_to_smt(&PureExpr::Var("u8::MAX".into(), None)), "255");
    assert_eq!(
        expr_to_smt(&PureExpr::Var("u16::MAX".into(), None)),
        "65535"
    );
    assert_eq!(
        expr_to_smt(&PureExpr::Var("u32::MAX".into(), None)),
        "4294967295"
    );
    assert_eq!(
        expr_to_smt(&PureExpr::Var("u64::MAX".into(), None)),
        "18446744073709551615"
    );
    // u128 bounds
    assert_eq!(
        expr_to_smt(&PureExpr::Var("u128::MAX".into(), None)),
        "340282366920938463463374607431768211455"
    );

    // Platform-dependent (assuming 64-bit)
    assert_eq!(
        expr_to_smt(&PureExpr::Var("isize::MIN".into(), None)),
        "(- 9223372036854775808)"
    );
    assert_eq!(
        expr_to_smt(&PureExpr::Var("isize::MAX".into(), None)),
        "9223372036854775807"
    );
    assert_eq!(expr_to_smt(&PureExpr::Var("usize::MIN".into(), None)), "0");
    assert_eq!(
        expr_to_smt(&PureExpr::Var("usize::MAX".into(), None)),
        "18446744073709551615"
    );
}

#[test]
fn test_expr_to_smt_binop() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    assert_eq!(expr_to_smt(&expr), "(> x 0)");
}

#[test]
fn test_expr_to_smt_div() {
    // Division uses SMT-LIB integer division "div"
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), None)),
        BinOp::Div,
        Arc::new(PureExpr::Int(2)),
    );
    assert_eq!(expr_to_smt(&expr), "(div x 2)");
}

#[test]
fn test_expr_to_smt_mod() {
    // Modulo uses SMT-LIB "mod"
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".into(), None)),
        BinOp::Mod,
        Arc::new(PureExpr::Int(3)),
    );
    assert_eq!(expr_to_smt(&expr), "(mod n 3)");
}

#[test]
fn test_expr_to_smt_rem_trunc() {
    // SMT-LIB `mod` is Euclidean; the truncated (Rust signed `%`) remainder is
    // emitted as a toward-zero form derived from it (sign of dividend).
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".into(), None)),
        BinOp::RemTrunc,
        Arc::new(PureExpr::Int(3)),
    );
    assert_eq!(
        expr_to_smt(&expr),
        "(let ((_tw_a n) (_tw_b 3)) (let ((_tw_m (mod _tw_a _tw_b))) \
         (ite (>= _tw_a 0) _tw_m (ite (= _tw_m 0) 0 (- _tw_m (abs _tw_b))))))"
    );
}

#[test]
fn test_expr_to_smt_div_trunc() {
    // SMT-LIB `div` is Euclidean (floor); the truncated (Rust signed `/`)
    // quotient is emitted as a toward-zero form derived from it.
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), None)),
        BinOp::DivTrunc,
        Arc::new(PureExpr::Int(2)),
    );
    assert_eq!(
        expr_to_smt(&expr),
        "(let ((_tw_a x) (_tw_b 2)) (let ((_tw_q (div _tw_a _tw_b)) (_tw_r (mod _tw_a _tw_b))) \
         (ite (or (>= _tw_a 0) (= _tw_r 0)) _tw_q (ite (> _tw_b 0) (+ _tw_q 1) (- _tw_q 1)))))"
    );
}

#[test]
fn test_expr_to_smt_bitwise_uses_canonical_uf_names() {
    let cases = [
        (BinOp::Shl, "__trust_wp_bit_shl"),
        (BinOp::Shr, "__trust_wp_bit_shr"),
        (BinOp::BitAnd, "__trust_wp_bit_and"),
        (BinOp::BitXor, "__trust_wp_bit_xor"),
        (BinOp::BitOr, "__trust_wp_bit_or"),
    ];
    for (op, symbol) in cases {
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".into(), None)),
            op,
            Arc::new(PureExpr::Int(1)),
        );
        assert_eq!(expr_to_smt(&expr), format!("({symbol} x 1)"));
    }
}

fn build_deep_and_formula(depth: usize, leaf: Formula) -> Formula {
    let mut formula = leaf;
    for _ in 0..depth {
        formula = Formula::And(Arc::new(Formula::True), Arc::new(formula));
    }
    formula
}

#[test]
fn test_formula_to_smt_deep_formula_fails_closed() {
    let depth = super::encoding::MAX_RECURSION_DEPTH + 2;
    let formula = build_deep_and_formula(depth, Formula::Pure(PureExpr::Bool(true)));
    let smt = formula_to_smt(&formula);
    assert!(
        smt.contains("false"),
        "deep formula should fail closed at recursion limit: {smt}"
    );
}

#[test]
fn test_collect_vars_formula_deep_leaf_is_not_collected() {
    let depth = super::encoding::MAX_RECURSION_DEPTH + 2;
    let formula = build_deep_and_formula(
        depth,
        Formula::Pure(PureExpr::Var("deep_var".to_string(), None)),
    );
    let vars = collect_vars_formula(&formula);
    assert!(
        !vars.contains("deep_var"),
        "formula walker should stop before the deep leaf once recursion limit is exceeded: {vars:?}"
    );
}

#[test]
fn test_extract_footprint_names_deep_points_to_is_ignored() {
    let depth = super::encoding::MAX_RECURSION_DEPTH + 2;
    let formula = build_deep_and_formula(
        depth,
        Formula::PointsTo {
            location: crate::formula::Location("deep_loc".to_string()),
            value: crate::formula::Value::Unknown,
            permission: crate::formula::Permission::FULL,
        },
    );
    let footprint = extract_footprint_names(&formula);
    assert!(
        footprint.is_empty(),
        "footprint collection should stop before the deep points-to leaf: {footprint:?}"
    );
}

#[test]
fn test_needs_heap_preamble_deep_points_to_fails_closed() {
    let depth = super::encoding::MAX_RECURSION_DEPTH + 2;
    let formula = build_deep_and_formula(
        depth,
        Formula::PointsTo {
            location: crate::formula::Location("deep_loc".to_string()),
            value: crate::formula::Value::Unknown,
            permission: crate::formula::Permission::FULL,
        },
    );
    assert!(
        !needs_heap_preamble(&formula),
        "heap preamble detection should stop before the deep points-to leaf"
    );
}

#[test]
fn test_needs_bitwise_preamble_deep_leaf_fails_closed() {
    let depth = super::encoding::MAX_RECURSION_DEPTH + 2;
    let formula = build_deep_and_formula(
        depth,
        Formula::Pure(PureExpr::BinOp(
            Arc::new(PureExpr::Int(1)),
            BinOp::BitAnd,
            Arc::new(PureExpr::Int(2)),
        )),
    );
    assert!(
        !needs_bitwise_preamble(&formula),
        "bitwise preamble detection should stop before the deep leaf"
    );
}

#[test]
fn test_needs_seq_preamble_deep_leaf_fails_closed() {
    let depth = super::encoding::MAX_RECURSION_DEPTH + 2;
    let formula = build_deep_and_formula(
        depth,
        Formula::Pure(PureExpr::View(Arc::new(PureExpr::Var(
            "xs".to_string(),
            None,
        )))),
    );
    assert!(
        !needs_seq_preamble(&formula),
        "seq preamble detection should stop before the deep leaf"
    );
}

#[test]
fn test_expr_to_smt_complex() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".into(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".into(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    );
    assert_eq!(expr_to_smt(&expr), "(= result (+ x 1))");
}

#[test]
fn test_expr_to_smt_ite() {
    let expr = PureExpr::Ite(
        Arc::new(PureExpr::Var("c".into(), None)),
        Arc::new(PureExpr::Int(1)),
        Arc::new(PureExpr::Int(0)),
    );
    assert_eq!(expr_to_smt(&expr), "(ite c 1 0)");
}

#[test]
fn test_generate_vc_basic() {
    let mut smt_gen = SmtGenerator::new();

    // requires: x > 0
    let req = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );

    // ensures: result > x
    let ens = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".into(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Var("x".into(), None)),
    );

    // result = x + 1
    let result = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    smt_gen.generate_vc("increment", &[req], &[ens], Some(&result));

    let output = smt_gen.output();
    assert!(output.contains("(set-logic ALL)"));
    assert!(output.contains("(declare-const x Int)"));
    assert!(output.contains("(declare-const result Int)"));
    assert!(output.contains("(check-sat)"));
}

#[test]
fn test_generate_vc_includes_bitwise_preamble_when_needed() {
    let mut smt_gen = SmtGenerator::new();
    let req = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), None)),
        BinOp::BitAnd,
        Arc::new(PureExpr::Int(1)),
    );
    let ens = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".into(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".into(), None)),
            BinOp::Shl,
            Arc::new(PureExpr::Int(2)),
        )),
    );
    smt_gen.generate_vc("bit_ops", &[req], &[ens], None);
    let output = smt_gen.output();

    assert!(output.contains("; Bitwise UF declarations"));
    assert!(output.contains("(declare-fun __trust_wp_bit_and (Int Int) Int)"));
    assert!(output.contains("(declare-fun __trust_wp_bit_shl (Int Int) Int)"));
}

#[test]
fn test_generate_vc_multiple_ensures_uses_flat_nary_and() {
    let mut smt_gen = SmtGenerator::new();

    let ens1 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".into(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Var("x".into(), None)),
    );
    let ens2 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".into(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("y".into(), None)),
    );
    let ens3 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".into(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let result = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );

    smt_gen.generate_vc(
        "triple_bounds",
        &[],
        &[ens1.clone(), ens2.clone(), ens3.clone()],
        Some(&result),
    );

    let output = smt_gen.output();
    let expected_assert = format!(
        "(assert (not (and {} {} {})))",
        expr_to_smt(&ens1),
        expr_to_smt(&ens2),
        expr_to_smt(&ens3),
    );
    assert!(output.contains(&expected_assert));
    assert!(!output.contains("(and (and "));
}

#[test]
fn test_generate_vc_multiple_ensures_preserves_old_encoding() {
    let mut smt_gen = SmtGenerator::new();

    let ens1 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".into(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Old(Arc::new(PureExpr::Var("x".into(), None)))),
    );
    let ens2 = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".into(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    let ens3 = PureExpr::Var("ok".into(), None);

    smt_gen.generate_vc(
        "capture_old_value",
        &[],
        &[ens1.clone(), ens2.clone(), ens3.clone()],
        None,
    );

    let output = smt_gen.output();
    let expected_assert = format!(
        "(assert (not (and {} {} {})))",
        expr_to_smt(&ens1),
        expr_to_smt(&ens2),
        expr_to_smt(&ens3),
    );
    assert!(output.contains(&expected_assert));
    assert!(output.contains("old_x"));
    assert!(output.contains("(declare-const ok Bool)"));
}

#[test]
fn test_infer_var_sorts_bool() {
    // !valid should infer valid as Bool
    let expr = PureExpr::UnOp(UnOp::Not, Arc::new(PureExpr::Var("valid".into(), None)));
    let sorts = infer_var_sorts(&expr);
    assert_eq!(sorts.get("valid"), Some(&VarSort::Bool));
}

#[test]
fn test_infer_var_sorts_int() {
    // x > 0 should infer x as Int
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    let sorts = infer_var_sorts(&expr);
    assert_eq!(sorts.get("x"), Some(&VarSort::Int));
}

#[test]
fn test_infer_var_sorts_mixed() {
    // x > 0 && valid - x is Int, valid is Bool (used under &&)
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".into(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        )),
        BinOp::And,
        Arc::new(PureExpr::Var("valid".into(), None)),
    );
    let sorts = infer_var_sorts(&expr);
    assert_eq!(sorts.get("x"), Some(&VarSort::Int));
    assert_eq!(sorts.get("valid"), Some(&VarSort::Bool));
}

#[test]
fn test_generate_vc_bool_precondition() {
    // Test that #[requires(!valid)] declares valid as Bool
    let mut smt_gen = SmtGenerator::new();

    // requires: !valid
    let req = PureExpr::UnOp(UnOp::Not, Arc::new(PureExpr::Var("valid".into(), None)));

    // ensures: result
    let ens = PureExpr::Var("result".into(), None);

    smt_gen.generate_vc("check_invalid", &[req], &[ens], None);

    let output = smt_gen.output();
    assert!(output.contains("(declare-const valid Bool)"));
    // result is used directly as Bool in ensures context
    assert!(output.contains("(declare-const result Bool)"));
}

#[test]
fn test_infer_var_sorts_bool_comparison() {
    // Issue #24: flag == true should infer flag as Bool, not Int
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("flag".into(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Bool(true)),
    );
    let sorts = infer_var_sorts(&expr);
    // Bug: currently infers Int because Eq always uses Int
    // After fix: should be Bool since comparing with Bool literal
    assert_eq!(sorts.get("flag"), Some(&VarSort::Bool));
}

#[test]
fn test_infer_var_sorts_bool_ne_comparison() {
    // flag != false should infer flag as Bool
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("flag".into(), None)),
        BinOp::Ne,
        Arc::new(PureExpr::Bool(false)),
    );
    let sorts = infer_var_sorts(&expr);
    assert_eq!(sorts.get("flag"), Some(&VarSort::Bool));
}

#[test]
fn test_infer_var_sorts_multi_union() {
    let exprs = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".into(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
        PureExpr::UnOp(UnOp::Not, Arc::new(PureExpr::Var("valid".into(), None))),
    ];
    let sorts = infer_var_sorts_multi(&exprs);
    assert_eq!(sorts.get("x"), Some(&VarSort::Int));
    assert_eq!(sorts.get("valid"), Some(&VarSort::Bool));
}

#[test]
fn test_infer_var_sorts_multi_conflict_bool_then_int() {
    let exprs = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("flag".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Bool(true)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("flag".into(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
    ];
    let sorts = infer_var_sorts_multi(&exprs);
    assert_eq!(sorts.get("flag"), Some(&VarSort::Int));
}

#[test]
fn test_infer_var_sorts_multi_conflict_int_then_bool() {
    let exprs = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("flag".into(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("flag".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Bool(true)),
        ),
    ];
    let sorts = infer_var_sorts_multi(&exprs);
    assert_eq!(sorts.get("flag"), Some(&VarSort::Int));
}

#[test]
fn test_expr_to_smt_old() {
    // old(x) should become old_x
    let expr = PureExpr::Old(Arc::new(PureExpr::Var("x".into(), None)));
    assert_eq!(expr_to_smt(&expr), "old_x");
}

#[test]
fn test_expr_to_smt_old_const() {
    // old(i32::MIN) should keep constant value
    let expr = PureExpr::Old(Arc::new(PureExpr::Var("i32::MIN".into(), None)));
    assert_eq!(expr_to_smt(&expr), "(- 2147483648)");

    let expr = PureExpr::Old(Arc::new(PureExpr::Int(i64::MIN)));
    assert_eq!(expr_to_smt(&expr), "(- 9223372036854775808)");
}

#[test]
fn test_expr_to_smt_old_complex() {
    // old(x + y) should become (+ old_x old_y)
    let expr = PureExpr::Old(Arc::new(PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".into(), None)),
        BinOp::Add,
        Arc::new(PureExpr::Var("y".into(), None)),
    )));
    assert_eq!(expr_to_smt(&expr), "(+ old_x old_y)");
}

#[test]
fn test_expr_to_smt_old_nested_deref() {
    // old(*v + *w) should produce (+ old_v_current old_w_current)
    // Tests SmtContext::Old propagation through binary ops to derefs.
    let expr = PureExpr::Old(Arc::new(PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var("v".into(), None)))),
        BinOp::Add,
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var("w".into(), None)))),
    )));
    assert_eq!(expr_to_smt(&expr), "(+ old_v_current old_w_current)");
}

#[test]
fn test_expr_to_smt_old_nested_view() {
    // old(v@) should produce old_v_view
    // Tests SmtContext::Old propagation to view expressions.
    let expr = PureExpr::Old(Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
        "v".into(),
        None,
    )))));
    assert_eq!(expr_to_smt(&expr), "old_v_view");
}

#[test]
fn test_expr_to_smt_old_nested_final() {
    // old(^v) should produce old_v_final
    // Tests SmtContext::Old propagation to final/prophecy expressions.
    let expr = PureExpr::Old(Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
        "v".into(),
        None,
    )))));
    assert_eq!(expr_to_smt(&expr), "old_v_final");
}

#[test]
fn test_formula_to_smt_mut_borrow() {
    // MutBorrow { var: "v", current: x, final_val: x + 1, id: 3 }
    // Should produce: (and (= v_current x) (= v_final (+ x 1)) (= v_id 3))
    let formula = Formula::MutBorrow {
        var: "v".into(),
        current: Arc::new(PureExpr::Var("x".into(), None)),
        final_val: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".into(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
        id: Arc::new(PureExpr::Int(3)),
    };
    let smt = formula_to_smt(&formula);
    assert_eq!(smt, "(and (= v_current x) (= v_final (+ x 1)) (= v_id 3))");
}

#[test]
fn test_collect_vars_mut_borrow() {
    let formula = Formula::MutBorrow {
        var: "v".into(),
        current: Arc::new(PureExpr::Var("x".into(), None)),
        final_val: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("y".into(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
        id: Arc::new(PureExpr::Var("z".into(), None)),
    };
    let vars = collect_vars_formula(&formula);
    // Should contain: v_current, v_final, v_id, x, y, z
    assert!(vars.contains("v_current"));
    assert!(vars.contains("v_final"));
    assert!(vars.contains("v_id"));
    assert!(vars.contains("x"));
    assert!(vars.contains("y"));
    assert!(vars.contains("z"));
}

// Tests for Deref and Final SMT encoding (Part of #13)
mod deref_final_tests {
    use super::*;

    #[test]
    fn test_expr_to_smt_deref() {
        // *v should become v_current
        let expr = PureExpr::Deref(Arc::new(PureExpr::Var("v".into(), None)));
        assert_eq!(expr_to_smt(&expr), "v_current");
    }

    #[test]
    fn test_expr_to_smt_final() {
        // ^v should become v_final
        let expr = PureExpr::Final(Arc::new(PureExpr::Var("v".into(), None)));
        assert_eq!(expr_to_smt(&expr), "v_final");
    }

    #[test]
    fn test_expr_to_smt_deref_comparison() {
        // *v > 0 should become (> v_current 0)
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var("v".into(), None)))),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        );
        assert_eq!(expr_to_smt(&expr), "(> v_current 0)");
    }

    #[test]
    fn test_expr_to_smt_final_comparison() {
        // ^v >= 0 should become (>= v_final 0)
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var("v".into(), None)))),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        );
        assert_eq!(expr_to_smt(&expr), "(>= v_final 0)");
    }

    #[test]
    fn test_expr_to_smt_final_equals_old_deref() {
        // ^v == old(*v) + 1 typical increment postcondition
        // In RustHorn encoding: old(*v) = *v = v_current
        // Should become: (= v_final (+ v_current 1))
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var("v".into(), None)))),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(
                    PureExpr::Var("v".into(), None),
                ))))),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        );
        assert_eq!(expr_to_smt(&expr), "(= v_final (+ v_current 1))");
    }

    #[test]
    fn test_collect_vars_deref() {
        // *v should add v_current to variables
        let expr = PureExpr::Deref(Arc::new(PureExpr::Var("v".into(), None)));
        let vars = collect_vars_expr(&expr);
        assert!(vars.contains("v_current"));
        assert!(!vars.contains("v"));
    }

    #[test]
    fn test_collect_vars_final() {
        // ^v should add v_final to variables
        let expr = PureExpr::Final(Arc::new(PureExpr::Var("v".into(), None)));
        let vars = collect_vars_expr(&expr);
        assert!(vars.contains("v_final"));
        assert!(!vars.contains("v"));
    }

    #[test]
    fn test_collect_vars_old_deref() {
        // old(*v) should add v_current to variables (RustHorn: old(*v) = *v = v_current)
        let expr = PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "v".into(),
            None,
        )))));
        let vars = collect_vars_expr(&expr);
        assert!(vars.contains("v_current"));
        assert!(!vars.contains("old_v_current"));
    }
}

// Tests for View and MethodCall SMT encoding (Part of #110)
mod view_method_tests {
    use super::*;

    #[test]
    fn test_expr_to_smt_view_simple() {
        // self@ should become self_view
        let expr = PureExpr::View(Arc::new(PureExpr::Var("self".into(), None)));
        assert_eq!(expr_to_smt(&expr), "self_view");
    }

    #[test]
    fn test_expr_to_smt_view_deref() {
        // (*v)@ should become v_current_view
        let expr = PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "v".into(),
            None,
        )))));
        assert_eq!(expr_to_smt(&expr), "v_current_view");
    }

    #[test]
    fn test_expr_to_smt_view_final() {
        // (^v)@ should become v_final_view
        let expr = PureExpr::View(Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "v".into(),
            None,
        )))));
        assert_eq!(expr_to_smt(&expr), "v_final_view");
    }

    #[test]
    fn test_expr_to_smt_method_call_no_args() {
        // self@.len() should become (seq_len self_view)
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var("self".into(), None)))),
            method: "len".into(),
            args: vec![],
        };
        assert_eq!(expr_to_smt(&expr), "(seq_len self_view)");
    }

    #[test]
    fn test_expr_to_smt_method_call_with_args() {
        // self@.index_logic(i) should become (seq_index_logic self_view i)
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var("self".into(), None)))),
            method: "index_logic".into(),
            args: vec![PureExpr::Var("i".into(), None)],
        };
        assert_eq!(expr_to_smt(&expr), "(seq_index_logic self_view i)");
    }

    #[test]
    fn test_expr_to_smt_method_call_push_back() {
        // self@.push_back(value) should become (seq_push_back self_view value)
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var("self".into(), None)))),
            method: "push_back".into(),
            args: vec![PureExpr::Var("value".into(), None)],
        };
        assert_eq!(expr_to_smt(&expr), "(seq_push_back self_view value)");
    }

    #[test]
    fn test_collect_vars_view_simple() {
        // self@ should add self_view to variables
        let expr = PureExpr::View(Arc::new(PureExpr::Var("self".into(), None)));
        let vars = collect_vars_expr(&expr);
        assert!(vars.contains("self_view"));
        assert!(!vars.contains("self"));
    }

    #[test]
    fn test_collect_vars_view_deref() {
        // (*v)@ should add v_current_view to variables
        let expr = PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "v".into(),
            None,
        )))));
        let vars = collect_vars_expr(&expr);
        assert!(vars.contains("v_current_view"));
        assert!(!vars.contains("v_current")); // Not just v_current
    }

    #[test]
    fn test_collect_vars_view_final() {
        // (^v)@ should add v_final_view to variables
        let expr = PureExpr::View(Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "v".into(),
            None,
        )))));
        let vars = collect_vars_expr(&expr);
        assert!(vars.contains("v_final_view"));
        assert!(!vars.contains("v_final")); // Not just v_final
    }

    #[test]
    fn test_collect_vars_method_call() {
        // self@.len() should collect from receiver (self_view)
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var("self".into(), None)))),
            method: "len".into(),
            args: vec![],
        };
        let vars = collect_vars_expr(&expr);
        assert!(vars.contains("self_view"));
    }

    #[test]
    fn test_collect_vars_method_call_with_args() {
        // self@.index_logic(i) should collect self_view and i
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var("self".into(), None)))),
            method: "index_logic".into(),
            args: vec![PureExpr::Var("i".into(), None)],
        };
        let vars = collect_vars_expr(&expr);
        assert!(vars.contains("self_view"));
        assert!(vars.contains("i"));
    }

    #[test]
    fn test_expr_to_smt_method_unknown() {
        // Unknown method names should be passed through as-is
        // This allows extending the spec language without modifying the encoder
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var("self".into(), None)))),
            method: "custom_method".into(),
            args: vec![PureExpr::Var("x".into(), None)],
        };
        assert_eq!(expr_to_smt(&expr), "(custom_method self_view x)");
    }

    #[test]
    fn test_expr_to_smt_implies() {
        // p ==> q should become (=> p q)
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("p".into(), None)),
            BinOp::Implies,
            Arc::new(PureExpr::Var("q".into(), None)),
        );
        assert_eq!(expr_to_smt(&expr), "(=> p q)");
    }

    #[test]
    fn test_expr_to_smt_implies_complex() {
        // (x > 0) ==> (y > 0) should become (=> (> x 0) (> y 0))
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".into(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            )),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("y".into(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            )),
        );
        assert_eq!(expr_to_smt(&expr), "(=> (> x 0) (> y 0))");
    }

    #[test]
    fn test_infer_var_sorts_implies() {
        // Variables in p ==> q should be inferred as Bool
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("p".into(), None)),
            BinOp::Implies,
            Arc::new(PureExpr::Var("q".into(), None)),
        );
        let sorts = infer_var_sorts(&expr);
        assert_eq!(sorts.get("p"), Some(&VarSort::Bool));
        assert_eq!(sorts.get("q"), Some(&VarSort::Bool));
    }

    #[test]
    fn test_expr_to_smt_match_simple() {
        use crate::formula::{MatchArm, Pattern};

        // match x { 0 => false, _ => true }
        // Should encode as: (ite (= x 0) false true)
        let expr = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("x".into(), None)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Literal(PureExpr::Int(0)),
                    body: PureExpr::Bool(false),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    body: PureExpr::Bool(true),
                },
            ],
        };
        assert_eq!(expr_to_smt(&expr), "(ite (= x 0) false true)");
    }

    #[test]
    fn test_expr_to_smt_match_option() {
        use crate::formula::{MatchArm, Pattern};

        // match opt { Some(v) => v, None => 0 }
        // Should encode as: (ite (is_some opt) v 0)
        let expr = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("opt".into(), None)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".into(),
                        inner: Some(Box::new(Pattern::Binding("v".into()))),
                    },
                    body: PureExpr::Var("v".into(), None),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".into(),
                        inner: None,
                    },
                    body: PureExpr::Int(0),
                },
            ],
        };
        // Note: Currently binding 'v' is not substituted - known limitation
        assert_eq!(expr_to_smt(&expr), "(ite (is_some opt) v 0)");
    }
}

mod logic_fn_tests {
    use super::*;

    #[test]
    fn test_expr_to_smt_logic_fn_call() {
        let expr = PureExpr::LogicFnCall {
            name: "crate::specs::max".into(),
            args: vec![
                PureExpr::Var("x".into(), None),
                PureExpr::Var("y".into(), None),
            ],
        };
        assert_eq!(expr_to_smt(&expr), "(logic_crate_P__P_specs_P__P_max x y)");
    }

    #[test]
    fn test_expr_to_smt_logic_fn_call_nullary() {
        let expr = PureExpr::LogicFnCall {
            name: "const_val".into(),
            args: vec![],
        };
        assert_eq!(expr_to_smt(&expr), "(logic_const__val)");
    }
}

mod quantifier_tests {
    use super::*;

    #[test]
    fn test_expr_to_smt_forall() {
        let expr = PureExpr::Forall {
            var: "i".into(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".into(), None)),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )),
            triggers: vec![],
        };
        assert_eq!(expr_to_smt(&expr), "(forall ((i Int)) (>= i 0))");
    }

    #[test]
    fn test_expr_to_smt_exists() {
        let expr = PureExpr::Exists {
            var: "j".into(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("j".into(), None)),
                BinOp::Lt,
                Arc::new(PureExpr::Int(10)),
            )),
            triggers: vec![],
        };
        assert_eq!(expr_to_smt(&expr), "(exists ((j Int)) (< j 10))");
    }

    // Part of #228: Trigger/pattern encoding tests
    #[test]
    fn test_expr_to_smt_forall_with_single_trigger() {
        // forall<i: Int> #[trigger(f(i))] i >= 0
        let expr = PureExpr::Forall {
            var: "i".into(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".into(), None)),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )),
            triggers: vec![vec![PureExpr::LogicFnCall {
                name: "f".into(),
                args: vec![PureExpr::Var("i".into(), None)],
            }]],
        };
        let smt = expr_to_smt(&expr);
        assert!(smt.contains(":pattern"), "Should emit :pattern annotation");
        // Logic function calls are prefixed with 'logic_' in SMT encoding
        assert!(
            smt.contains("(logic_f i)"),
            "Should encode trigger expression: {smt}"
        );
    }

    #[test]
    fn test_expr_to_smt_forall_with_multi_trigger() {
        // forall<i: Int> #[trigger(f(i), g(i))] body
        // Multi-trigger: both f(i) AND g(i) must match
        let expr = PureExpr::Forall {
            var: "i".into(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".into(), None)),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )),
            triggers: vec![vec![
                PureExpr::LogicFnCall {
                    name: "f".into(),
                    args: vec![PureExpr::Var("i".into(), None)],
                },
                PureExpr::LogicFnCall {
                    name: "g".into(),
                    args: vec![PureExpr::Var("i".into(), None)],
                },
            ]],
        };
        let smt = expr_to_smt(&expr);
        // Logic function calls are prefixed with 'logic_' in SMT encoding
        assert!(
            smt.contains(":pattern ((logic_f i) (logic_g i))"),
            "Multi-trigger should have multiple expressions in one pattern: {smt}"
        );
    }

    #[test]
    fn test_expr_to_smt_forall_with_multiple_trigger_groups() {
        // forall<i: Int> #[trigger(f(i))] #[trigger(g(i))] body
        // Two alternative triggers: f(i) OR g(i) can instantiate
        let expr = PureExpr::Forall {
            var: "i".into(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".into(), None)),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )),
            triggers: vec![
                vec![PureExpr::LogicFnCall {
                    name: "f".into(),
                    args: vec![PureExpr::Var("i".into(), None)],
                }],
                vec![PureExpr::LogicFnCall {
                    name: "g".into(),
                    args: vec![PureExpr::Var("i".into(), None)],
                }],
            ],
        };
        let smt = expr_to_smt(&expr);
        // Multiple :pattern annotations for alternative triggers
        let pattern_count = smt.matches(":pattern").count();
        assert_eq!(
            pattern_count, 2,
            "Should have two :pattern annotations for two trigger groups: {smt}"
        );
    }

    // Part of #228: Roundtrip test - parse contract string and encode to SMT
    #[test]
    fn test_trigger_roundtrip_parse_to_smt() {
        use crate::contract_parser::parse_contract;

        // Parse a quantifier with trigger annotation
        let input = "forall<i: Int> #[trigger(f(i))] i >= 0";
        let expr = parse_contract(input).expect("should parse");

        // Encode to SMT
        let smt = expr_to_smt(&expr);

        // Verify SMT output structure
        assert!(smt.starts_with("(forall"), "Should be forall: {smt}");
        assert!(smt.contains("((i Int))"), "Should have Int binding: {smt}");
        assert!(
            smt.contains(":pattern"),
            "Should have trigger pattern: {smt}"
        );
        assert!(
            smt.contains("(logic_f i)"),
            "Trigger should encode logic fn call: {smt}"
        );
    }

    #[test]
    fn test_trigger_roundtrip_multi_expr() {
        use crate::contract_parser::parse_contract;

        // Parse with multi-expression trigger (both exprs in same trigger)
        let input = "forall<i: Int> #[trigger(f(i), g(i))] i >= 0";
        let expr = parse_contract(input).expect("should parse");

        let smt = expr_to_smt(&expr);

        // Multi-trigger should have both expressions in one pattern
        assert!(
            smt.contains(":pattern ((logic_f i) (logic_g i))"),
            "Multi-trigger pattern: {smt}"
        );
    }

    #[test]
    fn test_trigger_roundtrip_multiple_groups() {
        use crate::contract_parser::parse_contract;

        // Parse with multiple trigger groups (alternatives)
        let input = "forall<i: Int> #[trigger(f(i))] #[trigger(g(i))] i >= 0";
        let expr = parse_contract(input).expect("should parse");

        let smt = expr_to_smt(&expr);

        // Should have two separate :pattern annotations
        let pattern_count = smt.matches(":pattern").count();
        assert_eq!(pattern_count, 2, "Two trigger groups: {smt}");
    }
}

// Tests for separation logic formula encoding (Part of #75)
mod sep_logic_encoding_tests {
    use super::*;

    #[test]
    fn test_formula_to_smt_points_to_known_value() {
        // PointsTo with known value: x ↦ 42
        use crate::formula::{Location, Permission, Value};
        let formula = Formula::PointsTo {
            location: Location("x".to_string()),
            value: Value::Expr(PureExpr::Int(42)),
            permission: Permission::FULL,
        };
        let smt = formula_to_smt(&formula);
        // Should encode: (and (select heap_domain x) (>= (select heap_perms x) PERM_SCALE) (= (select heap_contents x) 42))
        assert!(smt.contains("heap_domain"), "Should reference heap_domain");
        assert!(smt.contains("heap_perms"), "Should reference heap_perms");
        assert!(
            smt.contains("heap_contents"),
            "Should reference heap_contents"
        );
        assert!(smt.contains("42"), "Should contain the value 42");
        let full_scaled = Permission::PERM_SCALE.to_string();
        assert!(
            smt.contains(&full_scaled),
            "Full permission = {full_scaled}"
        );
    }

    #[test]
    fn test_formula_to_smt_points_to_unknown_value() {
        // PointsTo with unknown value: x ↦ ?
        use crate::formula::{Location, Permission, Value};
        let formula = Formula::PointsTo {
            location: Location("ptr".to_string()),
            value: Value::Unknown,
            permission: Permission::HALF,
        };
        let smt = formula_to_smt(&formula);
        // Should encode with true for value constraint
        assert!(smt.contains("heap_domain"), "Should reference heap_domain");
        let half_scaled = Permission::HALF.scaled_value().to_string();
        assert!(
            smt.contains(&half_scaled),
            "Half permission = {half_scaled}"
        );
        assert!(smt.contains("true"), "Unknown value = true");
    }

    #[test]
    fn test_formula_to_smt_sep_conj_pure() {
        // SepConj with pure formulas: true * true = (and true true)
        let formula = Formula::SepConj(Arc::new(Formula::True), Arc::new(Formula::True));
        let smt = formula_to_smt(&formula);
        assert_eq!(smt, "(and true true)");
    }

    #[test]
    fn test_formula_to_smt_sep_conj_with_disjointness() {
        // SepConj with heap formulas: (x ↦ 1) * (y ↦ 2)
        // Should generate disjointness constraint x != y
        use crate::formula::{Location, Permission, Value};
        let left = Formula::PointsTo {
            location: Location("x".to_string()),
            value: Value::Expr(PureExpr::Int(1)),
            permission: Permission::FULL,
        };
        let right = Formula::PointsTo {
            location: Location("y".to_string()),
            value: Value::Expr(PureExpr::Int(2)),
            permission: Permission::FULL,
        };
        let formula = Formula::SepConj(Arc::new(left), Arc::new(right));
        let smt = formula_to_smt(&formula);
        // Should contain disjointness: (not (= x y))
        assert!(
            smt.contains("(not (= x y))"),
            "Should assert x != y for disjointness"
        );
    }

    #[test]
    fn test_formula_to_smt_sep_conj_mixed() {
        // SepConj: pure * heap = just conjunction (no disjointness needed)
        use crate::formula::{Location, Permission, Value};
        let pure = Formula::Pure(PureExpr::BinOp(
            Arc::new(PureExpr::Var("n".to_string(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ));
        let heap = Formula::PointsTo {
            location: Location("x".to_string()),
            value: Value::Expr(PureExpr::Var("n".to_string(), None)),
            permission: Permission::FULL,
        };
        let formula = Formula::SepConj(Arc::new(pure), Arc::new(heap));
        let smt = formula_to_smt(&formula);
        // Should be conjunction without disjointness (pure has no footprint)
        assert!(smt.contains("(> n 0)"), "Should contain pure formula");
        assert!(smt.contains("heap_contents"), "Should contain heap formula");
        // Should NOT contain disjointness since pure has empty footprint
        assert!(
            !smt.contains("(not (="),
            "Should not have disjointness for pure * heap"
        );
    }

    #[test]
    fn test_formula_to_smt_magic_wand() {
        // MagicWand encoding: P -* Q encoded as implication
        let formula = Formula::MagicWand(Arc::new(Formula::True), Arc::new(Formula::True));
        let smt = formula_to_smt(&formula);
        assert_eq!(smt, "(=> true true)");
    }

    #[test]
    fn test_formula_to_smt_magic_wand_with_vars() {
        // MagicWand: (x > 0) -* (y > 0) encodes as (x > 0) → (y > 0)
        let formula = Formula::MagicWand(
            Arc::new(Formula::Pure(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            ))),
            Arc::new(Formula::Pure(PureExpr::BinOp(
                Arc::new(PureExpr::Var("y".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            ))),
        );
        let smt = formula_to_smt(&formula);
        assert_eq!(smt, "(=> (> x 0) (> y 0))");
    }

    #[test]
    fn test_formula_to_smt_exists() {
        // Exists is supported in SMT-LIB2 output
        let formula = Formula::Exists {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(Formula::Pure(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            ))),
            triggers: vec![],
        };
        let smt = formula_to_smt(&formula);
        assert_eq!(smt, "(exists ((x Int)) (> x 0))");
    }

    #[test]
    fn test_formula_to_smt_forall() {
        // Forall is supported in SMT-LIB2 output
        let formula = Formula::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(Formula::Pure(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            ))),
            triggers: vec![],
        };
        let smt = formula_to_smt(&formula);
        assert_eq!(smt, "(forall ((x Int)) (>= x 0))");
    }

    #[test]
    fn test_generate_heap_preamble() {
        let preamble = generate_heap_preamble();
        assert!(preamble.contains("heap_contents"));
        assert!(preamble.contains("heap_domain"));
        assert!(preamble.contains("heap_perms"));
        assert!(preamble.contains("Array Int"));
    }

    #[test]
    fn test_needs_heap_preamble_points_to() {
        use crate::formula::{Location, Permission, Value};
        let formula = Formula::PointsTo {
            location: Location("x".to_string()),
            value: Value::Unknown,
            permission: Permission::FULL,
        };
        assert!(needs_heap_preamble(&formula));
    }

    #[test]
    fn test_needs_heap_preamble_pure() {
        let formula = Formula::Pure(PureExpr::Bool(true));
        assert!(!needs_heap_preamble(&formula));
    }

    #[test]
    fn test_needs_heap_preamble_nested() {
        use crate::formula::{Location, Permission, Value};
        let inner = Formula::PointsTo {
            location: Location("x".to_string()),
            value: Value::Unknown,
            permission: Permission::FULL,
        };
        let formula = Formula::And(Arc::new(Formula::True), Arc::new(inner));
        assert!(needs_heap_preamble(&formula));
    }

    #[test]
    fn test_extract_footprint_names() {
        use crate::formula::{Location, Permission, Value};
        let left = Formula::PointsTo {
            location: Location("a".to_string()),
            value: Value::Unknown,
            permission: Permission::FULL,
        };
        let right = Formula::PointsTo {
            location: Location("b".to_string()),
            value: Value::Unknown,
            permission: Permission::FULL,
        };
        let formula = Formula::SepConj(Arc::new(left), Arc::new(right));
        let footprint = extract_footprint_names(&formula);
        assert_eq!(footprint, vec!["a", "b"]);
    }

    #[test]
    fn test_extract_footprint_names_empty_for_pure() {
        let formula = Formula::Pure(PureExpr::Bool(true));
        let footprint = extract_footprint_names(&formula);
        assert!(footprint.is_empty());
    }

    #[test]
    fn test_extract_footprint_names_deduplicates() {
        // If same location appears twice, should only appear once in footprint
        use crate::formula::{Location, Permission, Value};
        let first = Formula::PointsTo {
            location: Location("x".to_string()),
            value: Value::Expr(PureExpr::Int(1)),
            permission: Permission::FULL,
        };
        let second = Formula::PointsTo {
            location: Location("x".to_string()), // Same location
            value: Value::Expr(PureExpr::Int(2)),
            permission: Permission::HALF,
        };
        let formula = Formula::And(Arc::new(first), Arc::new(second));
        let footprint = extract_footprint_names(&formula);
        // Should deduplicate
        assert_eq!(footprint, vec!["x"]);
    }

    #[test]
    fn test_formula_to_smt_sep_conj_nested() {
        // Nested SepConj: (x ↦ 1) * ((y ↦ 2) * (z ↦ 3))
        // Should generate pairwise disjointness for all three locations
        use crate::formula::{Location, Permission, Value};
        let x = Formula::PointsTo {
            location: Location("x".to_string()),
            value: Value::Expr(PureExpr::Int(1)),
            permission: Permission::FULL,
        };
        let y = Formula::PointsTo {
            location: Location("y".to_string()),
            value: Value::Expr(PureExpr::Int(2)),
            permission: Permission::FULL,
        };
        let z = Formula::PointsTo {
            location: Location("z".to_string()),
            value: Value::Expr(PureExpr::Int(3)),
            permission: Permission::FULL,
        };
        // ((y ↦ 2) * (z ↦ 3))
        let inner = Formula::SepConj(Arc::new(y), Arc::new(z));
        // (x ↦ 1) * inner
        let formula = Formula::SepConj(Arc::new(x), Arc::new(inner));
        let smt = formula_to_smt(&formula);

        // Outer SepConj: cross-pair disjointness between left={x} and right={y,z}
        assert!(
            smt.contains("(not (= x y))"),
            "x should be disjoint from y: {smt}"
        );
        assert!(
            smt.contains("(not (= x z))"),
            "x should be disjoint from z: {smt}"
        );
        // Inner SepConj: y must be disjoint from z
        assert!(
            smt.contains("(not (= y z))"),
            "y should be disjoint from z: {smt}"
        );
    }

    /// Regression test for #449: `SepConj` with And inside one side.
    ///
    /// (x ↦ 1) * ((y ↦ 2) ∧ (z ↦ 3))
    ///
    /// The `*` requires only cross-pair disjointness: x ≠ y and x ≠ z.
    /// It must NOT assert y ≠ z — that would be semantically incorrect
    /// because the `∧` (not `*`) on the right side allows aliasing y = z.
    #[test]
    fn test_formula_to_smt_sep_conj_and_inside_no_intra_distinct() {
        use crate::formula::{Location, Permission, Value};
        let x = Formula::PointsTo {
            location: Location("x".to_string()),
            value: Value::Expr(PureExpr::Int(1)),
            permission: Permission::FULL,
        };
        let y = Formula::PointsTo {
            location: Location("y".to_string()),
            value: Value::Expr(PureExpr::Int(2)),
            permission: Permission::FULL,
        };
        let z = Formula::PointsTo {
            location: Location("z".to_string()),
            value: Value::Expr(PureExpr::Int(3)),
            permission: Permission::FULL,
        };
        // Right side uses And (not SepConj): (y ↦ 2) ∧ (z ↦ 3)
        let rhs = Formula::And(Arc::new(y), Arc::new(z));
        // (x ↦ 1) * ((y ↦ 2) ∧ (z ↦ 3))
        let formula = Formula::SepConj(Arc::new(x), Arc::new(rhs));
        let smt = formula_to_smt(&formula);

        // Cross-pair disjointness: x ≠ y, x ≠ z
        assert!(
            smt.contains("(not (= x y))"),
            "cross-pair: x should be disjoint from y: {smt}"
        );
        assert!(
            smt.contains("(not (= x z))"),
            "cross-pair: x should be disjoint from z: {smt}"
        );
        // Must NOT contain y ≠ z — And allows aliasing within one side of *
        assert!(
            !smt.contains("(not (= y z))"),
            "intra-side y ≠ z should NOT be asserted (And allows aliasing): {smt}"
        );
        assert!(
            !smt.contains("(distinct"),
            "should not use distinct (would add intra-side constraints): {smt}"
        );
    }

    // Note: test_encode_points_to_zero_denominator was removed because
    // Permission now uses NonZeroU32 for denominator, making zero
    // denominators impossible at the type level. (#139)

    // Tests for Seq preamble (Part of #111)
    #[test]
    fn test_generate_seq_preamble() {
        let preamble = generate_seq_preamble();
        // Check sort declaration
        assert!(
            preamble.contains("(declare-sort Seq 0)"),
            "Should declare Seq sort"
        );
        // Check function declarations
        assert!(preamble.contains("seq_len"), "Should declare seq_len");
        assert!(
            preamble.contains("seq_index_logic"),
            "Should declare seq_index_logic"
        );
        assert!(
            preamble.contains("seq_push_back"),
            "Should declare seq_push_back"
        );
        assert!(
            preamble.contains("seq_empty"),
            "Should declare seq_empty constant"
        );
        // Check axioms
        assert!(
            preamble.contains("(>= (seq_len s) 0)"),
            "Should have non-negative length axiom"
        );
        assert!(
            preamble.contains("(= (seq_len seq_empty) 0)"),
            "Should have empty length axiom"
        );
    }

    #[test]
    fn test_generate_bitwise_preamble() {
        let preamble = generate_bitwise_preamble();
        for symbol in [
            "__trust_wp_bit_shl",
            "__trust_wp_bit_shr",
            "__trust_wp_bit_and",
            "__trust_wp_bit_xor",
            "__trust_wp_bit_or",
        ] {
            assert!(
                preamble.contains(&format!("(declare-fun {symbol} (Int Int) Int)")),
                "Missing bitwise declaration for {symbol}"
            );
        }
    }

    #[test]
    fn test_needs_bitwise_preamble() {
        let formula = Formula::And(
            Arc::new(Formula::Pure(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".into(), None)),
                BinOp::BitOr,
                Arc::new(PureExpr::Var("y".into(), None)),
            ))),
            Arc::new(Formula::Pure(PureExpr::BinOp(
                Arc::new(PureExpr::Var("z".into(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            ))),
        );
        assert!(needs_bitwise_preamble(&formula));
        assert!(!needs_bitwise_preamble(&Formula::Pure(PureExpr::BinOp(
            Arc::new(PureExpr::Var("z".into(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ))));
    }

    #[test]
    fn test_needs_seq_preamble_view() {
        // Formula with View expression should need Seq preamble
        let expr = PureExpr::View(Arc::new(PureExpr::Var("self".into(), None)));
        let formula = Formula::Pure(expr);
        assert!(needs_seq_preamble(&formula));
    }

    #[test]
    fn test_needs_seq_preamble_method_call() {
        // Formula with Seq method call should need Seq preamble
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var("self".into(), None)))),
            method: "len".into(),
            args: vec![],
        };
        let formula = Formula::Pure(expr);
        assert!(needs_seq_preamble(&formula));
    }

    #[test]
    fn test_needs_seq_preamble_pure_int() {
        // Simple integer formula should NOT need Seq preamble
        let formula = Formula::Pure(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".into(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ));
        assert!(!needs_seq_preamble(&formula));
    }

    #[test]
    fn test_needs_seq_preamble_nested() {
        // View inside nested formula should trigger Seq preamble
        let inner = Formula::Pure(PureExpr::View(Arc::new(PureExpr::Var("v".into(), None))));
        let outer = Formula::And(Arc::new(Formula::True), Arc::new(inner));
        assert!(needs_seq_preamble(&outer));
    }

    #[test]
    fn test_is_seq_var() {
        assert!(is_seq_var("self_view"));
        assert!(is_seq_var("v_current_view"));
        assert!(is_seq_var("v_final_view"));
        assert!(!is_seq_var("x"));
        assert!(!is_seq_var("result"));
        assert!(!is_seq_var("v_current")); // Not a view
    }

    #[test]
    fn test_declare_seq_var() {
        let mut smt_gen = SmtGenerator::new();
        smt_gen.declare_seq("self_view");
        let output = smt_gen.output();
        assert!(output.contains("(declare-const self_view Seq)"));
    }

    #[test]
    fn test_declare_vars_in_formula_with_view() {
        // Formula with View should declare view variable as Seq sort
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var("self".into(), None)))),
            method: "len".into(),
            args: vec![PureExpr::Var("x".into(), None)],
        };
        let formula = Formula::Pure(PureExpr::BinOp(
            Arc::new(expr),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ));

        let mut smt_gen = SmtGenerator::new();
        smt_gen.declare_vars_in_formula(&formula);
        let output = smt_gen.output();

        // self_view should be Seq, x should be Int
        assert!(
            output.contains("(declare-const self_view Seq)"),
            "View var should be Seq sort"
        );
        assert!(
            output.contains("(declare-const x Int)"),
            "Regular var should be Int sort"
        );
    }

    #[test]
    fn test_needs_seq_preamble_method_call_with_nested_view() {
        // MethodCall with View in receiver should trigger via recursive check
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var("v".into(), None)))),
            method: "unknown_method".into(), // Not a known Seq method
            args: vec![],
        };
        let formula = Formula::Pure(expr);
        // Should still detect View in receiver
        assert!(needs_seq_preamble(&formula));
    }

    #[test]
    fn test_needs_seq_preamble_method_call_with_view_in_args() {
        // MethodCall with View in argument should trigger
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("x".into(), None)),
            method: "some_method".into(),
            args: vec![PureExpr::View(Arc::new(PureExpr::Var("v".into(), None)))],
        };
        let formula = Formula::Pure(expr);
        assert!(needs_seq_preamble(&formula));
    }

    #[test]
    fn test_declare_vars_in_expr_with_view() {
        // declare_vars_in_expr should also use Seq sort for view variables
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var("self".into(), None)))),
                method: "len".into(),
                args: vec![],
            }),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        );

        let mut smt_gen = SmtGenerator::new();
        smt_gen.declare_vars_in_expr(&expr);
        let output = smt_gen.output();

        // self_view should be Seq
        assert!(
            output.contains("(declare-const self_view Seq)"),
            "View var should be Seq in expr"
        );
    }

    #[test]
    fn test_collect_vars_with_sorts_old_context() {
        // Test that old(x) creates old_x with correct sort (#223)
        // old(flag) in a boolean context should create old_flag: Bool
        let expr = PureExpr::Old(Arc::new(PureExpr::Var("flag".into(), None)));
        let vars = collect_vars_with_sorts(&expr);
        assert_eq!(vars.get("old_flag"), Some(&VarSort::Bool));
        assert!(
            !vars.contains_key("flag"),
            "Original name should not appear"
        );
    }

    #[test]
    fn test_collect_vars_with_sorts_mixed_context() {
        // Test that variables in arithmetic context get Int sort
        // result == old(x) + 1 should have:
        // - result: Int (in arithmetic context via equality with Int)
        // - old_x: Int (in arithmetic context)
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Old(Arc::new(PureExpr::Var("x".into(), None)))),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
        );
        let vars = collect_vars_with_sorts(&expr);
        assert_eq!(vars.get("result"), Some(&VarSort::Int));
        assert_eq!(vars.get("old_x"), Some(&VarSort::Int));
    }

    #[test]
    fn test_collect_vars_with_sorts_view_always_seq() {
        // View variables should always get Seq sort regardless of context
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var("v".into(), None)))),
                method: "len".into(),
                args: vec![],
            }),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        );
        let vars = collect_vars_with_sorts(&expr);
        assert_eq!(vars.get("v_view"), Some(&VarSort::Seq));
    }
}

// Tests for basic Formula variants (Part of #90)
mod basic_formula_tests {
    use super::*;

    #[test]
    fn test_formula_to_smt_true() {
        assert_eq!(formula_to_smt(&Formula::True), "true");
    }

    #[test]
    fn test_formula_to_smt_false() {
        assert_eq!(formula_to_smt(&Formula::False), "false");
    }

    #[test]
    fn test_formula_to_smt_or() {
        let f = Formula::Or(Arc::new(Formula::True), Arc::new(Formula::False));
        assert_eq!(formula_to_smt(&f), "(or true false)");
    }

    #[test]
    fn test_formula_to_smt_implies() {
        let f = Formula::Implies(Arc::new(Formula::True), Arc::new(Formula::False));
        assert_eq!(formula_to_smt(&f), "(=> true false)");
    }

    #[test]
    fn test_formula_to_smt_or_with_pure() {
        // (x > 0) || (y < 10)
        let f = Formula::Or(
            Arc::new(Formula::Pure(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            ))),
            Arc::new(Formula::Pure(PureExpr::BinOp(
                Arc::new(PureExpr::Var("y".to_string(), None)),
                BinOp::Lt,
                Arc::new(PureExpr::Int(10)),
            ))),
        );
        assert_eq!(formula_to_smt(&f), "(or (> x 0) (< y 10))");
    }

    #[test]
    fn test_formula_to_smt_implies_with_pure() {
        // (x > 0) => (result > 0)
        let f = Formula::Implies(
            Arc::new(Formula::Pure(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            ))),
            Arc::new(Formula::Pure(PureExpr::BinOp(
                Arc::new(PureExpr::Var("result".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            ))),
        );
        assert_eq!(formula_to_smt(&f), "(=> (> x 0) (> result 0))");
    }

    #[test]
    fn test_formula_to_smt_and() {
        // Direct test for And (previously only tested indirectly)
        let f = Formula::And(Arc::new(Formula::True), Arc::new(Formula::False));
        assert_eq!(formula_to_smt(&f), "(and true false)");
    }

    #[test]
    fn test_formula_to_smt_nested_logic() {
        // ((x > 0) && (y > 0)) => (x + y > 0)
        let precond = Formula::And(
            Arc::new(Formula::Pure(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            ))),
            Arc::new(Formula::Pure(PureExpr::BinOp(
                Arc::new(PureExpr::Var("y".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            ))),
        );
        let postcond = Formula::Pure(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ));
        let f = Formula::Implies(Arc::new(precond), Arc::new(postcond));
        assert_eq!(
            formula_to_smt(&f),
            "(=> (and (> x 0) (> y 0)) (> (+ x y) 0))"
        );
    }
}

// Free variable collection tests (Part of #232)
mod free_var_tests {
    use super::*;
    use crate::formula::{ExprSort, MatchArm, Pattern};

    #[test]
    fn test_match_pattern_bindings_excluded() {
        // match opt { Some(x) => x + 1, None => 0 }
        // The `x` in `x + 1` is bound by `Some(x)`, not free
        let expr = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("opt".to_string(), None)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                    },
                    body: PureExpr::BinOp(
                        Arc::new(PureExpr::Var("x".to_string(), None)),
                        BinOp::Add,
                        Arc::new(PureExpr::Int(1)),
                    ),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    body: PureExpr::Int(0),
                },
            ],
        };

        let vars = collect_vars_with_sorts(&expr);
        // `opt` is free, `x` is NOT free (bound by pattern)
        assert!(vars.contains_key("opt"), "opt should be free: {vars:?}");
        assert!(
            !vars.contains_key("x"),
            "x should NOT be free (bound by pattern): {vars:?}"
        );
    }

    #[test]
    fn test_match_nested_pattern_bindings_excluded() {
        // match pair { Pair(a, b) => a + b }
        // Both `a` and `b` are bound
        let expr = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("pair".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: "Pair".to_string(),
                    inner: Some(Box::new(Pattern::Binding("a".to_string()))),
                    // Note: simplified - real nested patterns would need deeper nesting
                },
                body: PureExpr::BinOp(
                    Arc::new(PureExpr::Var("a".to_string(), None)),
                    BinOp::Add,
                    Arc::new(PureExpr::Var("b".to_string(), None)),
                ),
            }],
        };

        let vars = collect_vars_with_sorts(&expr);
        // `pair` is free, `a` is NOT free (bound), `b` IS free (not in pattern)
        assert!(vars.contains_key("pair"), "pair should be free: {vars:?}");
        assert!(
            !vars.contains_key("a"),
            "a should NOT be free (bound by pattern): {vars:?}"
        );
        assert!(
            vars.contains_key("b"),
            "b should be free (not bound): {vars:?}"
        );
    }

    #[test]
    fn test_wildcard_and_literal_patterns_no_bindings() {
        // match x { _ => y, 0 => z }
        // No bindings introduced
        let expr = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Wildcard,
                    body: PureExpr::Var("y".to_string(), None),
                },
                MatchArm {
                    pattern: Pattern::Literal(PureExpr::Int(0)),
                    body: PureExpr::Var("z".to_string(), None),
                },
            ],
        };

        let vars = collect_vars_with_sorts(&expr);
        // All vars are free
        assert!(vars.contains_key("x"), "x should be free: {vars:?}");
        assert!(vars.contains_key("y"), "y should be free: {vars:?}");
        assert!(vars.contains_key("z"), "z should be free: {vars:?}");
    }

    #[test]
    fn test_infer_var_sorts_match_pattern_bindings_excluded() {
        // Ensure infer_var_sorts also excludes pattern-bound variables
        // match opt { Some(x) => x + 1, None => 0 }
        let expr = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("opt".to_string(), None)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                    },
                    body: PureExpr::BinOp(
                        Arc::new(PureExpr::Var("x".to_string(), None)),
                        BinOp::Add,
                        Arc::new(PureExpr::Int(1)),
                    ),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    body: PureExpr::Int(0),
                },
            ],
        };

        let sorts = infer_var_sorts(&expr);
        // `opt` is free, `x` is NOT free (bound by pattern)
        assert!(sorts.contains_key("opt"), "opt should be free: {sorts:?}");
        assert!(
            !sorts.contains_key("x"),
            "x should NOT be free (bound by pattern): {sorts:?}"
        );
    }

    // --- Closure bound-parameter exclusion tests (#985) ---

    #[test]
    fn test_closure_bound_params_excluded_from_free_vars() {
        // |x: Int| x + y — `x` is bound, `y` is free
        let expr = PureExpr::Closure {
            params: vec![("x".to_string(), Some(ExprSort::Int))],
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
        };

        let vars = collect_vars_with_sorts(&expr);
        assert!(
            !vars.contains_key("x"),
            "x should NOT be free (closure-bound): {vars:?}"
        );
        assert!(vars.contains_key("y"), "y should be free: {vars:?}");
    }

    #[test]
    fn test_closure_multiple_bound_params_excluded() {
        // |a, b| a + b + c — `a` and `b` are bound, `c` is free
        let expr = PureExpr::Closure {
            params: vec![("a".to_string(), None), ("b".to_string(), None)],
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Var("a".to_string(), None)),
                    BinOp::Add,
                    Arc::new(PureExpr::Var("b".to_string(), None)),
                )),
                BinOp::Add,
                Arc::new(PureExpr::Var("c".to_string(), None)),
            )),
        };

        let vars = collect_vars_with_sorts(&expr);
        assert!(
            !vars.contains_key("a"),
            "a should NOT be free (closure-bound): {vars:?}"
        );
        assert!(
            !vars.contains_key("b"),
            "b should NOT be free (closure-bound): {vars:?}"
        );
        assert!(vars.contains_key("c"), "c should be free: {vars:?}");
    }

    #[test]
    fn test_closure_param_shadows_outer_free_var() {
        // BinOp(Var("x"), Add, Closure{x, body: Var("x")})
        // Outer `x` is free in the addition, inner `x` is bound by closure.
        // After processing, `x` should remain free because it appears outside.
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Closure {
                params: vec![("x".to_string(), None)],
                body: Arc::new(PureExpr::Var("x".to_string(), None)),
            }),
        );

        let vars = collect_vars_with_sorts(&expr);
        assert!(
            vars.contains_key("x"),
            "x should be free (appears outside closure): {vars:?}"
        );
    }

    #[test]
    fn test_infer_var_sorts_closure_bound_params_excluded() {
        // |x: Int| x + y — `x` is bound, `y` is free
        let expr = PureExpr::Closure {
            params: vec![("x".to_string(), Some(ExprSort::Int))],
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
        };

        let sorts = infer_var_sorts(&expr);
        assert!(
            !sorts.contains_key("x"),
            "x should NOT be free (closure-bound): {sorts:?}"
        );
        assert!(sorts.contains_key("y"), "y should be free: {sorts:?}");
    }

    #[test]
    fn test_let_bound_var_excluded_from_free_vars() {
        // `let x = 1 in x + y` should report only `y` as free.
        // The let-bound `x` is excluded, consistent with Forall/Exists/Closure.
        let expr = PureExpr::Let {
            var: "x".to_string(),
            value: Arc::new(PureExpr::Int(1)),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
        };

        let vars = collect_vars_with_sorts(&expr);
        assert!(
            !vars.contains_key("x"),
            "let-bound x should NOT be free: {vars:?}"
        );
        assert!(vars.contains_key("y"), "y should be free: {vars:?}");
    }

    // --- Let-binding value expression shadowing tests (#1016) ---

    #[test]
    fn test_let_shadow_value_expr_free_vars_with_sorts() {
        // `let x = x + 1 in x + y`
        // FV = {x, y}: outer x from value expression, y from body.
        // The let-bound x only scopes the body, not the value.
        let expr = PureExpr::Let {
            var: "x".to_string(),
            value: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
        };

        let vars = collect_vars_with_sorts(&expr);
        assert!(
            vars.contains_key("x"),
            "outer x (from value expr) should be free: {vars:?}"
        );
        assert!(vars.contains_key("y"), "y should be free: {vars:?}");
    }

    #[test]
    fn test_let_shadow_value_expr_infer_var_sorts() {
        // Same test for infer_var_sorts path.
        let expr = PureExpr::Let {
            var: "x".to_string(),
            value: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
        };

        let vars = infer_var_sorts(&expr);
        assert!(
            vars.contains_key("x"),
            "outer x (from value expr) should be free: {vars:?}"
        );
        assert!(vars.contains_key("y"), "y should be free: {vars:?}");
    }

    #[test]
    fn test_let_shadow_value_expr_collect_vars_expr() {
        // Same test for collect_vars_expr path (HashSet, no sorts).
        let expr = PureExpr::Let {
            var: "x".to_string(),
            value: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
        };

        let vars = collect_vars_expr(&expr);
        assert!(
            vars.contains("x"),
            "outer x (from value expr) should be free: {vars:?}"
        );
        assert!(vars.contains("y"), "y should be free: {vars:?}");
    }

    #[test]
    fn test_let_shadow_value_expr_collect_old_vars_expr() {
        // old(let x = x + 1 in x + y)
        // Under old-context collection, the outer x from the value expression
        // must remain free as `old_x`; body y is `old_y`.
        let expr = PureExpr::Old(Arc::new(PureExpr::Let {
            var: "x".to_string(),
            value: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Add,
                Arc::new(PureExpr::Var("y".to_string(), None)),
            )),
        }));

        let vars = collect_vars_expr(&expr);
        assert!(
            vars.contains("old_x"),
            "outer old_x (from value expr) should be free: {vars:?}"
        );
        assert!(vars.contains("old_y"), "old_y should be free: {vars:?}");
        assert!(
            !vars.contains("x"),
            "raw x should not appear under old-context collection: {vars:?}"
        );
        assert!(
            !vars.contains("y"),
            "raw y should not appear under old-context collection: {vars:?}"
        );
    }

    // --- Sibling-erasure regression tests (Part of #1392) ---
    // The binder-scope bug: `x + forall x. P` must keep outer `x` free.

    #[test]
    fn test_forall_sibling_preserves_outer_free_var_collect_vars() {
        // x + (forall x. x > 0)  =>  FV = {x}
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Forall {
                var: "x".to_string(),
                var_sort: None,
                body: Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Var("x".to_string(), None)),
                    BinOp::Gt,
                    Arc::new(PureExpr::Int(0)),
                )),
                triggers: vec![],
            }),
        );
        let vars = collect_vars_expr(&expr);
        assert!(
            vars.contains("x"),
            "outer x must survive sibling forall: {vars:?}"
        );
    }

    #[test]
    fn test_exists_sibling_preserves_outer_free_var_collect_vars() {
        // x + (exists x. x > 0)  =>  FV = {x}
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Exists {
                var: "x".to_string(),
                var_sort: None,
                body: Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Var("x".to_string(), None)),
                    BinOp::Gt,
                    Arc::new(PureExpr::Int(0)),
                )),
                triggers: vec![],
            }),
        );
        let vars = collect_vars_expr(&expr);
        assert!(
            vars.contains("x"),
            "outer x must survive sibling exists: {vars:?}"
        );
    }

    #[test]
    fn test_closure_sibling_preserves_outer_free_var_collect_vars() {
        // x + (|x| x + 1)  =>  FV = {x}
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Closure {
                params: vec![("x".to_string(), None)],
                body: Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Var("x".to_string(), None)),
                    BinOp::Add,
                    Arc::new(PureExpr::Int(1)),
                )),
            }),
        );
        let vars = collect_vars_expr(&expr);
        assert!(
            vars.contains("x"),
            "outer x must survive sibling closure: {vars:?}"
        );
    }

    #[test]
    fn test_match_sibling_preserves_outer_free_var_collect_vars() {
        use crate::formula::{MatchArm, Pattern};
        // x + match y { Some(x) => x }  =>  FV = {x, y}
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Match {
                scrutinee: Arc::new(PureExpr::Var("y".to_string(), None)),
                arms: vec![MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                    },
                    body: PureExpr::Var("x".to_string(), None),
                }],
            }),
        );
        let vars = collect_vars_expr(&expr);
        assert!(
            vars.contains("x"),
            "outer x must survive sibling match binding: {vars:?}"
        );
        assert!(vars.contains("y"), "scrutinee y must be free: {vars:?}");
    }

    #[test]
    fn test_forall_sibling_preserves_outer_free_var_old_context() {
        // old(x + forall x. x > 0)  =>  FV = {old_x}
        let expr = PureExpr::Old(Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Forall {
                var: "x".to_string(),
                var_sort: None,
                body: Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Var("x".to_string(), None)),
                    BinOp::Gt,
                    Arc::new(PureExpr::Int(0)),
                )),
                triggers: vec![],
            }),
        )));
        let vars = collect_vars_expr(&expr);
        assert!(
            vars.contains("old_x"),
            "outer old_x must survive sibling forall in old context: {vars:?}"
        );
    }

    #[test]
    fn test_forall_sibling_preserves_outer_free_var_infer_sorts() {
        // x + (forall x. x > 0)  =>  x should be in the sorts map
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Forall {
                var: "x".to_string(),
                var_sort: None,
                body: Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::Var("x".to_string(), None)),
                    BinOp::Gt,
                    Arc::new(PureExpr::Int(0)),
                )),
                triggers: vec![],
            }),
        );
        let sorts = infer_var_sorts(&expr);
        assert!(
            sorts.contains_key("x"),
            "outer x must survive sibling forall in infer_var_sorts: {sorts:?}"
        );
    }

    #[test]
    fn test_match_sibling_preserves_outer_free_var_infer_sorts() {
        use crate::formula::{MatchArm, Pattern};
        // x + match y { Some(x) => x }  =>  x and y in sorts
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Match {
                scrutinee: Arc::new(PureExpr::Var("y".to_string(), None)),
                arms: vec![MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                    },
                    body: PureExpr::Var("x".to_string(), None),
                }],
            }),
        );
        let sorts = infer_var_sorts(&expr);
        assert!(
            sorts.contains_key("x"),
            "outer x must survive sibling match in infer_var_sorts: {sorts:?}"
        );
        assert!(
            sorts.contains_key("y"),
            "scrutinee y must be in sorts: {sorts:?}"
        );
    }

    #[test]
    fn test_match_sibling_preserves_outer_free_var_collect_with_sorts() {
        use crate::formula::{MatchArm, Pattern};
        // x + match y { Some(x) => x }  =>  x and y in sorted vars
        let expr = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Match {
                scrutinee: Arc::new(PureExpr::Var("y".to_string(), None)),
                arms: vec![MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                    },
                    body: PureExpr::Var("x".to_string(), None),
                }],
            }),
        );
        let vars = collect_vars_with_sorts(&expr);
        assert!(
            vars.contains_key("x"),
            "outer x must survive sibling match in collect_vars_with_sorts: {vars:?}"
        );
        assert!(
            vars.contains_key("y"),
            "scrutinee y must be in vars: {vars:?}"
        );
    }

    #[test]
    fn test_formula_forall_sibling_preserves_outer_free_var() {
        // Pure(x > 0) && Forall { x, body: Pure(x > 1) }  =>  FV = {x}
        let formula = Formula::And(
            Arc::new(Formula::Pure(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), None)),
                BinOp::Gt,
                Arc::new(PureExpr::Int(0)),
            ))),
            Arc::new(Formula::Forall {
                var: "x".to_string(),
                var_sort: None,
                body: Arc::new(Formula::Pure(PureExpr::BinOp(
                    Arc::new(PureExpr::Var("x".to_string(), None)),
                    BinOp::Gt,
                    Arc::new(PureExpr::Int(1)),
                ))),
                triggers: vec![],
            }),
        );
        let vars = collect_vars_formula(&formula);
        assert!(
            vars.contains("x"),
            "outer x must survive formula-level sibling forall: {vars:?}"
        );
    }
}
