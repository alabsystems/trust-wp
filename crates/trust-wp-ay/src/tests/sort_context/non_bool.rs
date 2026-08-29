// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// =============================================================================
// Proof coverage: is_definitely_non_bool — comprehensive arms
// =============================================================================

/// Int literal is definitely non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_int_literal_returns_true() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        is_definitely_non_bool(&int(42)),
        "Int literal must be non-bool"
    );
}

/// Float literal is definitely non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_float_literal_returns_true() {
    use trust_wp_core::formula::FloatBits;

    use crate::encoder::sort_context::is_definitely_non_bool;

    assert!(
        is_definitely_non_bool(&PureExpr::Float(FloatBits::from_f64(3.5))),
        "Float literal must be non-bool"
    );
}

/// Bool literal is NOT definitely non-bool (it IS bool).
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_bool_literal_returns_false() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        !is_definitely_non_bool(&bool_expr(true)),
        "Bool literal should NOT be classified as non-bool"
    );
}

/// Arithmetic BinOp is definitely non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_arithmetic_binop_returns_true() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        is_definitely_non_bool(&add(var("x"), var("y"))),
        "Add should be non-bool"
    );
    assert!(
        is_definitely_non_bool(&sub(var("x"), var("y"))),
        "Sub should be non-bool"
    );
    assert!(
        is_definitely_non_bool(&mul(var("x"), var("y"))),
        "Mul should be non-bool"
    );
    assert!(
        is_definitely_non_bool(&div(var("x"), var("y"))),
        "Div should be non-bool"
    );
    assert!(
        is_definitely_non_bool(&mod_expr(var("x"), var("y"))),
        "Mod should be non-bool"
    );
}

/// Comparison BinOp is NOT definitely non-bool (returns Bool).
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_comparison_binop_returns_false() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        !is_definitely_non_bool(&eq(var("x"), var("y"))),
        "Eq is Bool, not non-bool"
    );
    assert!(
        !is_definitely_non_bool(&gt(var("x"), var("y"))),
        "Gt is Bool, not non-bool"
    );
}

/// Bitwise BinOp is definitely non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_bitwise_binop_returns_true() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    for op in [
        BinOp::Shl,
        BinOp::Shr,
        BinOp::BitAnd,
        BinOp::BitXor,
        BinOp::BitOr,
    ] {
        assert!(
            is_definitely_non_bool(&binop(var("x"), op, var("y"))),
            "BinOp::{op:?} should be non-bool"
        );
    }
}

/// UnOp::Neg is definitely non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_neg_returns_true() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        is_definitely_non_bool(&neg(var("x"))),
        "Neg should be non-bool"
    );
}

/// UnOp::Not is NOT definitely non-bool (returns Bool).
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_not_returns_false() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        !is_definitely_non_bool(&not(bool_expr(true))),
        "Not is Bool, not non-bool"
    );
}

/// MethodCall with Seq-producing method is definitely non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_seq_method_returns_true() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        is_definitely_non_bool(&method_call(view(var("v")), "push_back", vec![int(1)])),
        "push_back produces Seq, should be non-bool"
    );
    assert!(
        is_definitely_non_bool(&method_call(view(var("v")), "concat", vec![view(var("w"))])),
        "concat produces Seq, should be non-bool"
    );
}

/// MethodCall with known Int-returning builtins is definitely non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_len_sum_pow2_returns_true() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        is_definitely_non_bool(&method_call(view(var("v")), "len", vec![])),
        "len should be non-bool"
    );
    assert!(
        is_definitely_non_bool(&method_call(view(var("v")), "len_logic", vec![])),
        "len_logic should be non-bool"
    );
    assert!(
        is_definitely_non_bool(&method_call(view(var("v")), "sum", vec![])),
        "sum should be non-bool"
    );
    assert!(
        is_definitely_non_bool(&method_call(var("i"), "pow2", vec![])),
        "pow2 should be non-bool"
    );
}

/// LogicFnCall with "seq"/"seq_empty" is definitely non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_seq_logic_fn_returns_true() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        is_definitely_non_bool(&logic_fn_call("seq", vec![int(1)])),
        "seq should be non-bool"
    );
    assert!(
        is_definitely_non_bool(&logic_fn_call("seq_empty", vec![])),
        "seq_empty should be non-bool"
    );
    assert!(
        is_definitely_non_bool(&logic_fn_call("Seq::empty", vec![])),
        "Seq::empty should be non-bool"
    );
}

/// Var with Seq annotation is definitely non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_var_seq_returns_true() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        is_definitely_non_bool(&var_with_sort("s", ExprSort::Seq)),
        "Seq-annotated Var should be non-bool"
    );
}

/// Var with Int annotation is definitely non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_var_int_returns_true() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        is_definitely_non_bool(&var_with_sort("n", ExprSort::Int)),
        "Int-annotated Var should be non-bool"
    );
}

/// Var with Unit annotation is definitely non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_var_unit_returns_true() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        is_definitely_non_bool(&var_with_sort("u", ExprSort::Unit)),
        "Unit-annotated Var should be non-bool"
    );
}

/// Var with FMap annotation is definitely non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_var_fmap_returns_true() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        is_definitely_non_bool(&var_with_sort("m", ExprSort::FMap)),
        "FMap-annotated Var should be non-bool"
    );
}

/// Var with Tuple annotation is definitely non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_var_tuple_returns_true() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        is_definitely_non_bool(&var_with_sort("t", ExprSort::Tuple(3))),
        "Tuple-annotated Var should be non-bool"
    );
}

/// View recurses into inner — unannotated Var is not definitively non-bool. (#2057)
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_view_recurses() {
    use trust_wp_core::formula::FloatBits;

    use crate::encoder::sort_context::is_definitely_non_bool;

    // View(unannotated Var) — not definitively non-bool (could be Bool)
    assert!(
        !is_definitely_non_bool(&view(var("v"))),
        "View(unannotated Var) should not be definitively non-bool (#2057)"
    );
    // View(Int) — definitively non-bool
    assert!(
        is_definitely_non_bool(&view(int(42))),
        "View(Int) should be definitively non-bool"
    );
    assert!(
        is_definitely_non_bool(&view(PureExpr::Float(FloatBits::from_f64(2.0)))),
        "View(Float) should be definitively non-bool"
    );
}

/// Old/Deref/Final recurse into Float literals just like View does.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_old_deref_final_float_recurses() {
    use trust_wp_core::formula::FloatBits;

    use crate::encoder::sort_context::is_definitely_non_bool;

    let float_expr = PureExpr::Float(FloatBits::from_f64(2.0));
    assert!(
        is_definitely_non_bool(&old(float_expr.clone())),
        "Old(Float) should be definitively non-bool"
    );
    assert!(
        is_definitely_non_bool(&deref(float_expr.clone())),
        "Deref(Float) should be definitively non-bool"
    );
    assert!(
        is_definitely_non_bool(&final_expr(float_expr)),
        "Final(Float) should be definitively non-bool"
    );
}

/// Un-annotated Var defaults to false (could be Bool).
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_unannotated_var_returns_false() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        !is_definitely_non_bool(&var("x")),
        "Un-annotated Var could be Bool, so should return false"
    );
}

/// Forall/Exists fall to catch-all (could be Bool, returns false).
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_quantifier_returns_false() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    assert!(
        !is_definitely_non_bool(&forall("x", gt(var("x"), int(0)))),
        "Forall is Bool, should return false"
    );
    assert!(
        !is_definitely_non_bool(&exists("x", gt(var("x"), int(0)))),
        "Exists is Bool, should return false"
    );
}
