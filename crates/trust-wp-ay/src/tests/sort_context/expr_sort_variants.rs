// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// =============================================================================
// Step 2c (#2038): infer_expr_sort for new ExprSort variants
// =============================================================================

/// Unit-annotated Var must return Uninterpreted("Unit"), not Sort::Int.
#[test]
#[timeout(30000)]
fn infer_expr_sort_var_with_unit_annotation_returns_unit() {
    let expr = var_with_sort("u", ExprSort::Unit);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Uninterpreted("Unit".to_string()),
        "Unit-annotated Var should return Uninterpreted(Unit), not Int"
    );
}

/// Datatype-annotated Var returns Uninterpreted with bare type name (path stripped).
/// Changed in #2155: qualified paths are now stripped to canonical bare names.
#[test]
#[timeout(30000)]
fn infer_expr_sort_var_with_datatype_annotation_returns_uninterpreted_name() {
    let expr = var_with_sort(
        "opt",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name(
            "std::option::Option",
        )),
    );
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Uninterpreted("Option".to_string()),
        "Datatype-annotated Var should return Uninterpreted with bare type name (#2155)"
    );
}

/// FMap-annotated Var returns Uninterpreted("FMap").
#[test]
#[timeout(30000)]
fn infer_expr_sort_var_with_fmap_annotation_returns_fmap() {
    let expr = var_with_sort("m", ExprSort::FMap);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Uninterpreted("FMap".to_string()),
        "FMap-annotated Var should return Uninterpreted(FMap)"
    );
}

/// Tuple-annotated Var returns Uninterpreted("TupleN") for arity N.
#[test]
#[timeout(30000)]
fn infer_expr_sort_var_with_tuple_annotation_returns_tuple_arity() {
    let expr = var_with_sort("t", ExprSort::Tuple(3));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Uninterpreted("Tuple3".to_string()),
        "Tuple(3)-annotated Var should return Uninterpreted(Tuple3)"
    );
}

/// Ref(Bool)-annotated Var should infer as Bool (the referent sort).
#[test]
#[timeout(30000)]
fn infer_expr_sort_var_with_ref_bool_annotation_returns_bool() {
    let expr = var_with_sort("r", ExprSort::Ref(Box::new(ExprSort::Bool)));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "Ref(Bool)-annotated Var should return Bool (the referent sort)"
    );
}

/// Ref(Seq)-annotated Var should infer as Seq (the referent sort).
#[test]
#[timeout(30000)]
fn infer_expr_sort_var_with_ref_seq_annotation_returns_seq() {
    let expr = var_with_sort("r", ExprSort::Ref(Box::new(ExprSort::Seq)));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::seq(Sort::Int),
        "Ref(Seq)-annotated Var should return Seq (the referent sort)"
    );
}

/// Ref(Datatype)-annotated Var should infer as the ADT sort.
#[test]
#[timeout(30000)]
fn infer_expr_sort_var_with_ref_datatype_annotation_returns_datatype() {
    let expr = var_with_sort(
        "r",
        ExprSort::Ref(Box::new(ExprSort::Datatype(
            trust_wp_core::formula::intern_sort_name("MyStruct"),
        ))),
    );
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Uninterpreted("MyStruct".to_string()),
        "Ref(Datatype)-annotated Var should return Uninterpreted with the ADT name"
    );
}

/// MutRef(Bool)-annotated Var keeps the dedicated mut-ref carrier sort. (#2141)
#[test]
#[timeout(30000)]
fn infer_expr_sort_var_with_mutref_bool_annotation_returns_mutref_carrier() {
    let ann = ExprSort::MutRef(Box::new(ExprSort::Bool));
    let expr = var_with_sort("r", ann.clone());
    assert_eq!(
        infer_expr_sort(&expr),
        crate::encoder::sort_context::expr_sort_to_ay_sort(&ann),
        "MutRef(Bool)-annotated Var should keep the mut-ref carrier sort"
    );
}

/// Deref(MutRef(Bool)) should still infer as Bool, not as the mut-ref carrier. (#2141)
#[test]
#[timeout(30000)]
fn infer_expr_sort_deref_mutref_bool_annotation_returns_bool() {
    let expr = deref(var_with_sort(
        "r",
        ExprSort::MutRef(Box::new(ExprSort::Bool)),
    ));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "Deref(MutRef(Bool)) should infer as the referent sort"
    );
}

/// Final(MutRef(Seq)) should still infer as Seq, not as the mut-ref carrier. (#2141)
#[test]
#[timeout(30000)]
fn infer_expr_sort_final_mutref_seq_annotation_returns_seq() {
    let expr = final_expr(var_with_sort(
        "r",
        ExprSort::MutRef(Box::new(ExprSort::Seq)),
    ));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::seq(Sort::Int),
        "Final(MutRef(Seq)) should infer as the referent sort"
    );
}

// =============================================================================
// Self-audit (#2038): is_definitely_non_bool for new ExprSort variants
// =============================================================================

/// Bool-annotated Var must NOT be classified as definitely-non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_var_bool_returns_false() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    let expr = var_with_sort("b", ExprSort::Bool);
    assert!(
        !is_definitely_non_bool(&expr),
        "Bool-annotated Var must not be classified as definitely-non-bool"
    );
}

/// Datatype-annotated Var is definitely non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_var_datatype_returns_true() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    let expr = var_with_sort(
        "opt",
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("Option")),
    );
    assert!(
        is_definitely_non_bool(&expr),
        "Datatype-annotated Var must be classified as definitely-non-bool"
    );
}

/// Ref(Ref(Bool)) should NOT be classified as definitely-non-bool, because
/// the innermost referent is Bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_nested_ref_bool_returns_false() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    let expr = var_with_sort(
        "r",
        ExprSort::Ref(Box::new(ExprSort::Ref(Box::new(ExprSort::Bool)))),
    );
    assert!(
        !is_definitely_non_bool(&expr),
        "Ref(Ref(Bool)) should resolve to Bool and NOT be classified as non-bool"
    );
}

/// Ref(Int) should be classified as definitely non-bool.
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_ref_int_returns_true() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    let expr = var_with_sort("r", ExprSort::Ref(Box::new(ExprSort::Int)));
    assert!(
        is_definitely_non_bool(&expr),
        "Ref(Int)-annotated Var must be classified as definitely-non-bool"
    );
}

/// Deref(MutRef(Bool)) should not be classified as definitely non-bool. (#2141)
#[test]
#[timeout(30000)]
fn is_definitely_non_bool_deref_mutref_bool_returns_false() {
    use crate::encoder::sort_context::is_definitely_non_bool;
    let expr = deref(var_with_sort(
        "r",
        ExprSort::MutRef(Box::new(ExprSort::Bool)),
    ));
    assert!(
        !is_definitely_non_bool(&expr),
        "Deref(MutRef(Bool)) should resolve to Bool and stay bool-typed"
    );
}

// =============================================================================
// Proof coverage: infer_expr_sort — leaf types (#2057 coverage gap)
// =============================================================================

/// Bool literal returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_bool_literal_returns_bool() {
    assert_eq!(infer_expr_sort(&bool_expr(true)), Sort::Bool);
    assert_eq!(infer_expr_sort(&bool_expr(false)), Sort::Bool);
}

/// Int literal returns Sort::Int.
#[test]
#[timeout(30000)]
fn infer_expr_sort_int_literal_returns_int() {
    assert_eq!(infer_expr_sort(&int(0)), Sort::Int);
    assert_eq!(infer_expr_sort(&int(-42)), Sort::Int);
    assert_eq!(infer_expr_sort(&int(i64::MAX)), Sort::Int);
}

/// Bool-annotated Var returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_var_with_bool_annotation_returns_bool() {
    let expr = var_with_sort("b", ExprSort::Bool);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "Bool-annotated Var should return Sort::Bool"
    );
}

/// Un-annotated Var (None) returns Sort::Int (default fallback).
#[test]
#[timeout(30000)]
fn infer_expr_sort_var_unannotated_returns_int() {
    assert_eq!(
        infer_expr_sort(&var("x")),
        Sort::Int,
        "Un-annotated Var should default to Sort::Int"
    );
}

/// Int-annotated Var returns Sort::Int.
#[test]
#[timeout(30000)]
fn infer_expr_sort_var_with_int_annotation_returns_int() {
    let expr = var_with_sort("n", ExprSort::Int);
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Int,
        "Int-annotated Var should return Sort::Int"
    );
}

// =============================================================================
// Proof coverage: infer_expr_sort — BinOp arms
// =============================================================================

/// All comparison operators return Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_binop_comparison_returns_bool() {
    let x = var("x");
    let y = var("y");
    assert_eq!(infer_expr_sort(&eq(x.clone(), y.clone())), Sort::Bool, "Eq");
    assert_eq!(infer_expr_sort(&ne(x.clone(), y.clone())), Sort::Bool, "Ne");
    assert_eq!(infer_expr_sort(&lt(x.clone(), y.clone())), Sort::Bool, "Lt");
    assert_eq!(infer_expr_sort(&le(x.clone(), y.clone())), Sort::Bool, "Le");
    assert_eq!(infer_expr_sort(&gt(x.clone(), y.clone())), Sort::Bool, "Gt");
    assert_eq!(infer_expr_sort(&ge(x, y)), Sort::Bool, "Ge");
}

/// All logical operators return Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_binop_logical_returns_bool() {
    let p = bool_expr(true);
    let q = bool_expr(false);
    assert_eq!(
        infer_expr_sort(&and(p.clone(), q.clone())),
        Sort::Bool,
        "And"
    );
    assert_eq!(infer_expr_sort(&or(p.clone(), q.clone())), Sort::Bool, "Or");
    assert_eq!(infer_expr_sort(&implies(p, q)), Sort::Bool, "Implies");
}

/// All arithmetic operators return Sort::Int.
#[test]
#[timeout(30000)]
fn infer_expr_sort_binop_arithmetic_returns_int() {
    let x = var("x");
    let y = var("y");
    assert_eq!(
        infer_expr_sort(&add(x.clone(), y.clone())),
        Sort::Int,
        "Add"
    );
    assert_eq!(
        infer_expr_sort(&sub(x.clone(), y.clone())),
        Sort::Int,
        "Sub"
    );
    assert_eq!(
        infer_expr_sort(&mul(x.clone(), y.clone())),
        Sort::Int,
        "Mul"
    );
    assert_eq!(
        infer_expr_sort(&div(x.clone(), y.clone())),
        Sort::Int,
        "Div"
    );
    assert_eq!(
        infer_expr_sort(&mod_expr(x.clone(), y.clone())),
        Sort::Int,
        "Mod"
    );
}

/// Bitwise operators (Shl, Shr, BitAnd, BitXor, BitOr) return Sort::Int.
#[test]
#[timeout(30000)]
fn infer_expr_sort_binop_bitwise_returns_int() {
    let x = var("x");
    let y = var("y");
    for op in [
        BinOp::Shl,
        BinOp::Shr,
        BinOp::BitAnd,
        BinOp::BitXor,
        BinOp::BitOr,
    ] {
        assert_eq!(
            infer_expr_sort(&binop(x.clone(), op, y.clone())),
            Sort::Int,
            "BinOp::{op:?} should return Int"
        );
    }
}

// =============================================================================
// Proof coverage: infer_expr_sort — UnOp arms
// =============================================================================

/// Not returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_unop_not_returns_bool() {
    assert_eq!(
        infer_expr_sort(&not(bool_expr(true))),
        Sort::Bool,
        "Not should return Bool"
    );
}

/// Neg returns Sort::Int.
#[test]
#[timeout(30000)]
fn infer_expr_sort_unop_neg_returns_int() {
    assert_eq!(
        infer_expr_sort(&neg(var("x"))),
        Sort::Int,
        "Neg should return Int"
    );
}

// =============================================================================
// Proof coverage: infer_expr_sort — Ite, Forall, Exists
// =============================================================================

/// Ite returns the sort of the then-branch.
#[test]
#[timeout(30000)]
fn infer_expr_sort_ite_returns_then_sort() {
    // if cond then Bool else Bool → Bool
    let expr_bool = ite(var("c"), gt(var("x"), int(0)), bool_expr(false));
    assert_eq!(
        infer_expr_sort(&expr_bool),
        Sort::Bool,
        "Ite with Bool then-branch should return Bool"
    );

    // if cond then Int else Int → Int
    let expr_int = ite(var("c"), add(var("x"), int(1)), int(0));
    assert_eq!(
        infer_expr_sort(&expr_int),
        Sort::Int,
        "Ite with Int then-branch should return Int"
    );

    // if cond then View(Var) else View(Var) → Int (View recurses, #2057)
    let expr_view = ite(var("c"), view(var("v")), view(var("w")));
    assert_eq!(
        infer_expr_sort(&expr_view),
        Sort::Int,
        "Ite with View(unannotated Var) then-branch should return Int (#2057)"
    );

    // if cond then Seq (method) else Seq (method) → Seq
    let expr_seq = ite(
        var("c"),
        method_call(var("v"), "push_back", vec![int(1)]),
        method_call(var("w"), "push_back", vec![int(2)]),
    );
    assert_eq!(
        infer_expr_sort(&expr_seq),
        Sort::seq(Sort::Int),
        "Ite with Seq-producing method then-branch should return Seq"
    );
}

/// Forall returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_forall_returns_bool() {
    let expr = forall("x", gt(var("x"), int(0)));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "Forall should return Bool"
    );
}

/// Exists returns Sort::Bool.
#[test]
#[timeout(30000)]
fn infer_expr_sort_exists_returns_bool() {
    let expr = exists("x", gt(var("x"), int(0)));
    assert_eq!(
        infer_expr_sort(&expr),
        Sort::Bool,
        "Exists should return Bool"
    );
}
