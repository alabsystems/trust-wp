// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for pure expression walker functions in `expr.rs`.
//!
//! Targets genuinely untested `pub(crate)` functions:
//! - `expr_has_mut_ref_carrier`: zero test references
//! - `Pattern::binds_name`: tested here (was `pattern_binds_var` before dedup)
//!
//! Also covers edge cases in lightly-tested walkers:
//! - `expr_has_bitwise_ops`: 8 refs (no direct negative tests)
//! - `expr_has_uf_method_call`: 8 refs (no direct negative tests)
//!
//! Part of #2514 (coverage gap: expr.rs, 922 LOC, 1 inline test).

use ntest::timeout;
use trust_wp_core::formula::{ExprSort, Pattern, PureExpr};

use super::super::helpers::*;
use crate::expr::{expr_has_bitwise_ops, expr_has_mut_ref_carrier, expr_has_uf_method_call};

// ── expr_has_mut_ref_carrier ────────────────────────────────────

/// A plain variable without MutRef annotation returns false.
#[test]
#[timeout(30000)]
fn mut_ref_carrier_absent_for_plain_var() {
    assert!(!expr_has_mut_ref_carrier(&var("x")));
}

/// A variable with MutRef annotation returns true.
#[test]
#[timeout(30000)]
fn mut_ref_carrier_present_for_annotated_var() {
    let expr = var_with_sort("x", ExprSort::MutRef(Box::new(ExprSort::Int)));
    assert!(expr_has_mut_ref_carrier(&expr));
}

/// MutRef nested inside a BinOp is detected.
#[test]
#[timeout(30000)]
fn mut_ref_carrier_detected_in_binop() {
    let mutref_var = var_with_sort("m", ExprSort::MutRef(Box::new(ExprSort::Bool)));
    let expr = add(int(1), mutref_var);
    assert!(expr_has_mut_ref_carrier(&expr));
}

/// MutRef nested inside Deref is detected.
#[test]
#[timeout(30000)]
fn mut_ref_carrier_detected_through_deref() {
    let mutref_var = var_with_sort("r", ExprSort::MutRef(Box::new(ExprSort::Seq)));
    let expr = deref(mutref_var);
    assert!(expr_has_mut_ref_carrier(&expr));
}

/// MutRef nested inside ITE else branch is detected.
#[test]
#[timeout(30000)]
fn mut_ref_carrier_detected_in_ite_else() {
    let mutref_var = var_with_sort("r", ExprSort::MutRef(Box::new(ExprSort::Int)));
    let expr = ite(bool_expr(true), int(0), mutref_var);
    assert!(expr_has_mut_ref_carrier(&expr));
}

/// MutRef nested inside MethodCall args is detected.
#[test]
#[timeout(30000)]
fn mut_ref_carrier_detected_in_method_call_args() {
    let mutref_var = var_with_sort("m", ExprSort::MutRef(Box::new(ExprSort::Int)));
    let expr = method_call(var("self"), "len", vec![mutref_var]);
    assert!(expr_has_mut_ref_carrier(&expr));
}

/// MutRef nested inside LogicFnCall args is detected.
#[test]
#[timeout(30000)]
fn mut_ref_carrier_detected_in_logic_fn_call() {
    let mutref_var = var_with_sort("m", ExprSort::MutRef(Box::new(ExprSort::Int)));
    let expr = logic_fn_call("myfn", vec![mutref_var]);
    assert!(expr_has_mut_ref_carrier(&expr));
}

/// MutRef nested inside Forall body is detected.
#[test]
#[timeout(30000)]
fn mut_ref_carrier_detected_in_forall_body() {
    let mutref_var = var_with_sort("m", ExprSort::MutRef(Box::new(ExprSort::Int)));
    let expr = forall("i", eq(var("i"), mutref_var));
    assert!(expr_has_mut_ref_carrier(&expr));
}

/// Expression tree with no MutRef anywhere returns false.
#[test]
#[timeout(30000)]
fn mut_ref_carrier_absent_in_complex_tree() {
    let expr = ite(
        gt(var("x"), int(0)),
        add(var("x"), int(1)),
        method_call(var("self"), "len", vec![]),
    );
    assert!(!expr_has_mut_ref_carrier(&expr));
}

/// Literals return false.
#[test]
#[timeout(30000)]
fn mut_ref_carrier_absent_for_literals() {
    assert!(!expr_has_mut_ref_carrier(&int(42)));
    assert!(!expr_has_mut_ref_carrier(&bool_expr(true)));
}

/// MutRef inside Let binding is detected.
#[test]
#[timeout(30000)]
fn mut_ref_carrier_detected_in_let_binding() {
    let mutref_var = var_with_sort("m", ExprSort::MutRef(Box::new(ExprSort::Int)));
    let expr = let_bind("tmp", mutref_var, var("tmp"));
    assert!(expr_has_mut_ref_carrier(&expr));
}

/// MutRef inside LetAssume is detected.
#[test]
#[timeout(30000)]
fn mut_ref_carrier_detected_in_let_assume() {
    let mutref_var = var_with_sort("m", ExprSort::MutRef(Box::new(ExprSort::Int)));
    let expr = let_assume(mutref_var, bool_expr(true));
    assert!(expr_has_mut_ref_carrier(&expr));
}

/// MutRef inside LetObligation is detected.
#[test]
#[timeout(30000)]
fn mut_ref_carrier_detected_in_let_obligation() {
    let mutref_var = var_with_sort("m", ExprSort::MutRef(Box::new(ExprSort::Int)));
    let expr = let_obligation(mutref_var, bool_expr(true));
    assert!(expr_has_mut_ref_carrier(&expr));
}

/// MutRef inside Match arm body is detected.
#[test]
#[timeout(30000)]
fn mut_ref_carrier_detected_in_match_arm() {
    let mutref_var = var_with_sort("m", ExprSort::MutRef(Box::new(ExprSort::Int)));
    let expr = match_expr(var("x"), vec![(Pattern::Wildcard, mutref_var)]);
    assert!(expr_has_mut_ref_carrier(&expr));
}

// ── Pattern::binds_name (was pattern_binds_var) ─────────────────

/// Wildcard pattern does not bind any variable.
#[test]
#[timeout(30000)]
fn pattern_wildcard_binds_nothing() {
    assert!(!Pattern::Wildcard.binds_name("x"));
}

/// Literal pattern does not bind any variable.
#[test]
#[timeout(30000)]
fn pattern_literal_binds_nothing() {
    assert!(!Pattern::Literal(PureExpr::Int(42)).binds_name("x"));
}

/// Binding pattern matches the bound variable name.
#[test]
#[timeout(30000)]
fn pattern_binding_matches_name() {
    assert!(Pattern::Binding("x".to_string()).binds_name("x"));
}

/// Binding pattern does not match a different name.
#[test]
#[timeout(30000)]
fn pattern_binding_rejects_different_name() {
    assert!(!Pattern::Binding("y".to_string()).binds_name("x"));
}

/// Constructor pattern with inner binding matches.
#[test]
#[timeout(30000)]
fn pattern_constructor_with_inner_binding() {
    let pat = Pattern::Constructor {
        name: "Some".to_string(),
        inner: Some(Box::new(Pattern::Binding("v".to_string()))),
    };
    assert!(pat.binds_name("v"));
    assert!(!pat.binds_name("w"));
}

/// Constructor pattern without inner does not bind.
#[test]
#[timeout(30000)]
fn pattern_constructor_without_inner() {
    let pat = Pattern::Constructor {
        name: "None".to_string(),
        inner: None,
    };
    assert!(!pat.binds_name("x"));
}

/// Tuple pattern binds if any element matches.
#[test]
#[timeout(30000)]
fn pattern_tuple_binds_element() {
    let pat = Pattern::Tuple(vec![
        Pattern::Binding("a".to_string()),
        Pattern::Wildcard,
        Pattern::Binding("c".to_string()),
    ]);
    assert!(pat.binds_name("a"));
    assert!(!pat.binds_name("b"));
    assert!(pat.binds_name("c"));
}

/// Empty tuple pattern binds nothing.
#[test]
#[timeout(30000)]
fn pattern_empty_tuple_binds_nothing() {
    let pat = Pattern::Tuple(vec![]);
    assert!(!pat.binds_name("x"));
}

// ── expr_has_bitwise_ops edge cases ─────────────────────────────

/// Pure arithmetic with no bitwise ops returns false.
#[test]
#[timeout(30000)]
fn bitwise_absent_in_pure_arithmetic() {
    let expr = add(mul(var("x"), int(2)), sub(var("y"), int(1)));
    assert!(!expr_has_bitwise_ops(&expr));
}

/// Bitwise ops nested in ITE are detected.
#[test]
#[timeout(30000)]
fn bitwise_detected_in_ite() {
    let bw = PureExpr::BinOp(
        std::sync::Arc::new(var("x")),
        trust_wp_core::formula::BinOp::BitAnd,
        std::sync::Arc::new(int(0xFF)),
    );
    let expr = ite(bool_expr(true), int(0), bw);
    assert!(expr_has_bitwise_ops(&expr));
}

// ── expr_has_uf_method_call edge cases ──────────────────────────

/// Plain variable access returns false.
#[test]
#[timeout(30000)]
fn uf_method_absent_for_var() {
    assert!(!expr_has_uf_method_call(&var("x")));
}

/// Non-UF method (e.g., arithmetic) returns false.
#[test]
#[timeout(30000)]
fn uf_method_absent_for_non_uf_method() {
    // "len" is not in is_uf_injecting_method list (it routes through Seq)
    // but "deep_model" IS in the list
    let expr = method_call(var("x"), "some_user_method", vec![]);
    assert!(!expr_has_uf_method_call(&expr));
}

/// UF-injecting method "deep_model" is detected.
#[test]
#[timeout(30000)]
fn uf_method_detected_for_deep_model() {
    let expr = method_call(var("x"), "deep_model", vec![]);
    assert!(expr_has_uf_method_call(&expr));
}

/// UF-injecting method "ext_eq" is detected.
#[test]
#[timeout(30000)]
fn uf_method_detected_for_ext_eq() {
    let expr = method_call(var("s1"), "ext_eq", vec![var("s2")]);
    assert!(expr_has_uf_method_call(&expr));
}

/// UF-injecting method "produces" is detected.
#[test]
#[timeout(30000)]
fn uf_method_detected_for_produces() {
    let expr = method_call(var("iter"), "produces", vec![var("seq"), var("iter2")]);
    assert!(expr_has_uf_method_call(&expr));
}

/// UF method nested inside Forall body is detected.
#[test]
#[timeout(30000)]
fn uf_method_detected_in_forall_body() {
    let mc = method_call(var("x"), "fmap_lookup", vec![var("k")]);
    let expr = forall("k", mc);
    assert!(expr_has_uf_method_call(&expr));
}
