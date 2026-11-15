// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, sync::Arc};

use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr, UnOp};

use super::*;
use crate::mir_analysis::NameSubstitutions;

#[path = "tests/normalize_scalar_proof_assert_boundary.rs"]
mod normalize_scalar_proof_assert_boundary;
#[path = "tests/resolve_internal_references.rs"]
mod resolve_internal_references;
#[path = "tests/strip_call_effects.rs"]
mod strip_call_effects;
#[path = "tests/substitution_assumptions.rs"]
mod substitution_assumptions;

#[test]
fn simplify_proof_assert_expr_rewrites_reflexive_quantifier_tautologies() {
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )),
        )),
        triggers: Vec::new(),
    };

    assert_eq!(simplify_proof_assert_expr(expr), PureExpr::Bool(true));
}

fn x_int() -> Arc<PureExpr> {
    Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int)))
}

fn x_cmp(op: BinOp, bound: i64) -> Arc<PureExpr> {
    Arc::new(PureExpr::BinOp(x_int(), op, Arc::new(PureExpr::Int(bound))))
}

/// `forall<x: u8> body` as the parser states it: the range premise wraps the
/// body (D-203).
fn u8_ranged_forall(body: PureExpr) -> PureExpr {
    let range = PureExpr::BinOp(x_cmp(BinOp::Ge, 0), BinOp::And, x_cmp(BinOp::Lt, 256));
    PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(range),
            BinOp::Implies,
            Arc::new(body),
        )),
        triggers: Vec::new(),
    }
}

#[test]
fn simplify_proof_assert_expr_sees_a_tautology_under_a_binder_range_premise() {
    let tautology = PureExpr::BinOp(x_cmp(BinOp::Ge, 0), BinOp::Implies, x_cmp(BinOp::Ge, 0));
    assert_eq!(
        simplify_proof_assert_expr(u8_ranged_forall(tautology)),
        PureExpr::Bool(true)
    );
}

#[test]
fn simplify_proof_assert_expr_keeps_a_non_tautology_under_a_binder_range_premise() {
    let claim = PureExpr::BinOp(x_cmp(BinOp::Ge, 0), BinOp::Implies, x_cmp(BinOp::Ge, 1));
    let expr = u8_ranged_forall(claim);
    assert_eq!(simplify_proof_assert_expr(expr.clone()), expr);
}

#[test]
fn simplify_proof_assert_expr_rewrites_exists_reflexive_equality() {
    let expr = PureExpr::Exists {
        var: "y".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("y".to_string(), Some(ExprSort::Int))),
            BinOp::Eq,
            Arc::new(PureExpr::Var("y".to_string(), Some(ExprSort::Int))),
        )),
        triggers: Vec::new(),
    };

    assert_eq!(simplify_proof_assert_expr(expr), PureExpr::Bool(true));
}

#[test]
fn resolve_internal_references_transitive_chain() {
    // "a" → Var("b"), "b" → Int(5), "c" → Var("a") + Var("b")
    // After resolution: "c" → Int(5) + Int(5) (both a→b→5 and b→5 resolved)
    // Note: single-pass, so "a" resolves b→5 giving "a" → Int(5)
    // and "c" resolves a→Var("b") and b→5 giving c = Var("b") + 5
    // then Var("b") is NOT further resolved (single pass).
    let mut subs = HashMap::new();
    subs.insert("a".to_string(), PureExpr::Var("b".to_string(), None));
    subs.insert("b".to_string(), PureExpr::Int(5));
    subs.insert(
        "c".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("a".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Var("b".to_string(), None)),
        ),
    );

    resolve_internal_references(&mut subs);

    // "a" → Int(5) (b resolved to 5)
    assert_eq!(subs["a"], PureExpr::Int(5));
    // "b" → Int(5) (no other var to resolve, stays literal)
    assert_eq!(subs["b"], PureExpr::Int(5));
    // "c": a→Var("b") substituted + b→5 substituted = Var("b") + 5
    // Single pass means Var("a") becomes Var("b") (from snapshot), not Int(5)
    assert_eq!(
        subs["c"],
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("b".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(5)),
        ),
        "single-pass resolution: a→b is substituted as snapshot value Var(b), not transitively to 5"
    );
}

#[test]
fn simplify_proof_assert_expr_non_reflexive_implication_unchanged() {
    // forall<x> (x > 0 ==> x > 1) — not reflexive, should NOT be simplified
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
                BinOp::Ge,
                Arc::new(PureExpr::Int(1)),
            )),
        )),
        triggers: Vec::new(),
    };

    let result = simplify_proof_assert_expr(expr.clone());
    assert_eq!(
        result, expr,
        "non-reflexive implication should not be simplified"
    );
}
