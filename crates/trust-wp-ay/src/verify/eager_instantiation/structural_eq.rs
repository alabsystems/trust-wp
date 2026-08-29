// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Structural equality for PureExpr that ignores `ExprSort` annotations on `Var` nodes.
//!
//! Extracted from `matching.rs` to keep both files under the 500-line limit.
//! The core invariant: two expressions are structurally equal iff they have the
//! same shape and all leaf values match, but `Var("x", Some(Int))` equals
//! `Var("x", None)` — sort annotations are ignored at all nesting depths.

use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

/// Check if two expressions are structurally equal.
///
/// Sort annotations on `Var` nodes are ignored — matching is by name only.
/// This ensures that sort-enriched ground calls (from `normalize_deref_final`)
/// can match against unannotated body vars in eager instantiation, preventing
/// missed instantiations when ExprSort enrichment produces richer annotations.
pub(crate) fn exprs_structurally_equal(a: &PureExpr, b: &PureExpr) -> bool {
    match (a, b) {
        (PureExpr::Var(na, _), PureExpr::Var(nb, _)) => na == nb,
        (PureExpr::Bool(a), PureExpr::Bool(b)) => a == b,
        (PureExpr::Int(a), PureExpr::Int(b)) => a == b,
        (PureExpr::Float(a), PureExpr::Float(b)) => a == b,
        (PureExpr::BinOp(al, aop, ar), PureExpr::BinOp(bl, bop, br)) => {
            aop == bop && exprs_structurally_equal(al, bl) && exprs_structurally_equal(ar, br)
        }
        (PureExpr::UnOp(aop, ai), PureExpr::UnOp(bop, bi)) => {
            aop == bop && exprs_structurally_equal(ai, bi)
        }
        (PureExpr::Ite(ac, at, ae), PureExpr::Ite(bc, bt, be)) => {
            exprs_structurally_equal(ac, bc)
                && exprs_structurally_equal(at, bt)
                && exprs_structurally_equal(ae, be)
        }
        (PureExpr::Old(a), PureExpr::Old(b))
        | (PureExpr::Deref(a), PureExpr::Deref(b))
        | (PureExpr::Final(a), PureExpr::Final(b))
        | (PureExpr::View(a), PureExpr::View(b)) => exprs_structurally_equal(a, b),
        (
            PureExpr::MethodCall {
                receiver: ar,
                method: am,
                args: aa,
            },
            PureExpr::MethodCall {
                receiver: br,
                method: bm,
                args: ba,
            },
        ) => am == bm && exprs_structurally_equal(ar, br) && expr_list_eq(aa, ba),
        (
            PureExpr::LogicFnCall { name: an, args: aa },
            PureExpr::LogicFnCall { name: bn, args: ba },
        ) => an == bn && expr_list_eq(aa, ba),
        (
            PureExpr::LetAssume {
                assumption: aa,
                body: ab,
            },
            PureExpr::LetAssume {
                assumption: ba,
                body: bb,
            },
        ) => exprs_structurally_equal(aa, ba) && exprs_structurally_equal(ab, bb),
        (
            PureExpr::LetObligation {
                obligation: ao,
                body: ab,
            },
            PureExpr::LetObligation {
                obligation: bo,
                body: bb,
            },
        ) => exprs_structurally_equal(ao, bo) && exprs_structurally_equal(ab, bb),
        (
            PureExpr::Closure {
                params: ap,
                body: ab,
            },
            PureExpr::Closure {
                params: bp,
                body: bb,
            },
        ) => ap == bp && exprs_structurally_equal(ab, bb),
        _ => exprs_structurally_equal_binders(a, b),
    }
}

/// Binder forms: Forall, Exists, Match, Let.
/// Separated from `exprs_structurally_equal` to keep each function under 80 lines.
fn exprs_structurally_equal_binders(a: &PureExpr, b: &PureExpr) -> bool {
    match (a, b) {
        (
            PureExpr::Forall {
                var: av,
                var_sort: as_,
                body: ab,
                triggers: at,
            },
            PureExpr::Forall {
                var: bv,
                var_sort: bs,
                body: bb,
                triggers: bt,
            },
        )
        | (
            PureExpr::Exists {
                var: av,
                var_sort: as_,
                body: ab,
                triggers: at,
            },
            PureExpr::Exists {
                var: bv,
                var_sort: bs,
                body: bb,
                triggers: bt,
            },
        ) => av == bv && as_ == bs && exprs_structurally_equal(ab, bb) && trigger_list_eq(at, bt),
        (
            PureExpr::Match {
                scrutinee: as_,
                arms: aa,
            },
            PureExpr::Match {
                scrutinee: bs,
                arms: ba,
            },
        ) => exprs_structurally_equal(as_, bs) && match_arms_eq(aa, ba),
        (
            PureExpr::Let {
                var: av,
                value: aval,
                body: ab,
            },
            PureExpr::Let {
                var: bv,
                value: bval,
                body: bb,
            },
        ) => av == bv && exprs_structurally_equal(aval, bval) && exprs_structurally_equal(ab, bb),
        _ => a == b,
    }
}

fn expr_list_eq(a: &[PureExpr], b: &[PureExpr]) -> bool {
    a.len() == b.len()
        && a.iter()
            .zip(b.iter())
            .all(|(l, r)| exprs_structurally_equal(l, r))
}

fn trigger_list_eq(a: &[Vec<PureExpr>], b: &[Vec<PureExpr>]) -> bool {
    a.len() == b.len() && a.iter().zip(b.iter()).all(|(l, r)| expr_list_eq(l, r))
}

fn match_arms_eq(a: &[MatchArm], b: &[MatchArm]) -> bool {
    a.len() == b.len()
        && a.iter().zip(b.iter()).all(|(l, r)| {
            patterns_eq(&l.pattern, &r.pattern) && exprs_structurally_equal(&l.body, &r.body)
        })
}

fn patterns_eq(a: &Pattern, b: &Pattern) -> bool {
    match (a, b) {
        (Pattern::Wildcard, Pattern::Wildcard) => true,
        (Pattern::Binding(a), Pattern::Binding(b)) => a == b,
        (Pattern::Literal(a), Pattern::Literal(b)) => exprs_structurally_equal(a, b),
        (
            Pattern::Constructor {
                name: an,
                inner: ai,
            },
            Pattern::Constructor {
                name: bn,
                inner: bi,
            },
        ) => {
            an == bn
                && match (ai.as_deref(), bi.as_deref()) {
                    (Some(a), Some(b)) => patterns_eq(a, b),
                    (None, None) => true,
                    _ => false,
                }
        }
        (Pattern::Tuple(a), Pattern::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(l, r)| patterns_eq(l, r))
        }
        _ => a == b,
    }
}
