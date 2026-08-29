// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Collapse `old(...)` wrappers in mutable-borrow postconditions.
//!
//! In RustHorn-style mut-borrow verification, `old(*v)` is equivalent to `*v`
//! because `*v` already maps to `v_current` (the entry-state value). This module
//! recursively strips redundant `Old(...)` wrappers when all sub-expressions are
//! provably entry-state expressions (literals, derefs of mut-ref params, non-mut-ref
//! vars).
//!
//! Extracted from `mut_borrow.rs` as part of #1865 mid-tier decomposition.

use std::collections::HashSet;

use trust_wp_core::formula::PureExpr;

pub(crate) fn collapse_old_over_mut_ref_currents(
    expr: &PureExpr,
    mut_ref_params: &HashSet<String>,
) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::Old(inner)
            if old_body_is_mut_ref_entry_expr(inner.as_ref(), mut_ref_params, false) =>
        {
            inner.as_ref().clone()
        }
        other => other,
    })
}

pub(super) fn old_body_is_mut_ref_entry_expr(
    expr: &PureExpr,
    mut_ref_params: &HashSet<String>,
    under_deref: bool,
) -> bool {
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => true,
        PureExpr::Var(name, _) => !mut_ref_params.contains(name) || under_deref,
        PureExpr::Deref(inner) => old_body_is_mut_ref_entry_expr(inner, mut_ref_params, true),
        PureExpr::View(inner) | PureExpr::Old(inner) => {
            old_body_is_mut_ref_entry_expr(inner, mut_ref_params, under_deref)
        }
        PureExpr::BinOp(l, _, r) => {
            old_body_is_mut_ref_entry_expr(l, mut_ref_params, under_deref)
                && old_body_is_mut_ref_entry_expr(r, mut_ref_params, under_deref)
        }
        PureExpr::UnOp(_, inner) => {
            old_body_is_mut_ref_entry_expr(inner, mut_ref_params, under_deref)
        }
        PureExpr::Ite(c, t, e) => {
            old_body_is_mut_ref_entry_expr(c, mut_ref_params, under_deref)
                && old_body_is_mut_ref_entry_expr(t, mut_ref_params, under_deref)
                && old_body_is_mut_ref_entry_expr(e, mut_ref_params, under_deref)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            old_body_is_mut_ref_entry_expr(receiver, mut_ref_params, under_deref)
                && args
                    .iter()
                    .all(|a| old_body_is_mut_ref_entry_expr(a, mut_ref_params, under_deref))
        }
        PureExpr::LogicFnCall { args, .. } => args
            .iter()
            .all(|a| old_body_is_mut_ref_entry_expr(a, mut_ref_params, under_deref)),
        PureExpr::Final(_) => false,
        PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => {
            old_body_is_mut_ref_entry_expr(body, mut_ref_params, under_deref)
        }
        PureExpr::Match { scrutinee, arms } => {
            old_body_is_mut_ref_entry_expr(scrutinee, mut_ref_params, under_deref)
                && arms.iter().all(|arm| {
                    old_body_is_mut_ref_entry_expr(&arm.body, mut_ref_params, under_deref)
                })
        }
        PureExpr::Let { value, body, .. } => {
            old_body_is_mut_ref_entry_expr(value, mut_ref_params, under_deref)
                && old_body_is_mut_ref_entry_expr(body, mut_ref_params, under_deref)
        }
        PureExpr::LetAssume {
            assumption, body, ..
        } => {
            old_body_is_mut_ref_entry_expr(assumption, mut_ref_params, under_deref)
                && old_body_is_mut_ref_entry_expr(body, mut_ref_params, under_deref)
        }
        PureExpr::LetObligation {
            obligation, body, ..
        } => {
            old_body_is_mut_ref_entry_expr(obligation, mut_ref_params, under_deref)
                && old_body_is_mut_ref_entry_expr(body, mut_ref_params, under_deref)
        }
        PureExpr::Closure { body, .. } => {
            old_body_is_mut_ref_entry_expr(body, mut_ref_params, under_deref)
        }
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, sync::Arc};

    use ntest::timeout;
    use trust_wp_core::formula::{BinOp, PureExpr};

    use super::{collapse_old_over_mut_ref_currents, old_body_is_mut_ref_entry_expr};
    use crate::tests::helpers::{deref, final_expr, var};

    #[test]
    #[timeout(30000)]
    fn test_collapse_old_over_mut_ref_view_arithmetic() {
        let expr = PureExpr::Old(Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                PureExpr::Var("x".to_string(), None),
            ))))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )));
        let params: HashSet<String> = ["x".to_string()].into_iter().collect();

        let collapsed = collapse_old_over_mut_ref_currents(&expr, &params);

        match &collapsed {
            PureExpr::BinOp(lhs, BinOp::Add, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
                (PureExpr::View(inner_view), PureExpr::Int(1)) => match inner_view.as_ref() {
                    PureExpr::Deref(inner_deref) => match inner_deref.as_ref() {
                        PureExpr::Var(name, _) => assert_eq!(name, "x"),
                        other => panic!("expected Var(\"x\"), got {other:?}"),
                    },
                    other => panic!("expected Deref(...), got {other:?}"),
                },
                (lhs, rhs) => {
                    panic!("expected View(Deref(Var(\"x\"))) + Int(1), got {lhs:?} + {rhs:?}")
                }
            },
            other => panic!("expected BinOp(_, Add, _), got {other:?}"),
        }
    }

    #[test]
    #[timeout(30000)]
    fn test_collapse_old_strips_when_all_vars_are_entry_safe() {
        let expr = PureExpr::Old(Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("y".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                PureExpr::Var("x".to_string(), None),
            ))))),
        )));
        let params: HashSet<String> = ["x".to_string()].into_iter().collect();

        let collapsed = collapse_old_over_mut_ref_currents(&expr, &params);

        assert!(
            !matches!(collapsed, PureExpr::Old(_)),
            "Old should be stripped when all sub-exprs are entry-safe, got {collapsed:?}"
        );
        assert!(
            matches!(collapsed, PureExpr::BinOp(_, BinOp::Add, _)),
            "collapsed form should be BinOp(..., Add, ...), got {collapsed:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_collapse_old_keeps_bare_mut_ref_param() {
        let expr = PureExpr::Old(Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )));
        let params: HashSet<String> = ["x".to_string()].into_iter().collect();

        let collapsed = collapse_old_over_mut_ref_currents(&expr, &params);

        assert!(
            matches!(collapsed, PureExpr::Old(_)),
            "Old must be kept when bare mut-ref param appears without Deref, got {collapsed:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_old_body_bare_var_not_entry_expr() {
        let params: HashSet<String> = ["x".to_string()].into_iter().collect();
        let expr = PureExpr::Var("x".to_string(), None);
        assert!(!old_body_is_mut_ref_entry_expr(&expr, &params, false));
    }

    #[test]
    #[timeout(30000)]
    fn test_old_body_deref_var_is_entry_expr() {
        let params: HashSet<String> = ["x".to_string()].into_iter().collect();
        assert!(old_body_is_mut_ref_entry_expr(
            &deref(var("x")),
            &params,
            false
        ));
    }

    #[test]
    #[timeout(30000)]
    fn test_old_body_deref_non_param_is_entry() {
        let params: HashSet<String> = ["x".to_string()].into_iter().collect();
        assert!(old_body_is_mut_ref_entry_expr(
            &deref(var("y")),
            &params,
            false
        ));
    }

    #[test]
    #[timeout(30000)]
    fn test_old_body_final_rejected() {
        let params: HashSet<String> = ["x".to_string()].into_iter().collect();
        assert!(!old_body_is_mut_ref_entry_expr(
            &final_expr(var("x")),
            &params,
            false
        ));
    }
}
