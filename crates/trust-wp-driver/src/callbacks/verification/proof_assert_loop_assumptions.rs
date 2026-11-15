// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared helpers for contracted proof_assert loop-assumption handling.
//!
//! These utilities are used by the proof_assert driver when a proof_assert
//! appears after a loop and needs loop-exit assumptions rewritten into the
//! snapshot's local variable namespace.

use trust_wp_core::formula::PureExpr;

use super::super::{
    iterator_spec_rewrite::rewrite_iterator_spec_expr,
    proof_assert_extract::collapse_idempotent_views,
};
use crate::mir_analysis::NameSubstitutions;

pub(super) fn proof_assert_after_all_loops(
    span: rustc_span::Span,
    loop_spans: &[(u32, u32)],
) -> bool {
    if loop_spans.is_empty() {
        return false;
    }
    let callsite = span.source_callsite();
    let pa_start = callsite.lo().0;
    loop_spans.iter().all(|(_, end)| *end <= pa_start)
}

pub(super) fn rewrite_post_loop_proof_assert_assumptions(
    assumptions: &[PureExpr],
    substitutions: &NameSubstitutions,
) -> Vec<PureExpr> {
    if assumptions.is_empty() {
        return Vec::new();
    }

    assumptions
        .iter()
        .cloned()
        .map(|expr| {
            let expr = if substitutions.is_empty() {
                expr
            } else {
                expr.substitute(substitutions)
            };
            collapse_idempotent_views(rewrite_iterator_spec_expr(&collapse_idempotent_views(expr)))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, sync::Arc};

    use rustc_span::BytePos;
    use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr};

    use super::{proof_assert_after_all_loops, rewrite_post_loop_proof_assert_assumptions};
    use crate::mir_analysis::NameSubstitutions;

    #[test]
    fn test_proof_assert_after_all_loops_accepts_post_loop_span() {
        let span = rustc_span::Span::with_root_ctxt(BytePos(50), BytePos(55));
        assert!(proof_assert_after_all_loops(span, &[(10, 40)]));
    }

    #[test]
    fn test_proof_assert_after_all_loops_rejects_in_loop_and_pre_loop_spans() {
        let in_loop = rustc_span::Span::with_root_ctxt(BytePos(20), BytePos(25));
        let pre_loop = rustc_span::Span::with_root_ctxt(BytePos(5), BytePos(8));
        assert!(!proof_assert_after_all_loops(in_loop, &[(10, 40)]));
        assert!(!proof_assert_after_all_loops(pre_loop, &[(10, 40)]));
    }

    #[test]
    fn test_post_loop_assumptions_apply_snapshot_substitutions() {
        let assumptions = vec![PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), Some(ExprSort::Int))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(7)),
        )];
        let substitutions = NameSubstitutions::new(
            HashMap::from([(
                "result".to_string(),
                PureExpr::Var("result_state".to_string(), Some(ExprSort::Int)),
            )]),
            HashMap::from([("result".to_string(), Some(ExprSort::Int))]),
        );

        let rewritten = rewrite_post_loop_proof_assert_assumptions(&assumptions, &substitutions);

        assert_eq!(rewritten.len(), 1);
        assert_eq!(
            rewritten[0],
            PureExpr::BinOp(
                Arc::new(PureExpr::Var(
                    "result_state".to_string(),
                    Some(ExprSort::Int)
                )),
                BinOp::Eq,
                Arc::new(PureExpr::Int(7)),
            )
        );
    }

    #[test]
    fn test_post_loop_assumptions_rewrite_iterator_specs_after_substitution() {
        let into_iter_sort = Some(ExprSort::Datatype(intern_sort_name(
            "alloc::vec::into_iter::IntoIter",
        )));
        let assumptions = vec![PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("iter".to_string(), into_iter_sort.clone())),
            method: "completed".to_string(),
            args: vec![],
        }];
        let substitutions = NameSubstitutions::new(
            HashMap::from([(
                "iter".to_string(),
                PureExpr::Var("iter_state".to_string(), into_iter_sort.clone()),
            )]),
            HashMap::from([("iter".to_string(), into_iter_sort.clone())]),
        );

        let rewritten = rewrite_post_loop_proof_assert_assumptions(&assumptions, &substitutions);

        assert_eq!(rewritten.len(), 1);
        let PureExpr::BinOp(lhs, op, rhs) = &rewritten[0] else {
            panic!(
                "expected completed() rewrite to len() == 0, got {:?}",
                rewritten[0]
            );
        };
        assert_eq!(*op, BinOp::Eq);
        assert_eq!(rhs.as_ref(), &PureExpr::Int(0));
        let PureExpr::MethodCall {
            receiver, method, ..
        } = lhs.as_ref()
        else {
            panic!("expected len() method call, got {:?}", lhs);
        };
        assert_eq!(method, "len");
        assert!(
            matches!(
                receiver.as_ref(),
                PureExpr::View(inner)
                    if matches!(
                        inner.as_ref(),
                        PureExpr::Var(name, sort)
                            if name == "iter_state" && *sort == into_iter_sort
                    )
            ),
            "receiver should be the substituted iterator state, got {:?}",
            receiver
        );
    }

    #[test]
    fn test_snapshot_post_loop_assumptions_skip_stale_snapshot_substitutions() {
        let assumptions = vec![PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(3)),
        )];
        let substitutions = NameSubstitutions::new(
            HashMap::from([("i".to_string(), PureExpr::Int(0))]),
            HashMap::from([("i".to_string(), Some(ExprSort::Int))]),
        );

        let rewritten = rewrite_post_loop_proof_assert_assumptions(&assumptions, &substitutions);
        assert_eq!(
            rewritten,
            vec![PureExpr::BinOp(
                Arc::new(PureExpr::Int(0)),
                BinOp::Eq,
                Arc::new(PureExpr::Int(3)),
            )]
        );
    }
}
