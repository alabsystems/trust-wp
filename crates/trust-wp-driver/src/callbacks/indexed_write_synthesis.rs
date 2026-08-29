// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IndexMut postcondition synthesis from MIR indexed writes.
//!
//! When the MIR body contains `(*param)[idx] = val`, rustc inlines the
//! IndexMut call into a direct place projection. The mut_borrow extractor
//! records these as `indexed_writes`. This module synthesizes the equivalent
//! postconditions that the IndexMut extern spec would have provided:
//!
//! For each parameter with indexed writes:
//!   1. Point-write per write: `(^param)@.index_logic(idx_k) == val_k`
//!   2. Single length preservation: `(^param)@.len() == (*param)@.len()`
//!   3. Single combined frame:
//!      `forall i, i != idx_0 && ... && i != idx_n ==> (^param)@[i] == (*param)@[i]`
//!
//! Combining the frame avoids contradictory per-write frames when a body
//! writes to multiple indices of the same parameter (#1317, #1638).

use std::{collections::HashMap, sync::Arc};

use tracing::debug;
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use super::super::mir_analysis::IndexedWrite;

pub(super) fn group_indexed_writes_by_param(
    indexed_writes: &[IndexedWrite],
) -> Vec<(String, Vec<&IndexedWrite>)> {
    let mut grouped: Vec<(String, Vec<&IndexedWrite>)> = Vec::new();
    let mut param_positions: HashMap<String, usize> = HashMap::new();
    for iw in indexed_writes {
        if let Some(pos) = param_positions.get(&iw.param_name).copied() {
            grouped[pos].1.push(iw);
        } else {
            let pos = grouped.len();
            param_positions.insert(iw.param_name.clone(), pos);
            grouped.push((iw.param_name.clone(), vec![iw]));
        }
    }
    grouped
}

pub(super) fn build_combined_indexed_write_frame(
    current_view: &PureExpr,
    final_view: &PureExpr,
    excluded_indices: &[PureExpr],
) -> PureExpr {
    let qvar = PureExpr::Var("__iw_i".to_string(), Some(ExprSort::Int));
    let mut antecedent = PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Int(0)),
            BinOp::Le,
            Arc::new(qvar.clone()),
        )),
        BinOp::And,
        Arc::new(PureExpr::BinOp(
            Arc::new(qvar.clone()),
            BinOp::Lt,
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(current_view.clone()),
                method: "len".to_string(),
                args: vec![],
            }),
        )),
    );
    for excluded_idx in excluded_indices {
        antecedent = PureExpr::BinOp(
            Arc::new(antecedent),
            BinOp::And,
            Arc::new(PureExpr::BinOp(
                Arc::new(qvar.clone()),
                BinOp::Ne,
                Arc::new(excluded_idx.clone()),
            )),
        );
    }
    PureExpr::Forall {
        var: "__iw_i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(antecedent),
            BinOp::Implies,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(final_view.clone()),
                    method: "index_logic".to_string(),
                    args: vec![qvar.clone()],
                }),
                BinOp::Eq,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(current_view.clone()),
                    method: "index_logic".to_string(),
                    args: vec![qvar],
                }),
            )),
        )),
        triggers: vec![],
    }
}

pub(super) fn synthesize_indexed_write_postconditions(
    indexed_writes: &[IndexedWrite],
    effective_requires: &mut Vec<PureExpr>,
    verbose: bool,
) {
    for (param_name, writes) in group_indexed_writes_by_param(indexed_writes) {
        let param_var = PureExpr::Var(param_name, Some(ExprSort::Ref(Box::new(ExprSort::Seq))));
        let final_view = PureExpr::View(Arc::new(PureExpr::Final(Arc::new(param_var.clone()))));
        let current_view = PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(param_var))));

        for iw in &writes {
            let point_write = PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(final_view.clone()),
                    method: "index_logic".to_string(),
                    args: vec![iw.index.clone()],
                }),
                BinOp::Eq,
                Arc::new(iw.value.clone()),
            );
            effective_requires.push(point_write);
            if verbose {
                debug!(
                    "trust-wp:   (synthesized IndexMut point-write for {}[{:?}] = {:?})",
                    iw.param_name, iw.index, iw.value
                );
            }
        }

        let len_preservation = PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(final_view.clone()),
                method: "len".to_string(),
                args: vec![],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(current_view.clone()),
                method: "len".to_string(),
                args: vec![],
            }),
        );
        effective_requires.push(len_preservation);

        let excluded_indices: Vec<PureExpr> = writes.iter().map(|iw| iw.index.clone()).collect();
        effective_requires.push(build_combined_indexed_write_frame(
            &current_view,
            &final_view,
            &excluded_indices,
        ));

        if verbose {
            debug!(
                "trust-wp:   (synthesized combined IndexMut frame for {} with {} indexed write(s))",
                writes[0].param_name,
                writes.len()
            );
        }
    }
}
