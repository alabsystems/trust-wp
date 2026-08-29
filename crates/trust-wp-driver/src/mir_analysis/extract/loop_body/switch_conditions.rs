// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared `SwitchInt` branch predicate reconstruction for loop-body analyses.

use std::{collections::HashMap, sync::Arc};

use rustc_middle::mir::{BasicBlock, Body, Local, Operand, SwitchTargets};
use trust_wp_core::formula::{BinOp, PureExpr, UnOp};

use crate::mir_analysis::translate::{
    operand_int_ty, operand_is_bool, switch_value_to_i64, translate_operand_detailed,
    TranslationDiagContext,
};

/// Compute branch condition predicates for each successor of a `SwitchInt`.
///
/// For boolean switches (if/while lowering): true branch gets `cond`,
/// false branch gets `!cond`.
///
/// For integer switches (match lowering): each explicit value branch gets
/// `discr == value`, and the otherwise branch gets the conjunction of all
/// `discr != value` predicates.
pub(super) fn switch_branch_conditions<'tcx>(
    discr: &Operand<'tcx>,
    targets: &SwitchTargets,
    local_exprs: &HashMap<Local, PureExpr>,
    body: &Body<'tcx>,
    diag: Option<&TranslationDiagContext<'_>>,
) -> Option<HashMap<BasicBlock, PureExpr>> {
    let discr_expr = translate_operand_detailed(discr, local_exprs, diag)?;

    // Boolean switch (if/while lowering): true branch gets `cond`,
    // false branch gets `!cond`.
    if operand_is_bool(discr, body) {
        let mut false_bb = None;
        let mut true_bb = None;
        for (value, target) in targets.iter() {
            if value == 0 {
                false_bb = Some(target);
            } else if value == 1 {
                true_bb = Some(target);
            }
        }
        let otherwise_bb = targets.otherwise();
        let else_bb = false_bb.unwrap_or(otherwise_bb);
        let then_bb = true_bb.unwrap_or(otherwise_bb);
        if then_bb == else_bb {
            return None;
        }
        let mut out = HashMap::new();
        out.insert(then_bb, discr_expr.clone());
        out.insert(
            else_bb,
            PureExpr::UnOp(UnOp::Not, Arc::new(discr_expr.clone())),
        );
        return Some(out);
    }

    // Integer switch (match lowering): branch predicates are equality tests
    // against explicit values; otherwise branch gets conjunction of all `!=`.
    let discr_int_ty = operand_int_ty(discr, body)?;

    let mut out: HashMap<BasicBlock, PureExpr> = HashMap::new();
    let mut otherwise_conds = Vec::new();

    for (value, target_bb) in targets.iter() {
        let value_i64 = switch_value_to_i64(value, discr_int_ty)?;
        let value_expr = PureExpr::Int(value_i64);

        let eq_cond = PureExpr::BinOp(
            Arc::new(discr_expr.clone()),
            BinOp::Eq,
            Arc::new(value_expr.clone()),
        );
        let ne_cond = PureExpr::BinOp(
            Arc::new(discr_expr.clone()),
            BinOp::Ne,
            Arc::new(value_expr),
        );
        otherwise_conds.push(ne_cond);

        if let Some(existing) = out.get_mut(&target_bb) {
            let combined =
                PureExpr::BinOp(Arc::new(existing.clone()), BinOp::Or, Arc::new(eq_cond));
            *existing = combined;
        } else {
            out.insert(target_bb, eq_cond);
        }
    }

    if let Some(otherwise_cond) = conjunction(otherwise_conds) {
        out.insert(targets.otherwise(), otherwise_cond);
    }

    Some(out)
}

fn conjunction(mut exprs: Vec<PureExpr>) -> Option<PureExpr> {
    let first = exprs.pop()?;
    Some(exprs.into_iter().fold(first, |acc, expr| {
        PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(expr))
    }))
}
