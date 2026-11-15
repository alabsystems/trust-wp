// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Generic loop condition extraction and shared helpers (#1669, #2309).
//!
//! Extracts loop continuation conditions from MIR `SwitchInt` terminators for
//! `while`/`while let` loops. Range-synthesis and iterator analysis live in
//! sibling modules `for_range` and `for_loop_iter`.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_middle::mir::{
    BasicBlock, Body, Local, Operand, StatementKind, SwitchTargets, TerminatorKind,
};
use trust_wp_core::formula::{BinOp, PureExpr, UnOp};

use super::{
    super::translate::{
        operand_int_ty, operand_is_bool, switch_value_to_i64, translate_operand, translate_rvalue,
        DiscrIntTy,
    },
    detection::LoopInfo,
};

/// Scan loop body blocks for a `SwitchInt` that exits the loop (break pattern).
///
/// For `loop { ... if cond { break; } ... }` patterns where the break is not
/// at the loop header, the condition block is somewhere in the loop body.
/// This function finds the unique SwitchInt in the body with an exit edge and
/// extracts the negated condition (continuation condition).
///
/// Returns `None` if there are multiple SwitchInt exits (ambiguous) or none;
/// otherwise the break `SwitchInt` block and the continuation condition.
pub(super) fn find_body_break_condition(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    local_exprs: &HashMap<Local, PureExpr>,
    all_loops: Option<&[LoopInfo]>,
) -> Option<(BasicBlock, PureExpr)> {
    let mut candidates: Vec<(BasicBlock, PureExpr)> = Vec::new();

    // Collect blocks belonging to inner loops (skip those — their SwitchInt
    // controls inner loop flow, not this loop's break).
    let mut inner_loop_blocks: HashSet<BasicBlock> = HashSet::new();
    if let Some(loops) = all_loops {
        for other in loops {
            if other.header != loop_info.header && loop_info.body_blocks.contains(&other.header) {
                inner_loop_blocks.extend(&other.body_blocks);
            }
        }
    }

    for &bb in &loop_info.body_blocks {
        if bb == loop_info.header || inner_loop_blocks.contains(&bb) {
            continue;
        }
        let bb_data = &body.basic_blocks[bb];
        if let TerminatorKind::SwitchInt { discr, targets } = &bb_data.terminator().kind {
            if targets.all_targets().len() < 2 {
                continue;
            }
            if !operand_is_bool(discr, body) {
                continue;
            }

            // Check: does this SwitchInt have exactly one exit target?
            let otherwise_bb = targets.otherwise();
            let otherwise_exits = !loop_info.body_blocks.contains(&otherwise_bb);

            let mut explicit_exit_count = 0;
            for (_, target) in targets.iter() {
                if !loop_info.body_blocks.contains(&target) {
                    explicit_exit_count += 1;
                }
            }

            let has_exit = otherwise_exits || explicit_exit_count > 0;
            if !has_exit {
                continue;
            }

            // Resolve temporaries from this block's statements
            let mut block_local_exprs = local_exprs.clone();
            for stmt in &bb_data.statements {
                if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
                    if place.projection.is_empty() {
                        if let Some(expr) = translate_rvalue(rvalue, &block_local_exprs, Some(body))
                        {
                            block_local_exprs.insert(place.local, expr);
                        }
                    }
                }
            }

            if let Some(cond) = translate_operand(discr, &block_local_exprs) {
                // If the otherwise (true) branch exits, the condition is a break
                // condition → negate for continuation. If false branch exits,
                // condition is continuation as-is.
                let continuation_cond = if otherwise_exits {
                    PureExpr::UnOp(UnOp::Not, Arc::new(cond))
                } else {
                    cond
                };
                candidates.push((bb, continuation_cond));
            }
        }
    }

    // Only use if there's exactly one break-exit point (unambiguous).
    if candidates.len() == 1 {
        candidates.into_iter().next()
    } else {
        None
    }
}

pub(super) fn base_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner)
        | PureExpr::View(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner) => base_var_name(inner),
        _ => None,
    }
}

/// Convert a non-bool SwitchInt discriminant to a boolean loop condition.
///
/// For `while let Some(_) = b`, MIR produces `switchInt(discriminant(b)) -> [0: exit, ..]`.
/// The discriminant is Int-sorted, but the loop verifier needs a Bool condition.
///
/// Collects ALL body-continuing branch values and generates a disjunction of equalities,
/// which is correct for enums with any number of variants. (#352, #1001)
pub(super) fn whilelet_condition(
    discr: &Operand<'_>,
    targets: &SwitchTargets,
    body: &Body<'_>,
    local_exprs: &HashMap<Local, PureExpr>,
    loop_info: &LoopInfo,
) -> Option<PureExpr> {
    let discr_expr = translate_operand(discr, local_exprs)?;
    let discr_int_ty = operand_int_ty(discr, body);

    // Partition explicit SwitchInt values into body-continuing and exit values.
    let mut body_values: Vec<i64> = Vec::new();
    let mut exit_values: Vec<i64> = Vec::new();
    for (value, target) in targets.iter() {
        let val = switch_target_value_to_i64(value, discr_int_ty)?;
        if loop_info.body_blocks.contains(&target) {
            body_values.push(val);
        } else {
            exit_values.push(val);
        }
    }

    let otherwise_is_body = loop_info.body_blocks.contains(&targets.otherwise());

    if !body_values.is_empty() && !otherwise_is_body {
        // Body values are explicitly enumerated; generate `discr == v1 || discr == v2 || ...`.
        // For the common 2-variant case this produces a single `discr == body_val`.
        let mut cond = PureExpr::BinOp(
            Arc::new(discr_expr.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::Int(body_values[0])),
        );
        for &val in &body_values[1..] {
            cond = PureExpr::BinOp(
                Arc::new(cond),
                BinOp::Or,
                Arc::new(PureExpr::BinOp(
                    Arc::new(discr_expr.clone()),
                    BinOp::Eq,
                    Arc::new(PureExpr::Int(val)),
                )),
            );
        }
        Some(cond)
    } else if exit_values.len() == 1 && otherwise_is_body {
        // Single explicit exit value, otherwise continues the loop:
        // `discr != exit_value`.
        Some(PureExpr::BinOp(
            Arc::new(discr_expr),
            BinOp::Ne,
            Arc::new(PureExpr::Int(exit_values[0])),
        ))
    } else if !exit_values.is_empty() && otherwise_is_body {
        // Multiple explicit exit values, otherwise continues the loop:
        // `discr != exit1 && discr != exit2 && ...`.
        let mut cond = PureExpr::BinOp(
            Arc::new(discr_expr.clone()),
            BinOp::Ne,
            Arc::new(PureExpr::Int(exit_values[0])),
        );
        for &val in &exit_values[1..] {
            cond = PureExpr::BinOp(
                Arc::new(cond),
                BinOp::And,
                Arc::new(PureExpr::BinOp(
                    Arc::new(discr_expr.clone()),
                    BinOp::Ne,
                    Arc::new(PureExpr::Int(val)),
                )),
            );
        }
        Some(cond)
    } else {
        None
    }
}

pub(super) fn switch_target_value_to_i64(
    value: u128,
    discr_int_ty: Option<DiscrIntTy>,
) -> Option<i64> {
    if let Some(discr_int_ty) = discr_int_ty {
        switch_value_to_i64(value, discr_int_ty)
    } else {
        i64::try_from(value).ok()
    }
}
