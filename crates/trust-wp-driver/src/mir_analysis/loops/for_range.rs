// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Range-synthesis loop condition extraction (#2309).
//!
//! Synthesizes conditions for `for i in start..end` range loops and recovers
//! range bounds from pre-header MIR blocks.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_middle::mir::{
    BasicBlock, Body, Local, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_logic_fn_arity, tuple_logic_fn_name},
    BinOp, ExprSort, PureExpr,
};

use super::{
    super::{
        call_resolve::extract_call_def_id,
        translate::{translate_operand, translate_rvalue},
    },
    detection::LoopInfo,
    for_loop_iter::{resolve_for_loop_next_call, resolve_iterator_local_from_next_arg},
    CallSpecContext,
};

/// Synthesize a loop condition for MIR-desugared `for i in start..end` loops.
///
/// The desugared outer loop shape is:
/// - header terminator: `Call(Iterator::next(&mut iter), dest = opt, target = switch_bb)`
/// - `switch_bb`: `SwitchInt(discriminant(opt))`
/// - body-entry block assigns loop variable: `i = ((_opt as Some).0)`
///
/// We recover `start..end` from pre-header blocks:
/// - preheader statement: `iter = move iter_tmp`
/// - preheader predecessor call: `iter_tmp = IntoIterator::into_iter(range_expr)`
///
/// If `range_expr` translates to a tuple2-like constructor, synthesize the
/// continuation fact `produced.len() < (end - start)`.
///
/// The yielded element value is not part of the loop guard: it is introduced by
/// `Iterator::next` inside the loop body. Conjoining a recovered or synthetic
/// loop-element bound (`start <= i && i < end`) makes `!condition` too weak at
/// loop exit because it can hold through an unconstrained synthetic element
/// variable even when the iterator is not proven exhausted. (#2171)
pub(super) fn synthesize_for_range_condition(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    local_exprs: &HashMap<Local, PureExpr>,
    _local_to_name: &HashMap<Local, String>,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
) -> Option<PureExpr> {
    let (call_block, switch_bb) = resolve_for_loop_next_call(body, loop_info)?;
    let header_data = &body.basic_blocks[call_block];
    let TerminatorKind::Call { args, .. } = &header_data.terminator().kind else {
        return None;
    };

    let switch_data = &body.basic_blocks[switch_bb];
    let TerminatorKind::SwitchInt { .. } = &switch_data.terminator().kind else {
        return None;
    };

    let iterator_local =
        resolve_iterator_local_from_next_arg(args.first()?, &header_data.statements)?;
    let (range_start, range_end) = recover_range_bounds(
        body,
        loop_info,
        call_block,
        iterator_local,
        local_exprs,
        preds,
    )?;
    let produced_len = PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
            "produced".to_string(),
            Some(ExprSort::Seq),
        )))),
        method: "len".to_string(),
        args: vec![],
    };
    let range_trip_count = PureExpr::BinOp(Arc::new(range_end), BinOp::Sub, Arc::new(range_start));

    Some(PureExpr::BinOp(
        Arc::new(produced_len),
        BinOp::Lt,
        Arc::new(range_trip_count),
    ))
}

pub(super) fn recover_range_bounds(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    call_block: BasicBlock,
    iterator_local: Local,
    local_exprs: &HashMap<Local, PureExpr>,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
) -> Option<(PureExpr, PureExpr)> {
    recover_range_bounds_inner(
        body,
        loop_info,
        call_block,
        iterator_local,
        local_exprs,
        preds,
        None,
    )
}

pub(super) fn recover_range_bounds_with_spec_ctx(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    call_block: BasicBlock,
    iterator_local: Local,
    local_exprs: &HashMap<Local, PureExpr>,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
    call_spec_ctx: Option<CallSpecContext<'_, '_>>,
) -> Option<(PureExpr, PureExpr)> {
    recover_range_bounds_inner(
        body,
        loop_info,
        call_block,
        iterator_local,
        local_exprs,
        preds,
        call_spec_ctx,
    )
}

fn recover_range_bounds_inner(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    call_block: BasicBlock,
    iterator_local: Local,
    local_exprs: &HashMap<Local, PureExpr>,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
    call_spec_ctx: Option<CallSpecContext<'_, '_>>,
) -> Option<(PureExpr, PureExpr)> {
    let iterator_local =
        resolve_iterator_local_from_call_ref_chain(body, call_block, iterator_local)
            .unwrap_or(iterator_local);
    let from_iter_source =
        recover_iterator_source_from_preheader(body, loop_info, call_block, iterator_local, preds)
            .and_then(|(preheader, iter_source_local)| {
                recover_range_expr_from_into_iter_source(
                    body,
                    loop_info,
                    preheader,
                    iter_source_local,
                    local_exprs,
                    preds,
                    call_spec_ctx,
                )
            });
    let range_expr = from_iter_source.or_else(|| {
        recover_range_expr_from_iterator_initializer(
            body,
            loop_info,
            call_block,
            iterator_local,
            local_exprs,
            preds,
            call_spec_ctx,
        )
    })?;

    tuple_bounds(range_expr)
}

fn resolve_iterator_local_from_call_ref_chain(
    body: &Body<'_>,
    call_block: BasicBlock,
    iterator_arg_local: Local,
) -> Option<Local> {
    let mut current = iterator_arg_local;
    let mut visited = HashSet::new();

    loop {
        if !visited.insert(current) {
            return None;
        }

        let source_place = body.basic_blocks[call_block]
            .statements
            .iter()
            .rev()
            .find_map(|stmt| match &stmt.kind {
                StatementKind::Assign((place, Rvalue::Ref(_, _, source_place)))
                    if place.projection.is_empty() && place.local == current =>
                {
                    Some(source_place)
                }
                _ => None,
            })?;

        if source_place.projection.is_empty() {
            return Some(source_place.local);
        }

        if source_place.projection.len() == 1
            && matches!(source_place.projection[0], ProjectionElem::Deref)
        {
            current = source_place.local;
            continue;
        }

        return None;
    }
}

fn recover_iterator_source_from_preheader(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    call_block: BasicBlock,
    iterator_local: Local,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
) -> Option<(BasicBlock, Local)> {
    candidate_preheader_blocks(body, loop_info, call_block, preds)
        .into_iter()
        .find_map(|preheader| {
            find_iterator_source_local(body, preheader, iterator_local)
                .map(|iter_source_local| (preheader, iter_source_local))
        })
}

fn candidate_preheader_blocks(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    call_block: BasicBlock,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
) -> Vec<BasicBlock> {
    let mut anchors = vec![call_block];
    if let Some(mut entry_chain) = loop_entry_chain_to_call(body, loop_info.header, call_block) {
        entry_chain.reverse();
        for anchor in entry_chain {
            if !anchors.contains(&anchor) {
                anchors.push(anchor);
            }
        }
    }

    let mut preheaders = Vec::new();
    for anchor in anchors {
        let Some(anchor_preds) = preds.get(&anchor) else {
            continue;
        };
        for pred in anchor_preds {
            if !loop_info.body_blocks.contains(pred) && !preheaders.contains(pred) {
                preheaders.push(*pred);
            }
        }
    }

    preheaders
}

fn loop_entry_chain_to_call(
    body: &Body<'_>,
    header: BasicBlock,
    call_block: BasicBlock,
) -> Option<Vec<BasicBlock>> {
    let mut chain = vec![header];
    let mut current = header;
    let mut visited = HashSet::new();

    while current != call_block {
        if !visited.insert(current) {
            return None;
        }

        current = match &body.basic_blocks[current].terminator().kind {
            TerminatorKind::Goto { target, .. } => *target,
            TerminatorKind::FalseUnwind { real_target, .. } => *real_target,
            _ => return None,
        };
        chain.push(current);
    }

    Some(chain)
}

fn find_iterator_source_local(
    body: &Body<'_>,
    preheader: BasicBlock,
    iterator_local: Local,
) -> Option<Local> {
    let preheader_data = &body.basic_blocks[preheader];

    preheader_data
        .statements
        .iter()
        .find_map(|stmt| match &stmt.kind {
            StatementKind::Assign((place, Rvalue::Use(operand, _)))
                if place.projection.is_empty() && place.local == iterator_local =>
            {
                match operand {
                    Operand::Copy(src) | Operand::Move(src) if src.projection.is_empty() => {
                        Some(src.local)
                    }
                    _ => None,
                }
            }
            _ => None,
        })
}

fn recover_range_expr_from_into_iter_source(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    preheader: BasicBlock,
    iter_source_local: Local,
    local_exprs: &HashMap<Local, PureExpr>,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
    call_spec_ctx: Option<CallSpecContext<'_, '_>>,
) -> Option<PureExpr> {
    if let Some(expr) = local_exprs.get(&iter_source_local) {
        if tuple_bounds(expr.clone()).is_some() {
            return Some(expr.clone());
        }
    }

    preds
        .get(&preheader)?
        .iter()
        .copied()
        .filter(|bb| !loop_info.body_blocks.contains(bb))
        .find_map(|pre_preheader| {
            let pre_preheader_data = &body.basic_blocks[pre_preheader];
            match &pre_preheader_data.terminator().kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } if destination.projection.is_empty()
                    && destination.local == iter_source_local =>
                {
                    if is_range_inclusive_new_call(func, call_spec_ctx) && args.len() == 2 {
                        return tuple_expr_from_call_args(args, body, pre_preheader, local_exprs);
                    }
                    args.first().and_then(|arg| {
                        recover_range_expr_from_operand_or_initializer(
                            &arg.node,
                            body,
                            loop_info,
                            pre_preheader,
                            local_exprs,
                            preds,
                            call_spec_ctx,
                        )
                    })
                }
                _ => None,
            }
        })
}

fn recover_range_expr_from_iterator_initializer(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    call_block: BasicBlock,
    iterator_local: Local,
    local_exprs: &HashMap<Local, PureExpr>,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
    call_spec_ctx: Option<CallSpecContext<'_, '_>>,
) -> Option<PureExpr> {
    for preheader in candidate_preheader_blocks(body, loop_info, call_block, preds) {
        if let Some(expr) =
            recover_range_expr_from_block_assignment(body, preheader, iterator_local, local_exprs)
        {
            return Some(expr);
        }
        if let Some(expr) = recover_range_expr_from_call_destination(
            body,
            preheader,
            iterator_local,
            local_exprs,
            call_spec_ctx,
        ) {
            return Some(expr);
        }
        if let Some(expr) = preds.get(&preheader).and_then(|preheader_preds| {
            preheader_preds
                .iter()
                .copied()
                .filter(|bb| !loop_info.body_blocks.contains(bb))
                .find_map(|pred| {
                    recover_range_expr_from_call_destination(
                        body,
                        pred,
                        iterator_local,
                        local_exprs,
                        call_spec_ctx,
                    )
                })
        }) {
            return Some(expr);
        }
    }

    None
}

fn recover_range_expr_from_block_assignment(
    body: &Body<'_>,
    block: BasicBlock,
    target_local: Local,
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<PureExpr> {
    body.basic_blocks[block]
        .statements
        .iter()
        .rev()
        .find_map(|stmt| match &stmt.kind {
            StatementKind::Assign((place, rvalue))
                if place.projection.is_empty() && place.local == target_local =>
            {
                recover_range_expr_from_rvalue(rvalue, body, block, local_exprs)
            }
            _ => None,
        })
}

fn recover_range_expr_from_call_destination(
    body: &Body<'_>,
    block: BasicBlock,
    target_local: Local,
    local_exprs: &HashMap<Local, PureExpr>,
    call_spec_ctx: Option<CallSpecContext<'_, '_>>,
) -> Option<PureExpr> {
    match &body.basic_blocks[block].terminator().kind {
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } if destination.projection.is_empty() && destination.local == target_local => {
            if args.len() == 2
                && (is_range_inclusive_new_call(func, call_spec_ctx)
                    || destination_local_is_range_inclusive(body, target_local, call_spec_ctx))
            {
                tuple_expr_from_call_args(args, body, block, local_exprs)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn tuple_expr_from_call_args(
    args: &[rustc_span::Spanned<Operand<'_>>],
    body: &Body<'_>,
    block: BasicBlock,
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<PureExpr> {
    let start = translate_operand(&args[0].node, local_exprs).or_else(|| {
        recover_range_expr_from_block_operand(&args[0].node, body, block, local_exprs)
    })?;
    let end = translate_operand(&args[1].node, local_exprs).or_else(|| {
        recover_range_expr_from_block_operand(&args[1].node, body, block, local_exprs)
    })?;
    Some(PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(2),
        args: vec![start, end],
    })
}

fn recover_range_expr_from_operand_or_initializer(
    operand: &Operand<'_>,
    body: &Body<'_>,
    loop_info: &LoopInfo,
    block: BasicBlock,
    local_exprs: &HashMap<Local, PureExpr>,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
    call_spec_ctx: Option<CallSpecContext<'_, '_>>,
) -> Option<PureExpr> {
    if let Some(expr) = translate_operand(operand, local_exprs) {
        if tuple_bounds(expr.clone()).is_some() {
            return Some(expr);
        }
    }
    if let Some(expr) = recover_range_expr_from_block_operand(operand, body, block, local_exprs) {
        if tuple_bounds(expr.clone()).is_some() {
            return Some(expr);
        }
    }
    operand_local(operand).and_then(|source_local| {
        recover_range_expr_from_local_initializer(
            body,
            loop_info,
            block,
            source_local,
            local_exprs,
            preds,
            call_spec_ctx,
        )
    })
}

fn operand_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}

fn recover_range_expr_from_local_initializer(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    block: BasicBlock,
    source_local: Local,
    local_exprs: &HashMap<Local, PureExpr>,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
    call_spec_ctx: Option<CallSpecContext<'_, '_>>,
) -> Option<PureExpr> {
    preds
        .get(&block)?
        .iter()
        .copied()
        .filter(|bb| !loop_info.body_blocks.contains(bb))
        .find_map(|pred| {
            recover_range_expr_from_call_destination(
                body,
                pred,
                source_local,
                local_exprs,
                call_spec_ctx,
            )
            .or_else(|| {
                recover_range_expr_from_block_assignment(body, pred, source_local, local_exprs)
            })
        })
}

fn destination_local_is_range_inclusive(
    body: &Body<'_>,
    local: Local,
    call_spec_ctx: Option<CallSpecContext<'_, '_>>,
) -> bool {
    if let Some(ctx) = call_spec_ctx {
        if match body.local_decls[local].ty.kind() {
            rustc_middle::ty::TyKind::Adt(def, _) => {
                ctx.tcx.def_path_str(def.did()).contains("RangeInclusive")
            }
            _ => false,
        } {
            return true;
        }
    }
    format!("{:?}", body.local_decls[local].ty).contains("RangeInclusive")
}

fn is_range_inclusive_new_call(
    func: &Operand<'_>,
    call_spec_ctx: Option<CallSpecContext<'_, '_>>,
) -> bool {
    let Some(ctx) = call_spec_ctx else {
        return false;
    };
    let Some(def_id) = extract_call_def_id(func) else {
        return false;
    };
    let path = ctx.tcx.def_path_str(def_id);
    path.contains("RangeInclusive") && path.ends_with("::new")
}

fn tuple_bounds(range_expr: PureExpr) -> Option<(PureExpr, PureExpr)> {
    match range_expr {
        PureExpr::LogicFnCall { name, args } if tuple_logic_fn_arity(&name) == Some(2) => {
            let start = args.first()?.clone();
            let end = args.get(1)?.clone();
            Some((start, end))
        }
        _ => None,
    }
}

fn recover_range_expr_from_block_operand(
    operand: &Operand<'_>,
    body: &Body<'_>,
    block: BasicBlock,
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<PureExpr> {
    let source_local = match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => place.local,
        _ => return None,
    };

    body.basic_blocks[block]
        .statements
        .iter()
        .rev()
        .find_map(|stmt| match &stmt.kind {
            StatementKind::Assign((place, rvalue))
                if place.projection.is_empty() && place.local == source_local =>
            {
                recover_range_expr_from_rvalue(rvalue, body, block, local_exprs)
            }
            _ => None,
        })
}

fn recover_range_expr_from_rvalue<'tcx>(
    rvalue: &Rvalue<'tcx>,
    body: &Body<'tcx>,
    block: BasicBlock,
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<PureExpr> {
    match rvalue {
        Rvalue::Aggregate(rustc_middle::mir::AggregateKind::Adt(..), operands)
            if operands.len() == 2 =>
        {
            let mut translated = Vec::with_capacity(2);
            for operand in operands {
                translated.push(translate_operand(operand, local_exprs).or_else(|| {
                    recover_range_expr_from_block_operand(operand, body, block, local_exprs)
                })?);
            }
            Some(PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(2),
                args: translated,
            })
        }
        Rvalue::Use(operand, _) => translate_operand(operand, local_exprs)
            .or_else(|| recover_range_expr_from_block_operand(operand, body, block, local_exprs)),
        _ => translate_rvalue(rvalue, local_exprs, Some(body)),
    }
}
