// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pre-loop assignment extraction from MIR.
//!
//! Walks MIR blocks between function entry (bb0) and the loop header,
//! collecting variable assignments and unresolved call terminators.

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{
    BasicBlock, Body, Local, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use trust_wp_core::formula::{NamedBindingValue, PureExpr};

use super::{
    super::{
        call_resolve::extract_call_def_id,
        translate::{
            translate_operand, translate_rvalue, translate_rvalue_typed, ty_to_expr_sort,
            ty_to_expr_sort_enriched,
        },
    },
    detection::LoopInfo,
};

/// Unresolved pre-loop function call data. (#1295, #1581)
///
/// Extracted from MIR without `TyCtxt`, then resolved by
/// `resolve_pre_loop_calls` which has access to `TyCtxt`.
///
/// Calls to unnamed temporaries are also collected (with `dest_name: None`)
/// so that `resolve_pre_loop_calls` can chain through multi-call sequences
/// like `Seq::new().into_inner()`. (#1581)
#[derive(Debug, Clone)]
pub(crate) struct UnresolvedPreLoopCall {
    /// Destination variable name (e.g., `ghost_len`), or `None` for unnamed temporaries.
    pub(crate) dest_name: Option<String>,
    /// MIR local that receives the call result.
    pub(crate) dest_local: Local,
    /// MIR-derived sort of the destination local (#2053).
    pub(crate) dest_sort: Option<trust_wp_core::formula::ExprSort>,
    /// DefId of the called function.
    pub(crate) def_id: DefId,
    /// Translated receiver expression (first arg), if available.
    pub(crate) receiver_expr: Option<PureExpr>,
    /// MIR local for the call receiver, when it is a direct local.
    pub(crate) receiver_local: Option<Local>,
    /// Named non-parameter receiver local to advance from mutating pre-loop calls.
    pub(crate) receiver_name: Option<String>,
    /// MIR-derived sort of the receiver local.
    pub(crate) receiver_sort: Option<trust_wp_core::formula::ExprSort>,
    /// Translated call argument expressions, if available.
    ///
    /// Unlike `arg_locals`, this preserves constants and pre-loop temporary
    /// assignments such as the `100` in `vec![false; 100]`.
    pub(crate) arg_exprs: Vec<Option<PureExpr>>,
    /// MIR locals referenced by arguments (for multi-pass chaining). (#1581)
    pub(crate) arg_locals: Vec<Option<Local>>,
}

/// Extract pre-loop variable assignments by walking MIR blocks from bb0 to the loop header.
///
/// Walks basic blocks between function entry and the loop header, collecting
/// assignments to locally-declared variables. For `let mut i = 0;` before a
/// `while` loop, returns `{"i": Int(0)}`.
///
/// Also collects unresolved Call terminators into `unresolved_calls` so the
/// caller can resolve them with `TyCtxt` separately (needed because
/// `TyCtxt` can't be passed into `MIR_BODIES.with` closures). (#1295)
pub(super) fn extract_pre_loop_assignments<'tcx>(
    body: &Body<'tcx>,
    arg_names: &[String],
    loop_info: &LoopInfo,
    tcx: Option<rustc_middle::ty::TyCtxt<'tcx>>,
) -> (
    HashMap<String, NamedBindingValue>,
    Vec<UnresolvedPreLoopCall>,
    HashSet<String>,
    HashMap<Local, Local>,
) {
    let mut local_exprs: HashMap<Local, PureExpr> = HashMap::new();
    let mut local_to_name: HashMap<Local, String> = HashMap::new();
    let param_locals: HashSet<Local> = (0..arg_names.len())
        .map(|i| Local::from_usize(i + 1))
        .collect();

    // Use enriched sort when TyCtxt is available (#994 Phase 2)
    let sort_for_local = |local: Local| -> Option<trust_wp_core::formula::ExprSort> {
        match tcx {
            Some(tcx) => ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty),
            None => ty_to_expr_sort(body.local_decls[local].ty),
        }
    };

    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        let sort = sort_for_local(local);
        local_exprs.insert(local, PureExpr::Var(name.clone(), sort));
        local_to_name.insert(local, name.clone());
    }

    // Add local variable names from debug info (e.g., `let mut i = 0`).
    // Seed both local_to_name and local_exprs with symbolic Var(name) entries
    // so that assignments referencing other locals (e.g., `door = pass` in a
    // nested loop) can be translated. Without this, translate_rvalue returns
    // None for any rvalue referencing a local that isn't in local_exprs. (#1295)
    for var_debug in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &var_debug.value {
            if place.projection.is_empty() && !param_locals.contains(&place.local) {
                let name = var_debug.name.to_string();
                local_to_name.insert(place.local, name.clone());
                let sort = sort_for_local(place.local);
                local_exprs.insert(place.local, PureExpr::Var(name, sort));
            }
        }
    }

    let mut result: HashMap<String, NamedBindingValue> = HashMap::new();
    let mut unresolved_calls: Vec<UnresolvedPreLoopCall> = Vec::new();
    let mut call_result_aliases: HashMap<Local, String> = HashMap::new();
    // Track parameters reassigned before loop entry (#2095).
    let mut pre_loop_written_params: HashSet<String> = HashSet::new();
    // Track Ref assignments so the resolver can follow borrow chains. (#2665)
    // When MIR has `_ref = &_source`, we record `_ref → _source` so that
    // calls like `Snapshot::capture(&view_result)` can resolve through the
    // intermediate borrow even when the source is a call result.
    let mut ref_source_locals: HashMap<Local, Local> = HashMap::new();
    let mut copy_source_locals: HashMap<Local, Local> = HashMap::new();
    let mut visited: HashSet<BasicBlock> = HashSet::new();
    let mut worklist = vec![BasicBlock::from_u32(0)];

    while let Some(bb) = worklist.pop() {
        if loop_info.body_blocks.contains(&bb) || !visited.insert(bb) {
            continue;
        }

        let bb_data = &body.basic_blocks[bb];

        for stmt in &bb_data.statements {
            if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                if place.projection.is_empty() {
                    if let (Some(name), Some(src_local)) = (
                        local_to_name.get(&place.local),
                        assignment_source_local(rvalue),
                    ) {
                        if !param_locals.contains(&place.local) {
                            call_result_aliases.insert(src_local, name.clone());
                        }
                    }
                    let expr = tcx
                        .and_then(|tcx| {
                            translate_rvalue_typed(tcx, rvalue, &local_exprs, Some(body))
                        })
                        .or_else(|| translate_rvalue(rvalue, &local_exprs, Some(body)));
                    if let Some(expr) = expr {
                        // For NAMED borrow destinations (`let bor_k = &mut k`),
                        // do NOT overwrite the symbolic `Var("bor_k", MutRef(_))`
                        // entry from var_debug_info with the value of the borrow
                        // source. The borrow has its own identity — equating
                        // `bor_k` with `k`'s value at pre-loop entry loses the
                        // distinction between the reference and its referent,
                        // and downstream `Snapshot::capture(&bor_k)` resolution
                        // would propagate the wrong value. Unnamed temporaries
                        // (e.g., the `_tmp = &bor_k` produced by `snapshot!`)
                        // still flow through so call resolution can chase the
                        // ref chain. (#994 Phase 3 B3)
                        let is_named_borrow_dest = matches!(rvalue, Rvalue::Ref(..))
                            && local_to_name.contains_key(&place.local)
                            && !param_locals.contains(&place.local);
                        if !is_named_borrow_dest {
                            local_exprs.insert(place.local, expr.clone());
                            if let Some(name) = local_to_name.get(&place.local) {
                                if param_locals.contains(&place.local) {
                                    // Parameter reassigned before loop entry (#2095).
                                    pre_loop_written_params.insert(name.clone());
                                } else {
                                    let sort = sort_for_local(place.local);
                                    result.insert(name.clone(), NamedBindingValue::new(sort, expr));
                                }
                            }
                        }
                    }
                    // Track Ref assignments for borrow-chain resolution. (#2665)
                    // When `_ref = &_source` and `_source` is a call result (not
                    // yet in local_exprs), record the mapping so the multi-pass
                    // resolver can look through borrows.
                    if let Rvalue::Ref(_, _, ref_place) = rvalue {
                        if ref_place.projection.is_empty() {
                            ref_source_locals.insert(place.local, ref_place.local);
                        } else if matches!(ref_place.projection.as_ref(), [ProjectionElem::Deref]) {
                            copy_source_locals.insert(place.local, ref_place.local);
                            if let Some(ref_source) =
                                ref_source_locals.get(&ref_place.local).copied()
                            {
                                ref_source_locals.insert(place.local, ref_source);
                            }
                        }
                    } else if let Some(src_local) = assignment_source_local(rvalue) {
                        copy_source_locals.insert(place.local, src_local);
                        if let Some(ref_source) = ref_source_locals.get(&src_local).copied() {
                            ref_source_locals.insert(place.local, ref_source);
                        }
                    }
                }
            }
        }

        // Collect Call terminators assigning to locals (named or unnamed). (#1295, #1581)
        // For `let ghost_len = addr.len()`, MIR generates a Call terminator
        // that assigns to the local for `ghost_len`. We extract the DefId
        // and translated arg expressions as owned data so the caller can
        // resolve the method name via TyCtxt outside the MIR_BODIES closure.
        //
        // Also collect calls to unnamed temporaries so `resolve_pre_loop_calls`
        // can chain through multi-call sequences like `Seq::new().into_inner()`.
        // (#1581)
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &bb_data.terminator().kind
        {
            if destination.projection.is_empty() && !param_locals.contains(&destination.local) {
                if let Some(def_id) = extract_call_def_id(func) {
                    let name = local_to_name.get(&destination.local).cloned();
                    let receiver_local = args
                        .first()
                        .and_then(|arg| extract_operand_local(&arg.node));
                    let receiver_name = receiver_local.and_then(|local| {
                        (!param_locals.contains(&local))
                            .then(|| local_to_name.get(&local).cloned())
                            .flatten()
                    });
                    // Translate the first argument (receiver) if available.
                    let receiver_expr = args
                        .first()
                        .and_then(|a| translate_operand(&a.node, &local_exprs));
                    let arg_exprs = args
                        .iter()
                        .map(|a| translate_operand(&a.node, &local_exprs))
                        .collect();
                    // Record arg locals for multi-pass chaining (#1581).
                    let arg_locals = args
                        .iter()
                        .map(|a| extract_operand_local(&a.node))
                        .collect();
                    unresolved_calls.push(UnresolvedPreLoopCall {
                        dest_name: name,
                        dest_local: destination.local,
                        dest_sort: sort_for_local(destination.local),
                        def_id,
                        receiver_expr,
                        receiver_local,
                        receiver_name,
                        receiver_sort: receiver_local.and_then(sort_for_local),
                        arg_exprs,
                        arg_locals,
                    });
                }
            }
        }

        for succ in bb_data.terminator().successors() {
            worklist.push(succ);
        }
    }

    for call in &mut unresolved_calls {
        if call.dest_name.is_none() {
            call.dest_name = call_result_aliases.get(&call.dest_local).cloned();
        }
    }

    for _ in 0..copy_source_locals.len() {
        let mut changed = false;
        for (alias, source) in &copy_source_locals {
            if ref_source_locals.contains_key(alias) {
                continue;
            }
            if let Some(ref_source) = ref_source_locals.get(source).copied() {
                ref_source_locals.insert(*alias, ref_source);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    (
        result,
        unresolved_calls,
        pre_loop_written_params,
        ref_source_locals,
    )
}

fn assignment_source_local(rvalue: &Rvalue<'_>) -> Option<Local> {
    match rvalue {
        Rvalue::Use(operand, _) => extract_operand_local(operand),
        _ => None,
    }
}

/// Extract the MIR Local from an Operand (Copy or Move), if any. (#1581)
fn extract_operand_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}
