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
    write_sites::WriteSites,
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
    /// Per argument, whether it reads a pointee after a store its
    /// translation does not see (`extract::stale_arguments`).
    pub(crate) arg_stale: Vec<bool>,
    /// Whether builtin-table contracts may describe this call (computed from
    /// the call's generic arguments at collection time).
    pub(crate) builtin_admission: crate::provenance::BuiltinSpecAdmission,
}

/// Extract pre-loop variable assignments by walking MIR blocks from bb0 to the loop header.
///
/// Walks basic blocks between function entry and the loop header, collecting
/// assignments to locally-declared variables. For `let mut i = 0;` before a
/// `while` loop, returns `{"i": Int(0)}`.
///
/// Also collects unresolved Call terminators into `unresolved_calls` so the
/// caller can resolve their typed identities and compose their effects after
/// the structural MIR walk. (#1295)
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
            if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
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
        // resolve the method name with the same compiler context.
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
                        arg_stale: crate::mir_analysis::extract::stale_arguments(tcx, body, args),
                        builtin_admission: tcx
                            .map(|tcx| {
                                crate::provenance::builtin_spec_admission_for_operand(
                                    tcx,
                                    func,
                                    Some(body.source.def_id()),
                                )
                            })
                            .unwrap_or(crate::provenance::BuiltinSpecAdmission::Refused),
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

/// Drop pre-loop bindings that a loop which may run BEFORE this loop's header
/// can overwrite (enclosing loops and preceding sequential loops alike).
///
/// `extract_pre_loop_assignments` walks from bb0 skipping only THIS loop's
/// body, and keeps the last translatable assignment per name. A variable a
/// prior loop advances (`i += 1` lowers to an untranslatable `i = move
/// (_t.0)`) would keep its bb0 binding `i = 0` (or a once-through `i = 0 + 1`),
/// and Rule 1 of `infer_stable_loop_invariants` would promote it to an
/// effective invariant of this loop — a FALSE premise. An ENCLOSING loop
/// (`while j < n { while i < n { need0(j) } j += 1 }` would verify `j == 0`)
/// and a PRECEDING loop (`#[invariant(i <= n)] while i < n { i += 1 } let _y
/// = 10 - i; loop {}` would bind `i == 0 + 1` and `_y == 10 - (0 + 1)` at the
/// second loop) both exhibit it. A binding computed FROM such a variable is
/// resolved through the same stale value.
///
/// Prior loops: every other loop whose header is reachable from bb0 without
/// entering this loop's body and from whose header this loop's header is
/// reachable (enclosing and preceding loops alike).
///
/// A local is unstable when it has a write site (outside this loop's body)
/// inside a prior loop and either two or more write sites, a write site that
/// does not dominate this loop's header, or an implicit entry definition (a
/// parameter); and, transitively, when any write site outside this loop's
/// body reads an unstable local. Bindings of unstable locals, and bindings
/// whose value mentions an unstable local's name, are dropped. Dropping a
/// binding only removes a premise.
pub(super) fn drop_bindings_rewritten_by_enclosing_loops(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    all_loops: Option<&[LoopInfo]>,
    local_to_name: &HashMap<Local, String>,
    bindings: &mut HashMap<String, NamedBindingValue>,
) {
    use rustc_middle::mir::{
        visit::{PlaceContext, Visitor},
        BasicBlock as Bb, Location as Loc,
    };
    struct ReadLocals(Vec<Local>);
    impl<'tcx> Visitor<'tcx> for ReadLocals {
        fn visit_local(&mut self, local: Local, _context: PlaceContext, _location: Loc) {
            self.0.push(local);
        }
    }

    let Some(loops) = all_loops else {
        return;
    };
    let prior = prior_loop_blocks(body, loop_info, loops);
    if prior.is_empty() {
        return;
    }
    // Write sites outside this loop's body, with the locals each one reads and
    // whether the written value is one this analysis can see (`direct`: the
    // destination of an `Assign` or a `Call`; an indirect write — a `&mut`
    // borrow handed to a call, a store through a pointer — leaves the value
    // unknown).
    let write_sites = WriteSites::new(body);
    let mut sites: HashMap<Local, Vec<(Bb, Vec<Local>, bool)>> = HashMap::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if loop_info.body_blocks.contains(&bb) {
            continue;
        }
        for statement_index in 0..=data.statements.len() {
            let location = Loc {
                block: bb,
                statement_index,
            };
            let writes = write_sites.writes_at(location);
            if writes.is_empty() {
                continue;
            }
            // Every local the site mentions: an over-approximation of what it
            // reads (a destination reads itself here, which only ever
            // propagates instability a local already has).
            let mut reads = ReadLocals(Vec::new());
            if statement_index < data.statements.len() {
                reads.visit_statement(&data.statements[statement_index], location);
            } else {
                reads.visit_terminator(data.terminator(), location);
            }
            for (local, write) in writes {
                sites
                    .entry(local)
                    .or_default()
                    .push((bb, reads.0.clone(), write.direct));
            }
        }
    }
    let dominators = body.basic_blocks.dominators();
    let mut unstable: HashSet<Local> = sites
        .iter()
        .filter(|(local, local_sites)| {
            let is_parameter = local.as_usize() >= 1 && local.as_usize() <= body.arg_count;
            local_sites.iter().any(|(bb, _, _)| prior.contains(bb))
                && (local_sites.len() >= 2
                    || is_parameter
                    || local_sites
                        .iter()
                        .any(|(bb, _, _)| !dominators.dominates(*bb, loop_info.header))
                    // An indirect write inside a prior loop leaves the value
                    // unknown even when it is the only site and dominates.
                    || local_sites
                        .iter()
                        .any(|(bb, _, direct)| prior.contains(bb) && !direct))
        })
        .map(|(local, _)| *local)
        .collect();
    loop {
        let newly: Vec<Local> = sites
            .iter()
            .filter(|(local, local_sites)| {
                !unstable.contains(*local)
                    && local_sites
                        .iter()
                        .any(|(_, reads, _)| reads.iter().any(|read| unstable.contains(read)))
            })
            .map(|(local, _)| *local)
            .collect();
        if newly.is_empty() {
            break;
        }
        unstable.extend(newly);
    }
    let unstable_names: HashSet<&String> = unstable
        .iter()
        .filter_map(|local| local_to_name.get(local))
        .collect();
    bindings.retain(|name, binding| {
        !unstable_names.contains(name) && !binding_mentions_any(&binding.value, &unstable_names)
    });
}

/// Drop the pre-loop bindings whose value at this loop's header depends on the
/// path the execution took to it (D-243).
///
/// `extract_pre_loop_assignments` walks depth-first and keeps, per name, the
/// last translatable assignment it met. At a join the arm it walked last
/// stood for every arm (`let m = if c { 1 } else { 2 }` stated `m == 2` at the
/// loop's entry on both paths), and an assignment on a path that never
/// reaches the loop (an arm that returns) stood for the path that does. A
/// local is set on one path when a block the walk reads (one the entry
/// reaches without entering this loop's body) that does not dominate this
/// loop's header writes it, either as an `Assign` or `Call` destination the
/// walk may have recorded, or in any way on a path that goes on to the header
/// (a borrow, a store through a pointer, a drop); and, transitively, when such
/// a write site, or one that dominates the header, computes it from a local
/// set on one path. A write on a path that never reaches the header and that
/// the walk does not record (the drop on an unwind path) changes nothing the
/// loop is entered with. Its binding, and every binding whose value names it,
/// is dropped. Dropping a binding only removes a premise. Returns the locals
/// set on one path.
pub(super) fn drop_bindings_set_on_one_path(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    local_to_name: &HashMap<Local, String>,
    bindings: &mut HashMap<String, NamedBindingValue>,
) -> HashSet<Local> {
    use rustc_middle::mir::{
        visit::{PlaceContext, Visitor},
        Location as Loc,
    };
    struct ReadLocals(Vec<Local>);
    impl<'tcx> Visitor<'tcx> for ReadLocals {
        fn visit_local(&mut self, local: Local, _context: PlaceContext, _location: Loc) {
            self.0.push(local);
        }
    }

    let mut region: HashSet<BasicBlock> = HashSet::new();
    let mut worklist = vec![rustc_middle::mir::START_BLOCK];
    while let Some(bb) = worklist.pop() {
        if loop_info.body_blocks.contains(&bb) || !region.insert(bb) {
            continue;
        }
        worklist.extend(body.basic_blocks[bb].terminator().successors());
    }
    // The region's blocks from which the header can be reached without
    // entering this loop's body.
    let predecessors = body.basic_blocks.predecessors();
    let mut leads_to_header: HashSet<BasicBlock> = HashSet::new();
    let mut worklist: Vec<BasicBlock> = predecessors[loop_info.header]
        .iter()
        .copied()
        .filter(|pred| !loop_info.body_blocks.contains(pred))
        .collect();
    while let Some(bb) = worklist.pop() {
        if loop_info.body_blocks.contains(&bb) || !leads_to_header.insert(bb) {
            continue;
        }
        worklist.extend(predecessors[bb].iter().copied());
    }
    let dominators = body.basic_blocks.dominators();
    let write_sites = WriteSites::new(body);
    let mut unstable: HashSet<Local> = HashSet::new();
    // Each counted write site's destination with the locals the site mentions
    // (an over-approximation of what it reads).
    let mut computed_from: Vec<(Local, Vec<Local>)> = Vec::new();
    for &bb in &region {
        let data = &body.basic_blocks[bb];
        let on_every_path = dominators.dominates(bb, loop_info.header);
        let goes_on_to_header = leads_to_header.contains(&bb);
        for statement_index in 0..=data.statements.len() {
            let location = Loc {
                block: bb,
                statement_index,
            };
            let writes = write_sites.writes_at(location);
            if writes.is_empty() {
                continue;
            }
            let mut reads = ReadLocals(Vec::new());
            if statement_index < data.statements.len() {
                reads.visit_statement(&data.statements[statement_index], location);
            } else {
                reads.visit_terminator(data.terminator(), location);
            }
            for (local, write) in writes {
                if !write.direct && !goes_on_to_header {
                    continue;
                }
                if !on_every_path {
                    unstable.insert(local);
                }
                computed_from.push((local, reads.0.clone()));
            }
        }
    }
    if unstable.is_empty() {
        return unstable;
    }
    loop {
        let newly: Vec<Local> = computed_from
            .iter()
            .filter(|(local, reads)| {
                !unstable.contains(local) && reads.iter().any(|read| unstable.contains(read))
            })
            .map(|(local, _)| *local)
            .collect();
        if newly.is_empty() {
            break;
        }
        unstable.extend(newly);
    }
    let unstable_names: HashSet<&String> = unstable
        .iter()
        .filter_map(|local| local_to_name.get(local))
        .collect();
    bindings.retain(|name, binding| {
        !unstable_names.contains(name) && !binding_mentions_any(&binding.value, &unstable_names)
    });
    unstable
}

/// Body blocks of every loop that may run before `loop_info`'s header on some
/// path from function entry (enclosing and preceding loops).
pub(crate) fn prior_loop_blocks(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    loops: &[LoopInfo],
) -> HashSet<BasicBlock> {
    // Blocks reachable from `from` without expanding this loop's body.
    let reach = |from: BasicBlock| -> HashSet<BasicBlock> {
        let mut seen = HashSet::new();
        let mut worklist = vec![from];
        while let Some(bb) = worklist.pop() {
            if !seen.insert(bb) || loop_info.body_blocks.contains(&bb) {
                continue;
            }
            worklist.extend(body.basic_blocks[bb].terminator().successors());
        }
        seen
    };
    let from_entry = reach(BasicBlock::from_u32(0));
    loops
        .iter()
        .filter(|other| {
            other.header != loop_info.header
                && !loop_info.body_blocks.contains(&other.header)
                && from_entry.contains(&other.header)
                && reach(other.header).contains(&loop_info.header)
        })
        .flat_map(|other| other.body_blocks.iter().copied())
        .filter(|bb| !loop_info.body_blocks.contains(bb))
        .collect()
}

fn binding_mentions_any(expr: &PureExpr, names: &HashSet<&String>) -> bool {
    !names.is_empty() && expr.free_vars().iter().any(|name| names.contains(name))
}

/// Whether every path from the function's entry to a `Return` passes through
/// `loop_info`'s header.
///
/// Only then does a fact that holds at the loop's exit, or a value a walk from
/// its exit states, describe every run the function returns from. A return
/// before the loop, or a loop in one arm of a branch, returns on a path the
/// loop never saw (loop_lane_result_early_return_before_loop.rs,
/// loop_lane_result_loop_in_one_branch.rs).
pub(crate) fn every_return_passes_through(body: &Body<'_>, loop_info: &LoopInfo) -> bool {
    let mut seen: HashSet<BasicBlock> = HashSet::new();
    let mut worklist = vec![rustc_middle::mir::START_BLOCK];
    while let Some(bb) = worklist.pop() {
        if bb == loop_info.header || !seen.insert(bb) {
            continue;
        }
        let terminator = body.basic_blocks[bb].terminator();
        if matches!(terminator.kind, TerminatorKind::Return) {
            return false;
        }
        worklist.extend(terminator.successors());
    }
    true
}

/// Names that may be rewritten after `loop_info` exits and before ANOTHER loop
/// runs, or `None` when no other loop is reachable from its exit.
///
/// The multi-loop fold hands each loop's exit facts (continuation assumptions,
/// frame constraints) to the function-level post-loop VC. Only the LAST loop's
/// post-loop walk rebinds later writes; a fact of an earlier loop about a
/// variable written between the loops (`#[invariant(k == 0)] while .. {} k = n;
/// while .. {} k` proved `result == 0`) is stale. A local counts as rewritten
/// when a block reachable from the exit (outside this loop's body) writes it,
/// borrows it mutably, or stores through a pointer (then every local the body
/// ever writes or borrows mutably counts).
pub(crate) fn names_rewritten_after_exit_before_later_loop(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    loops: &[LoopInfo],
    arg_names: &[String],
) -> Option<HashSet<String>> {
    use rustc_middle::mir::{
        visit::{PlaceContext, Visitor},
        Location, Place,
    };
    struct Writes {
        locals: HashSet<Local>,
        stores_through_pointer: bool,
    }
    impl<'tcx> Visitor<'tcx> for Writes {
        fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
            if let PlaceContext::MutatingUse(_) = context {
                self.locals.insert(place.local);
                if place
                    .projection
                    .iter()
                    .any(|elem| matches!(elem, ProjectionElem::Deref))
                {
                    self.stores_through_pointer = true;
                }
            }
            self.super_place(place, context, location);
        }
    }

    let mut reached: HashSet<BasicBlock> = HashSet::new();
    let mut worklist: Vec<BasicBlock> = loop_info
        .body_blocks
        .iter()
        .flat_map(|bb| body.basic_blocks[*bb].terminator().successors())
        .collect();
    while let Some(bb) = worklist.pop() {
        if loop_info.body_blocks.contains(&bb) || !reached.insert(bb) {
            continue;
        }
        worklist.extend(body.basic_blocks[bb].terminator().successors());
    }
    if !loops
        .iter()
        .any(|other| other.header != loop_info.header && reached.contains(&other.header))
    {
        return None;
    }
    let mut writes = Writes {
        locals: HashSet::new(),
        stores_through_pointer: false,
    };
    for bb in &reached {
        writes.visit_basic_block_data(*bb, &body.basic_blocks[*bb]);
    }
    if writes.stores_through_pointer {
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            writes.visit_basic_block_data(bb, data);
        }
    }
    let mut names = HashSet::new();
    for local in &writes.locals {
        let index = local.as_usize();
        if index >= 1 && index <= arg_names.len() {
            names.insert(arg_names[index - 1].clone());
        }
    }
    for var_debug in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &var_debug.value {
            if writes.locals.contains(&place.local) {
                names.insert(var_debug.name.to_string());
            }
        }
    }
    Some(names)
}
