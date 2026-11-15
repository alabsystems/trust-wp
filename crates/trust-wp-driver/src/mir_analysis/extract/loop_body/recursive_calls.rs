// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recursive call-site extraction for loop/termination verification.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{GenericArgs, TyCtxt, TyKind},
};
use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_field_logic_fn_name, ExprSort, PureExpr, UnOp,
};

use super::switch_conditions::switch_branch_conditions;
use crate::mir_analysis::{
    call_resolve::extract_call_def_id,
    translate::{
        translate_operand, translate_operand_with_tcx, translate_rvalue, translate_rvalue_typed,
        translate_typed_field_place, ty_to_expr_sort, ty_to_expr_sort_enriched,
    },
};

/// A recursive call site with translated arguments.
///
/// Represents a point in a function's MIR where the function calls itself.
/// The `call_args` are symbolic expressions for the arguments passed at
/// that call site, enabling variant decrease verification.
#[derive(Debug, Clone)]
pub(crate) struct RecursiveCallSite {
    /// Symbolic expressions for the arguments at the recursive call site.
    /// Indexed by parameter position.
    pub call_args: Vec<PureExpr>,
    /// Path predicates that must hold to reach this call site.
    /// These are conjoined with function-level requires when checking
    /// recursive variant decrease obligations.
    pub path_conditions: Vec<PureExpr>,
}

/// Extract arguments at each recursive call site in a function's MIR.
///
/// Walks the MIR body following CFG edges (not sequential block order) to
/// correctly scope assignments per control-flow path. This prevents
/// assignments from unreachable or divergent branches from polluting the
/// expression map at a recursive call site (#807).
///
/// Used by termination checking (Phase 2) to verify that the variant
/// expression strictly decreases at each recursive call site.
///
/// # Arguments
/// * `body` - The MIR body to analyze
/// * `arg_names` - Function parameter names for symbolic representation
/// * `self_def_id` - The DefId of the function itself (for detecting self-calls)
///
/// # Returns
/// A list of `RecursiveCallSite`s, one for each recursive call found.
pub(crate) fn extract_recursive_call_args<'tcx>(
    body: &Body<'tcx>,
    arg_names: &[String],
    self_def_id: DefId,
    tcx: Option<rustc_middle::ty::TyCtxt<'tcx>>,
) -> Vec<RecursiveCallSite> {
    // Use enriched sort when TyCtxt is available (#994 Phase 2)
    let sort_for_local = |local: Local| -> Option<trust_wp_core::formula::ExprSort> {
        match tcx {
            Some(tcx) => ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty),
            None => ty_to_expr_sort(body.local_decls[local].ty),
        }
    };

    // Seed local_exprs with argument names, annotated with MIR types (#1965).
    let mut initial_exprs: HashMap<Local, PureExpr> = HashMap::new();
    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        let sort = sort_for_local(local);
        initial_exprs.insert(local, PureExpr::Var(name.clone(), sort));
    }

    // Also seed from debug info (same as loop extraction).
    for info in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &info.value {
            if place.projection.is_empty() {
                let local = place.local;
                let sort = sort_for_local(local);
                // Don't overwrite argument entries.
                initial_exprs
                    .entry(local)
                    .or_insert_with(|| PureExpr::Var(info.name.to_string(), sort));
            }
        }
    }

    let lent = lent_locals(body, tcx);

    // Walk CFG from entry block, following edges and scoping assignments per-path.
    let mut sites = Vec::new();
    let visited = HashSet::new();
    extract_recursive_calls_from_block(
        body,
        BasicBlock::from_u32(0),
        initial_exprs,
        visited,
        Vec::new(),
        self_def_id,
        &mut sites,
        tcx,
        &lent,
    );

    sites
}

/// The locals whose own memory the body borrows `&mut` or raw anywhere (not a
/// reborrow through a `Deref`), or borrows shared while their type may reach
/// interior mutability.
///
/// The walk binds a local at its projection-free assignments and binds a
/// non-recursive call's destination, nothing else. Through such a loan the
/// local also changes at a store through a reference (`let r = &mut m;
/// *r = 5`), inside a callee handed the loan (`set5(&mut m)`), and where drop
/// glue writes it, at a `Drop` or inside a callee (`{ let _g = G(&mut m); }`,
/// D-140); a recursive call handed it would be checked against the value from
/// before (recursive_variant_reads_local_before_drop_glue_write.rs,
/// recursive_variant_reads_local_before_borrow_write.rs). The walk forgets
/// these locals at each such point (`forget_at_terminator`), and a read of a
/// forgotten local is a fresh value. Without `tcx` (the walk's unit tests)
/// the interior-mutability clause is not asked.
fn lent_locals<'tcx>(body: &Body<'tcx>, tcx: Option<TyCtxt<'tcx>>) -> HashSet<Local> {
    use rustc_middle::mir::{BorrowKind, RawPtrKind};
    let mut lent = HashSet::new();
    for data in body.basic_blocks.iter() {
        for stmt in &data.statements {
            let StatementKind::Assign((_, rvalue)) = &stmt.kind else {
                continue;
            };
            let (place, may_write) = match rvalue {
                Rvalue::Ref(_, kind, place) => (place, matches!(kind, BorrowKind::Mut { .. })),
                Rvalue::RawPtr(kind, place) => (place, !matches!(kind, RawPtrKind::Const)),
                _ => continue,
            };
            if place.is_indirect() {
                continue;
            }
            let interior = !may_write
                && tcx.is_some_and(|tcx| {
                    super::local_type_may_reach_interior_mutability(tcx, body, place.local)
                });
            if may_write || interior {
                lent.insert(place.local);
            }
        }
    }
    lent
}

/// Forget what the terminator of `bb` may write behind the walk, after the
/// call's arguments were read: every lent local when a callee is handed an
/// argument it may write through (a `&mut`, a raw pointer, a value holding
/// one, interior mutability), else what `locals_changed_by_handoff` names, the
/// substitution walk's own answer at a `Drop` or a call whose drop glue may
/// write (D-140). Without `tcx` every lent local is forgotten.
fn forget_at_terminator<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    tcx: Option<TyCtxt<'tcx>>,
    lent: &HashSet<Local>,
    local_exprs: &mut HashMap<Local, PureExpr>,
) {
    let terminator = body.basic_blocks[bb].terminator();
    if !matches!(
        terminator.kind,
        TerminatorKind::Call { .. } | TerminatorKind::Drop { .. }
    ) {
        return;
    }
    let lends = |tcx: TyCtxt<'tcx>| {
        matches!(&terminator.kind, TerminatorKind::Call { func, args, .. }
        if crate::mir_analysis::extract::drop_glue_writes::call_may_write_through_args(
            tcx, body, func, args,
        ))
    };
    let changed = match tcx {
        Some(tcx) if !lends(tcx) => {
            crate::mir_analysis::extract::drop_glue_writes::locals_changed_by_handoff(
                tcx, body, bb, terminator,
            )
            .unwrap_or_default()
        }
        _ => lent.clone(),
    };
    for local in changed {
        local_exprs.remove(&local);
    }
}

/// Recursive CFG walker for extracting recursive call arguments.
///
/// Processes statements in `bb`, then follows the terminator's successor edges.
/// `local_exprs` is passed by value so each branch gets its own copy, preventing
/// assignments in one branch from being visible in another.
fn extract_recursive_calls_from_block<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    mut local_exprs: HashMap<Local, PureExpr>,
    mut visited: HashSet<BasicBlock>,
    path_conditions: Vec<PureExpr>,
    self_def_id: DefId,
    sites: &mut Vec<RecursiveCallSite>,
    tcx: Option<rustc_middle::ty::TyCtxt<'tcx>>,
    lent: &HashSet<Local>,
) {
    if !visited.insert(bb) {
        return;
    }

    let bb_data = &body.basic_blocks[bb];

    // Process statements in this block.
    for stmt in &bb_data.statements {
        if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
            // A write the walk cannot translate, or one into a projection of
            // the local (a field, or a store through a reference it holds),
            // leaves the local's old value stale: it is unbound, not kept. A
            // store through a reference may write any lent local.
            let expr = place
                .projection
                .is_empty()
                .then(|| translate_recursive_rvalue(rvalue, &local_exprs, body, tcx))
                .flatten();
            match expr {
                Some(expr) => {
                    local_exprs.insert(place.local, expr);
                }
                None => {
                    local_exprs.remove(&place.local);
                }
            }
            if place.is_indirect() {
                for local in lent {
                    local_exprs.remove(local);
                }
            }
        }
    }

    // Check terminator.
    let Some(ref terminator) = bb_data.terminator else {
        return;
    };

    match &terminator.kind {
        TerminatorKind::Call {
            func,
            args: call_args,
            destination,
            target,
            ..
        } => {
            // Check if this is a recursive call.
            let is_recursive = call_targets_self(func, self_def_id, tcx);
            if is_recursive {
                let translated: Vec<PureExpr> = call_args
                    .iter()
                    .enumerate()
                    .map(|(idx, arg)| {
                        translate_recursive_call_arg(&arg.node, &local_exprs, body, tcx)
                            .unwrap_or_else(|| {
                                crate::mir_analysis::fresh_fallback_arg_var(idx, None)
                            })
                    })
                    .collect();
                sites.push(RecursiveCallSite {
                    call_args: translated,
                    path_conditions: path_conditions.clone(),
                });
            } else if !destination.projection.is_empty() {
                local_exprs.remove(&destination.local);
            } else {
                // For non-recursive calls, record the destination local with
                // the same `call_{N}` naming convention used by the main VC
                // extraction pipeline. This ensures that call_assumptions
                // (postconditions of intermediate calls) can constrain the
                // actual argument passed to a downstream recursive call.
                let dest_local = destination.local;
                let sort = match tcx {
                    Some(tcx) => ty_to_expr_sort_enriched(tcx, body.local_decls[dest_local].ty),
                    None => ty_to_expr_sort(body.local_decls[dest_local].ty),
                };
                local_exprs.insert(
                    dest_local,
                    PureExpr::Var(format!("$call_{}", dest_local.as_u32()), sort),
                );
            }
            forget_at_terminator(body, bb, tcx, lent, &mut local_exprs);
            // Continue to the call's return target (if any).
            if let Some(target_bb) = target {
                extract_recursive_calls_from_block(
                    body,
                    *target_bb,
                    local_exprs,
                    visited,
                    path_conditions,
                    self_def_id,
                    sites,
                    tcx,
                    lent,
                );
            }
        }
        // For branches, clone local_exprs for each successor so per-branch
        // assignments don't cross-contaminate.
        TerminatorKind::SwitchInt { discr, targets } => {
            let branch_conditions =
                switch_branch_conditions(discr, targets, &local_exprs, body, None)
                    .unwrap_or_default();

            for target_bb in targets.all_targets() {
                let mut branch_path_conditions = path_conditions.clone();
                if let Some(cond) = branch_conditions.get(target_bb) {
                    branch_path_conditions.push(cond.clone());
                }
                extract_recursive_calls_from_block(
                    body,
                    *target_bb,
                    local_exprs.clone(),
                    visited.clone(),
                    branch_path_conditions,
                    self_def_id,
                    sites,
                    tcx,
                    lent,
                );
            }
        }
        // Linear successors: pass local_exprs along.
        TerminatorKind::Goto { target, .. } | TerminatorKind::Drop { target, .. } => {
            forget_at_terminator(body, bb, tcx, lent, &mut local_exprs);
            extract_recursive_calls_from_block(
                body,
                *target,
                local_exprs,
                visited,
                path_conditions,
                self_def_id,
                sites,
                tcx,
                lent,
            );
        }
        TerminatorKind::Assert {
            cond,
            expected,
            target,
            ..
        } => {
            let mut asserted_path_conditions = path_conditions;
            if let Some(cond_expr) = translate_operand(cond, &local_exprs) {
                let asserted_cond = if *expected {
                    cond_expr
                } else {
                    PureExpr::UnOp(UnOp::Not, Arc::new(cond_expr))
                };
                asserted_path_conditions.push(asserted_cond);
            }
            extract_recursive_calls_from_block(
                body,
                *target,
                local_exprs,
                visited,
                asserted_path_conditions,
                self_def_id,
                sites,
                tcx,
                lent,
            );
        }
        // FalseEdge/FalseUnwind: follow the real target.
        TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } => {
            extract_recursive_calls_from_block(
                body,
                *real_target,
                local_exprs,
                visited,
                path_conditions,
                self_def_id,
                sites,
                tcx,
                lent,
            );
        }
        // Terminal: no successors, no recursive calls possible.
        TerminatorKind::Return
        | TerminatorKind::Unreachable
        | TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::CoroutineDrop
        | TerminatorKind::InlineAsm { .. }
        | TerminatorKind::Yield { .. }
        | TerminatorKind::TailCall { .. } => {}
    }
}

fn translate_recursive_call_arg<'tcx>(
    operand: &Operand<'tcx>,
    local_exprs: &HashMap<Local, PureExpr>,
    body: &Body<'tcx>,
    tcx: Option<TyCtxt<'tcx>>,
) -> Option<PureExpr> {
    let Some(tcx) = tcx else {
        return translate_operand(operand, local_exprs);
    };
    translate_operand_with_tcx(operand, local_exprs, tcx).or_else(|| match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            translate_typed_field_place(tcx, body, place, local_exprs)
                .or_else(|| translate_structural_place(tcx, body, place, local_exprs))
        }
        // RuntimeChecks, like Constant, references no place/local.
        Operand::Constant(_) | Operand::RuntimeChecks(_) => None,
    })
}

fn translate_recursive_rvalue<'tcx>(
    rvalue: &Rvalue<'tcx>,
    local_exprs: &HashMap<Local, PureExpr>,
    body: &Body<'tcx>,
    tcx: Option<TyCtxt<'tcx>>,
) -> Option<PureExpr> {
    let Some(tcx) = tcx else {
        return translate_rvalue(rvalue, local_exprs, Some(body));
    };
    translate_rvalue_typed(tcx, rvalue, local_exprs, Some(body)).or_else(|| match rvalue {
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)
        | Rvalue::Ref(_, _, place)
        | Rvalue::CopyForDeref(place) => translate_structural_place(tcx, body, place, local_exprs),
        // A float cast rounds, saturates or maps NaN: it is never its
        // operand, and the typed translator above already gave it its IEEE
        // meaning or refused it.
        Rvalue::Cast(
            rustc_middle::mir::CastKind::FloatToInt
            | rustc_middle::mir::CastKind::IntToFloat
            | rustc_middle::mir::CastKind::FloatToFloat,
            _,
            _,
        ) => None,
        Rvalue::Cast(_, operand, _) => {
            translate_recursive_call_arg(operand, local_exprs, body, Some(tcx))
        }
        _ => None,
    })
}

fn translate_structural_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: &Place<'tcx>,
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<PureExpr> {
    let mut current = local_exprs.get(&place.local)?.clone();
    let mut current_ty = body.local_decls[place.local].ty;

    for projection in place.projection {
        match projection {
            ProjectionElem::Deref => {
                if expr_sort_is_ref_like(&current) {
                    current = PureExpr::Deref(Arc::new(current));
                }
                current_ty = current_ty.builtin_deref(true).map_or(current_ty, |ty| ty);
            }
            ProjectionElem::Downcast(_, _) | ProjectionElem::OpaqueCast(_) => {}
            ProjectionElem::Field(field, field_ty) => {
                if field.as_u32() == 0 && ty_is_transparent_box_carrier(tcx, current_ty) {
                    current_ty = field_ty;
                    continue;
                }
                let field_idx = usize::try_from(field.as_u32()).ok()?;
                current = PureExpr::LogicFnCall {
                    name: tuple_field_logic_fn_name(field_idx),
                    args: vec![current],
                };
                current_ty = field_ty;
            }
            _ => return None,
        }
    }

    Some(current)
}

fn expr_sort_is_ref_like(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::Var(_, Some(ExprSort::Ref(_) | ExprSort::MutRef(_)))
    )
}

fn ty_is_transparent_box_carrier(tcx: TyCtxt<'_>, ty: rustc_middle::ty::Ty<'_>) -> bool {
    let TyKind::Adt(adt_def, _) = ty.kind() else {
        return false;
    };
    let path = tcx.def_path_str(adt_def.did());
    // `Box<T>`'s field 0 is its `BoxRaw<T>`, whose field 0 is the `NonNull<T>`.
    matches!(path.as_str(), "alloc::boxed::Box" | "std::boxed::Box")
        || path.ends_with("boxed::BoxRaw")
        || path.ends_with("ptr::unique::Unique")
        || path.ends_with("ptr::non_null::NonNull")
        || path.ends_with("ptr::Unique")
        || path.ends_with("ptr::NonNull")
}

fn call_targets_self<'tcx>(
    func: &Operand<'tcx>,
    self_def_id: DefId,
    tcx: Option<TyCtxt<'tcx>>,
) -> bool {
    if extract_call_def_id(func).is_some_and(|callee_id| callee_id == self_def_id) {
        return true;
    }

    let (Some(tcx), Some((callee, args))) = (tcx, extract_fn_def_with_args(func)) else {
        return false;
    };
    resolve_trait_impl_method(tcx, callee, args).is_some_and(|resolved| resolved == self_def_id)
}

fn extract_fn_def_with_args<'tcx>(func: &Operand<'tcx>) -> Option<(DefId, GenericArgs<'tcx>)> {
    let Operand::Constant(deref!(constant)) = func else {
        return None;
    };
    let TyKind::FnDef(def_id, args) = constant.const_.ty().kind() else {
        return None;
    };
    Some((*def_id, args.skip_binder()))
}

fn resolve_trait_impl_method<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: DefId,
    args: GenericArgs<'tcx>,
) -> Option<DefId> {
    let assoc = tcx.opt_associated_item(callee_def_id)?;
    if !matches!(assoc.container, rustc_middle::ty::AssocContainer::Trait) {
        return None;
    }

    let trait_def_id = tcx.parent(callee_def_id);
    let method_name = tcx.item_name(callee_def_id);
    let self_ty = args.types().next()?;
    if matches!(self_ty.kind(), TyKind::Param(..) | TyKind::Alias(..)) {
        return None;
    }

    for local in tcx.iter_local_def_id() {
        let impl_def_id = local.to_def_id();
        if !matches!(
            tcx.def_kind(impl_def_id),
            rustc_hir::def::DefKind::Impl { of_trait: true }
        ) {
            continue;
        }
        let impl_trait_ref = tcx.impl_trait_ref(impl_def_id).skip_binder();
        if impl_trait_ref.def_id != trait_def_id || impl_trait_ref.self_ty() != self_ty {
            continue;
        }
        for item in tcx.associated_items(impl_def_id).in_definition_order() {
            // An async trait method's synthesized return type is an
            // associated item with no name.
            if item.opt_name() == Some(method_name)
                && matches!(tcx.def_kind(item.def_id), rustc_hir::def::DefKind::AssocFn)
            {
                return Some(item.def_id);
            }
        }
    }
    None
}
