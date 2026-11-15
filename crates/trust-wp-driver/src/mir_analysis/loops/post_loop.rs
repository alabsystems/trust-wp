// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Post-loop analysis: exit block finding, return extraction, and
//! mutable-borrow dereference write tracking.

use std::{
    collections::{HashMap, HashSet},
    ops::ControlFlow,
    sync::Arc,
};

use rustc_middle::{
    mir::{
        visit::{PlaceContext, Visitor},
        AggregateKind, BasicBlock, BasicBlockData, Body, BorrowKind, Local, Location, Operand,
        Place, ProjectionElem, RawPtrKind, Rvalue, StatementKind, SwitchTargets, TerminatorKind,
    },
    ty::TyCtxt,
};
use tracing::debug;
use trust_wp_core::formula::{BinOp, PureExpr};

use super::{
    super::{
        extract::translate_rvalue_with_enum_variants,
        mut_borrow::is_freeze,
        translate::{
            operand_int_ty, operand_is_bool, switch_value_to_i64, translate_operand,
            translate_rvalue,
        },
    },
    detection::LoopInfo,
};

/// Extract the return expression from post-loop MIR blocks.
///
/// After a loop exits, MIR typically has a short chain of blocks that copy the
/// computed value into `_0` (the return place) and then execute `Return`.
/// For `count_to_n`, the MIR looks like:
/// ```text
///   bb_exit: _0 = copy _2;  // _2 is local `i`
///            return;
/// ```
///
/// The function-level check binds `result` to what this returns for every
/// execution that leaves the loop, so it is the value of every such execution:
/// each path from the loop exit block (the SwitchInt target that is NOT in the
/// loop body) to `Return` is walked on its own, resolving temporaries, and a
/// branch on a value becomes an `ite` over its arms. A path that re-enters a
/// loop, calls something whose result the walk cannot name, or writes a local
/// in a way the walk cannot follow makes the whole value unknown (`None`); a
/// local the walk cannot follow is forgotten, never kept at a value it held
/// before the write. A local lent mutably anywhere in the body can be written
/// through that loan by any later write through a pointer, call or drop, so each
/// of those forgets every such local (see [`mutably_lent_locals`]).
///
/// A D-140 hand-off on the way (a `Drop` whose glue may write, or a call that
/// may run such glue) also re-binds every local it may change to a fresh
/// symbol. Without a `TyCtxt` a writing drop cannot be told from a harmless
/// one, so a path that meets a `Drop` is unknown.
pub(super) fn extract_post_loop_return<'tcx>(
    tcx: Option<TyCtxt<'tcx>>,
    body: &Body<'tcx>,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<PureExpr> {
    let Some(exit_block) = find_post_loop_exit_block(body, cond_block, loop_info) else {
        debug!("extract_post_loop_return: exit block not found");
        return None;
    };
    debug!(
        "extract_post_loop_return: exit block found: bb{}",
        exit_block.as_usize()
    );

    let mut post_exprs = local_exprs.clone();
    // `_0` holds what the post-loop code writes into it; an entry from before
    // the loop is not the value the function returns.
    post_exprs.remove(&RETURN_PLACE);
    let mut walk = PostLoopWalk {
        tcx,
        body,
        cond_block,
        header: loop_info.header,
        budget: POST_LOOP_WALK_BLOCK_BUDGET,
        lent: mutably_lent_locals(tcx, body),
    };
    match walk.path_value(exit_block, post_exprs, HashSet::new()) {
        PathValue::Value(value) => Some(value),
        PathValue::Diverges | PathValue::Unknown => None,
    }
}

const RETURN_PLACE: Local = Local::from_u32(0);

/// Blocks the walk may visit over all paths; past it the value is unknown.
const POST_LOOP_WALK_BLOCK_BUDGET: usize = 256;

/// What `_0` holds when one post-loop path reaches `Return`.
enum PathValue {
    Value(PureExpr),
    /// The path never returns (it panics or is unreachable), so it constrains
    /// no returned value.
    Diverges,
    Unknown,
}

struct PostLoopWalk<'a, 'tcx> {
    tcx: Option<TyCtxt<'tcx>>,
    body: &'a Body<'tcx>,
    cond_block: BasicBlock,
    header: BasicBlock,
    budget: usize,
    /// Every local some loan in the body may point at.
    lent: HashSet<Local>,
}

impl<'tcx> PostLoopWalk<'_, 'tcx> {
    fn path_value(
        &mut self,
        mut bb: BasicBlock,
        mut post_exprs: HashMap<Local, PureExpr>,
        mut visited: HashSet<BasicBlock>,
    ) -> PathValue {
        loop {
            if self.budget == 0 {
                return PathValue::Unknown;
            }
            self.budget -= 1;
            if !visited.insert(bb) || bb == self.cond_block || bb == self.header {
                debug!(
                    "extract_post_loop_return: bb{} re-enters a loop; no single return value",
                    bb.as_usize()
                );
                return PathValue::Unknown;
            }
            debug!("extract_post_loop_return: processing bb{}", bb.as_usize());

            let bb_data = &self.body.basic_blocks[bb];
            for stmt in &bb_data.statements {
                // A local lent out mutably can be written through the loan
                // (`let r = &mut t; r.0 = x;`, or a call taking `&mut t`), a
                // write the walk never sees, so its value is forgotten here.
                if let StatementKind::Assign((_, rvalue)) = &stmt.kind {
                    if let Some(lent) = mutably_lent_place(rvalue) {
                        post_exprs.remove(&lent.local);
                    }
                }
                if statement_may_write_through_a_pointer(&stmt.kind) {
                    self.forget_lent(&mut post_exprs);
                }
                match &stmt.kind {
                    StatementKind::Assign((place, rvalue)) if place.projection.is_empty() => {
                        match translate_post_loop_rvalue(self.tcx, rvalue, &post_exprs, self.body) {
                            Some(expr) => {
                                post_exprs.insert(place.local, expr);
                            }
                            None => {
                                post_exprs.remove(&place.local);
                            }
                        }
                    }
                    // A write into part of a local (a field, an element, a
                    // pointee) leaves the walk no expression for the whole.
                    StatementKind::Assign((place, _))
                    | StatementKind::SetDiscriminant {
                        place: deref!(place),
                        ..
                    } => {
                        post_exprs.remove(&place.local);
                    }
                    _ => {}
                }
            }

            bb = match &bb_data.terminator().kind {
                TerminatorKind::Return => {
                    let value = post_exprs.get(&RETURN_PLACE).cloned();
                    debug!(
                        "extract_post_loop_return: Return in bb{} value={value:?}",
                        bb.as_usize()
                    );
                    return value.map_or(PathValue::Unknown, PathValue::Value);
                }
                // Dropping a value runs its destructor, which may write
                // through a loan the value holds.
                TerminatorKind::Drop { target, .. } => {
                    let Some(tcx) = self.tcx else {
                        return PathValue::Unknown;
                    };
                    self.rebind_handoff(tcx, bb, &mut post_exprs);
                    self.forget_lent(&mut post_exprs);
                    *target
                }
                TerminatorKind::Unreachable
                | TerminatorKind::UnwindResume
                | TerminatorKind::UnwindTerminate(..) => return PathValue::Diverges,
                TerminatorKind::Goto { target, .. }
                | TerminatorKind::Assert { target, .. }
                | TerminatorKind::FalseEdge {
                    real_target: target,
                    ..
                }
                | TerminatorKind::FalseUnwind {
                    real_target: target,
                    ..
                } => *target,
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    ..
                } => {
                    // Ghost blocks lower to `Ghost::new(<inner>)` (and a
                    // snapshot to `Snapshot::new`); a postcondition over
                    // `result` of a function returning one reads `<inner>`
                    // (#873, #2116, #2671). Any other call returns a value the
                    // walk does not model.
                    let ghost_inner = (destination.projection.is_empty()
                        && ghost_constructor_call(self.tcx, func))
                    .then(|| args.first())
                    .flatten()
                    .and_then(|arg0| translate_operand(&arg0.node, &post_exprs));
                    if let Some(tcx) = self.tcx {
                        self.rebind_handoff(tcx, bb, &mut post_exprs);
                    }
                    match ghost_inner {
                        Some(inner) => {
                            post_exprs.insert(destination.local, inner);
                        }
                        None => {
                            // The callee may write through any loan it can
                            // reach from its arguments (`r.take()` for a
                            // `r = &mut o` made before the loop).
                            self.forget_lent(&mut post_exprs);
                            post_exprs.remove(&destination.local);
                        }
                    }
                    match target {
                        Some(target) => *target,
                        None => return PathValue::Diverges,
                    }
                }
                TerminatorKind::SwitchInt { discr, targets } => {
                    // A branch on a constant has one live arm.
                    if let Some(value) = constant_switch_value(discr) {
                        targets.target_for_value(value)
                    } else {
                        return self.branch_value(discr, targets, &post_exprs, &visited);
                    }
                }
                _ => return PathValue::Unknown,
            };
        }
    }

    fn forget_lent(&self, post_exprs: &mut HashMap<Local, PureExpr>) {
        post_exprs.retain(|local, _| !self.lent.contains(local));
    }

    /// Re-binds what the hand-off at the terminator of `bb` may change
    /// (`locals_changed_by_handoff`, the loop-body walk's own answer at the
    /// same terminator) to symbols nothing constrains. A symbol is named by
    /// block and local, and a path visits a block once.
    fn rebind_handoff(
        &self,
        tcx: TyCtxt<'tcx>,
        bb: BasicBlock,
        post_exprs: &mut HashMap<Local, PureExpr>,
    ) {
        let Some(changed) =
            crate::mir_analysis::extract::drop_glue_writes::locals_changed_by_handoff(
                tcx,
                self.body,
                bb,
                self.body.basic_blocks[bb].terminator(),
            )
        else {
            return;
        };
        for local in changed {
            let sort = crate::mir_analysis::translate::ty_to_expr_sort_enriched(
                tcx,
                self.body.local_decls[local].ty,
            );
            post_exprs.insert(
                local,
                PureExpr::Var(
                    format!("$post_loop_handoff_{}_{}", bb.as_u32(), local.as_u32()),
                    sort,
                ),
            );
        }
    }

    /// The value of a branch on `discr`: an `ite` over the arms' values, each
    /// arm walked from the state the branch is taken in.
    fn branch_value(
        &mut self,
        discr: &Operand<'tcx>,
        targets: &SwitchTargets,
        post_exprs: &HashMap<Local, PureExpr>,
        visited: &HashSet<BasicBlock>,
    ) -> PathValue {
        let Some(discr_expr) = translate_operand(discr, post_exprs) else {
            return PathValue::Unknown;
        };
        let mut arms = Vec::new();
        if operand_is_bool(discr, self.body) {
            // `switchInt(b) -> [0: else, otherwise: then]`.
            let mut else_bb = targets.otherwise();
            let mut then_bb = targets.otherwise();
            for (value, target) in targets.iter() {
                match value {
                    0 => else_bb = target,
                    1 => then_bb = target,
                    _ => return PathValue::Unknown,
                }
            }
            arms.push((Some(discr_expr), then_bb));
            arms.push((None, else_bb));
        } else {
            let Some(int_ty) = operand_int_ty(discr, self.body) else {
                return PathValue::Unknown;
            };
            for (value, target) in targets.iter() {
                let Some(value) = switch_value_to_i64(value, int_ty) else {
                    return PathValue::Unknown;
                };
                let guard = PureExpr::BinOp(
                    Arc::new(discr_expr.clone()),
                    BinOp::Eq,
                    Arc::new(PureExpr::Int(value)),
                );
                arms.push((Some(guard), target));
            }
            arms.push((None, targets.otherwise()));
        }

        // Fold from the last arm (the fall-through) back to the first.
        let mut acc = PathValue::Diverges;
        for (guard, target) in arms.into_iter().rev() {
            let arm = self.path_value(target, post_exprs.clone(), visited.clone());
            acc = match (guard, arm, acc) {
                (_, PathValue::Unknown, _) | (_, _, PathValue::Unknown) => {
                    return PathValue::Unknown;
                }
                (_, PathValue::Diverges, rest) => rest,
                (_, value @ PathValue::Value(_), PathValue::Diverges) => value,
                (None, value, _) => value,
                (Some(guard), PathValue::Value(arm), PathValue::Value(rest)) => PathValue::Value(
                    PureExpr::Ite(Arc::new(guard), Arc::new(arm), Arc::new(rest)),
                ),
            };
        }
        acc
    }
}

/// Whether a post-loop call builds a ghost or snapshot value from its argument:
/// the inherent `new` of `Ghost` or `Snapshot`.
///
/// Resolved by the callee rustc names, never by the destination's spelling:
/// any other one-argument call would otherwise be read as the identity. The
/// owner is the impl's self type, because the printed path carries the impl's
/// generic arguments (`creusot_std::Ghost::<T>::new`), which a path match on
/// `Ghost::new` does not see through.
fn ghost_constructor_call<'tcx>(tcx: Option<TyCtxt<'tcx>>, func: &Operand<'tcx>) -> bool {
    let (Some(tcx), Some((def_id, _))) = (tcx, func.const_fn_def()) else {
        return false;
    };
    if tcx.item_name(def_id).as_str() != "new" {
        return false;
    }
    let Some(impl_id) = tcx.impl_of_assoc(def_id) else {
        return false;
    };
    matches!(
        tcx.def_kind(impl_id),
        rustc_hir::def::DefKind::Impl { of_trait: false }
    ) && crate::ghost::type_helpers::is_ghost_like_type(tcx, tcx.type_of(impl_id).skip_binder())
}

/// Every local whose place a mutable borrow or raw pointer lends out anywhere in
/// the body, before, in or after the loop, and, with a `TyCtxt`, every local a
/// shared borrow lends out while its type is not `Freeze` (a `Cell` is written
/// through `&`), as the loop-body walk's lent body-locals are.
///
/// A loan made before the loop is still live after it (`let r = &mut o;` ...
/// loop ... `*r = None; o`), and a write through it names the loan, never the
/// local it points at, so the walk cannot tell which of these locals a write
/// through a pointer, a call or a drop changes. The loop-exit state names such a
/// local only when the loop itself changes it; [`super::extract_loop_body`]
/// drops every other one from the state the walk starts in.
pub(super) fn mutably_lent_locals<'tcx>(
    tcx: Option<TyCtxt<'tcx>>,
    body: &Body<'tcx>,
) -> HashSet<Local> {
    body.basic_blocks
        .iter()
        .flat_map(|data| &data.statements)
        .filter_map(|stmt| match &stmt.kind {
            StatementKind::Assign((_, rvalue)) => mutably_lent_place(rvalue).or_else(|| {
                let (tcx, Rvalue::Ref(_, BorrowKind::Shared, place)) = (tcx?, rvalue) else {
                    return None;
                };
                // The region-erasing query: a place type read from borrow-checked
                // MIR carries region variables, which the bare query cannot hash.
                let ty = place.ty(&body.local_decls, tcx).ty;
                (!is_freeze(tcx, body.typing_env(tcx), ty)).then_some(place)
            }),
            _ => None,
        })
        .map(|place| place.local)
        .collect()
}

/// Every local a statement or call in `blocks` may write. The loop-exit state
/// names a local only when the loop changes it under a name its VC constrains;
/// one the loop writes otherwise has no value at the exit.
pub(super) fn locals_written_in(body: &Body<'_>, blocks: &HashSet<BasicBlock>) -> HashSet<Local> {
    struct Writes(HashSet<Local>);
    impl<'tcx> Visitor<'tcx> for Writes {
        fn visit_local(&mut self, local: Local, context: PlaceContext, _location: Location) {
            if context.is_mutating_use() {
                self.0.insert(local);
            }
        }
    }
    let mut writes = Writes(HashSet::new());
    for bb in blocks {
        writes.visit_basic_block_data(*bb, &body.basic_blocks[*bb]);
    }
    writes.0
}

/// Whether a statement may write through a pointer, and so change a local some
/// loan points at without naming it.
fn statement_may_write_through_a_pointer(kind: &StatementKind<'_>) -> bool {
    match kind {
        StatementKind::Assign((place, _))
        | StatementKind::SetDiscriminant {
            place: deref!(place),
            ..
        } => place.is_indirect(),
        StatementKind::StorageLive(_)
        | StatementKind::StorageDead(_)
        | StatementKind::Nop
        | StatementKind::FakeRead(_)
        | StatementKind::PlaceMention(_)
        | StatementKind::Coverage(_)
        | StatementKind::ConstEvalCounter
        | StatementKind::BackwardIncompatibleDropHint { .. }
        | StatementKind::AscribeUserType(..) => false,
        // An intrinsic (`copy_nonoverlapping` writes through its destination)
        // or a kind this list does not name.
        _ => true,
    }
}

/// The place a mutable borrow or raw pointer lends out, if `rvalue` makes one.
/// A raw pointer of either mutability counts: a `*const` can be cast and
/// written through.
fn mutably_lent_place<'a, 'tcx>(rvalue: &'a Rvalue<'tcx>) -> Option<&'a Place<'tcx>> {
    match rvalue {
        Rvalue::Ref(_, BorrowKind::Mut { .. }, place) => Some(place),
        Rvalue::RawPtr(kind, place) if !matches!(kind, RawPtrKind::FakeForPtrMetadata) => {
            Some(place)
        }
        _ => None,
    }
}

fn constant_switch_value(discr: &Operand<'_>) -> Option<u128> {
    let Operand::Constant(constant) = discr else {
        return None;
    };
    let scalar = constant.const_.try_to_scalar_int()?;
    Some(scalar.to_uint(scalar.size()))
}

/// One post-loop assignment's value.
///
/// The syntax-only translator reads a one-field aggregate as its field and a
/// field-less one as the unit tuple, which for an enum drops the variant:
/// `Err(i)` and `Ok(i)` both read as `i`. A returned value is the function's
/// `result`, which a postcondition may test for its variant, so an enum value
/// is read, whenever the `TyCtxt` is at hand, by the translator the
/// function-body extraction reads it with.
fn translate_post_loop_rvalue<'tcx>(
    tcx: Option<TyCtxt<'tcx>>,
    rvalue: &Rvalue<'tcx>,
    post_exprs: &HashMap<Local, PureExpr>,
    body: &Body<'tcx>,
) -> Option<PureExpr> {
    if let Some(tcx) = tcx {
        if rvalue_is_enum_value(tcx, rvalue) {
            return translate_rvalue_with_enum_variants(
                tcx,
                rvalue,
                post_exprs,
                Some(body),
                None,
                None,
            );
        }
    }
    translate_rvalue(rvalue, post_exprs, Some(body))
}

fn rvalue_is_enum_value<'tcx>(tcx: TyCtxt<'tcx>, rvalue: &Rvalue<'tcx>) -> bool {
    match rvalue {
        Rvalue::Aggregate(AggregateKind::Adt(def_id, ..), _) => tcx.adt_def(*def_id).is_enum(),
        Rvalue::Use(Operand::Constant(constant), _) => {
            matches!(constant.ty().kind(), rustc_middle::ty::TyKind::Adt(adt_def, _) if adt_def.is_enum())
        }
        _ => false,
    }
}

/// Find the block reached when the loop condition evaluates to exit.
pub(crate) fn find_post_loop_exit_block(
    body: &Body<'_>,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
) -> Option<BasicBlock> {
    let cond_data = &body.basic_blocks[cond_block];
    match &cond_data.terminator().kind {
        TerminatorKind::SwitchInt { targets, .. } => {
            recover_post_loop_exit_block(body, cond_block, loop_info, targets).or_else(|| {
                targets
                    .all_targets()
                    .iter()
                    .copied()
                    .find(|target| {
                        !loop_info.body_blocks.contains(target)
                            && !matches!(
                                body.basic_blocks[*target].terminator().kind,
                                TerminatorKind::Unreachable
                            )
                    })
                    .or_else(|| {
                        targets
                            .all_targets()
                            .iter()
                            .copied()
                            .find(|target| !loop_info.body_blocks.contains(target))
                    })
            })
        }
        _ => None,
    }
}

fn recover_post_loop_exit_block(
    body: &Body<'_>,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
    targets: &rustc_middle::mir::SwitchTargets,
) -> Option<BasicBlock> {
    // Some desugarings route the loop-exit arm through a block that loop
    // detection conservatively keeps inside `body_blocks`. Recover the real
    // exit arm by looking for the unique switch target that can reach `Return`
    // without ever flowing back to the loop header/condition. (#2171)
    let mut exit_candidates = Vec::new();
    for target in targets.all_targets().iter().copied() {
        let reaches_return =
            reaches_return_without_loop_reentry(body, target, cond_block, loop_info);
        let reaches_reentry = reaches_loop_reentry(body, target, cond_block, loop_info);
        if reaches_return && !reaches_reentry {
            exit_candidates.push(target);
        }
    }

    let mut exit_targets = exit_candidates.into_iter();
    let exit = exit_targets.next()?;
    if exit_targets.next().is_none() {
        Some(exit)
    } else {
        None
    }
}

fn reaches_return_without_loop_reentry(
    body: &Body<'_>,
    start: BasicBlock,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
) -> bool {
    let mut visited = HashSet::new();
    let mut worklist = vec![start];

    while let Some(bb) = worklist.pop() {
        if !visited.insert(bb) {
            continue;
        }
        if bb == cond_block || bb == loop_info.header {
            continue;
        }
        let bb_data = &body.basic_blocks[bb];
        if matches!(bb_data.terminator().kind, TerminatorKind::Return) {
            return true;
        }
        match &bb_data.terminator().kind {
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => {
                worklist.push(*real_target);
            }
            _ => {
                for succ in bb_data.terminator().successors() {
                    worklist.push(succ);
                }
            }
        }
    }

    false
}

fn reaches_loop_reentry(
    body: &Body<'_>,
    start: BasicBlock,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
) -> bool {
    let mut visited = HashSet::new();
    let mut worklist = vec![start];

    while let Some(bb) = worklist.pop() {
        if !visited.insert(bb) {
            continue;
        }
        if bb == cond_block || bb == loop_info.header {
            return true;
        }
        match &body.basic_blocks[bb].terminator().kind {
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => {
                worklist.push(*real_target);
            }
            _ => {
                for succ in body.basic_blocks[bb].terminator().successors() {
                    worklist.push(succ);
                }
            }
        }
    }

    false
}

/// Walk post-loop blocks from the exit block, calling `visitor` on each block.
/// Handles visited tracking, loop-header guards, and FalseEdge/FalseUnwind
/// successor patterns.
fn walk_post_loop_blocks<'tcx, F>(
    body: &Body<'tcx>,
    exit_block: BasicBlock,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
    mut visitor: F,
) -> ControlFlow<()>
where
    F: FnMut(&BasicBlock, &BasicBlockData<'tcx>) -> ControlFlow<()>,
{
    let mut visited = HashSet::new();
    let mut worklist = vec![exit_block];
    while let Some(bb) = worklist.pop() {
        if !visited.insert(bb) {
            continue;
        }
        if bb == cond_block || bb == loop_info.header {
            continue;
        }
        let bb_data = &body.basic_blocks[bb];
        if visitor(&bb, bb_data).is_break() {
            return ControlFlow::Break(());
        }
        match &bb_data.terminator().kind {
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => {
                worklist.push(*real_target);
            }
            _ => {
                for succ in bb_data.terminator().successors() {
                    worklist.push(succ);
                }
            }
        }
    }
    ControlFlow::Continue(())
}

/// Extract mutable-borrow dereference writes that occur after loop exit.
///
/// Tracks direct writes (`*v = expr`) and temporary-mediated writes
/// (`_tmp = *v; *_tmp = expr`) along paths from loop exit to function return.
pub(super) fn extract_post_loop_deref_writes<'tcx>(
    body: &Body<'tcx>,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
    local_to_name: &HashMap<Local, String>,
) -> HashSet<String> {
    let Some(exit_block) = find_post_loop_exit_block(body, cond_block, loop_info) else {
        return HashSet::new();
    };

    let mut writes = HashSet::new();
    let mut deref_aliases: HashMap<Local, String> = HashMap::new();
    let _ = walk_post_loop_blocks(body, exit_block, cond_block, loop_info, |_bb, bb_data| {
        for stmt in &bb_data.statements {
            if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
                update_post_loop_deref_alias(place, rvalue, local_to_name, &mut deref_aliases);
                if let Some(root) = post_loop_deref_write_root(place, local_to_name, &deref_aliases)
                {
                    writes.insert(root);
                }
            }
        }
        ControlFlow::Continue(())
    });
    writes
}

/// Extract post-loop deref-write final values: maps `&mut` parameter names to
/// their final symbolic expressions assigned after the loop exits.
///
/// For `set_after_loop(x: &mut i32, n: i32) { while ... { *x = 0; } *x = n; }`,
/// returns `{"x" -> Var("n")}`. This provides the `final_values` needed by
/// `verify_mut_borrow_function_with_modes` when `extract_mut_borrow_body` returns
/// `None` due to loop cycle detection.
///
/// Walks the same post-loop blocks as `extract_post_loop_deref_writes` but also
/// tracks symbolic values via `translate_rvalue` to resolve the written expression.
pub(super) fn extract_post_loop_deref_final_values<'tcx>(
    body: &Body<'tcx>,
    cond_block: BasicBlock,
    loop_info: &LoopInfo,
    local_to_name: &HashMap<Local, String>,
    local_exprs: &HashMap<Local, PureExpr>,
) -> HashMap<String, PureExpr> {
    let Some(exit_block) = find_post_loop_exit_block(body, cond_block, loop_info) else {
        return HashMap::new();
    };

    let mut final_values = HashMap::new();
    let mut deref_aliases: HashMap<Local, String> = HashMap::new();
    // Track symbolic expressions for locals in post-loop blocks, starting from
    // the expressions established before the loop (pre-loop assignments + args).
    let mut post_exprs = local_exprs.clone();
    let bail = walk_post_loop_blocks(body, exit_block, cond_block, loop_info, |_bb, bb_data| {
        for stmt in &bb_data.statements {
            if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
                // Update deref alias tracking (reborrows like `_tmp = &mut *x`).
                update_post_loop_deref_alias(place, rvalue, local_to_name, &mut deref_aliases);

                if place.projection.is_empty() {
                    // Plain local assignment: update symbolic state.
                    if let Some(expr) = translate_rvalue(rvalue, &post_exprs, Some(body)) {
                        post_exprs.insert(place.local, expr);
                    }
                } else if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
                    // Deref write: `*local = rvalue`. Resolve the root param name
                    // and the rvalue to a symbolic expression.
                    if let Some(root) =
                        post_loop_deref_root_for_local(place.local, local_to_name, &deref_aliases)
                    {
                        if let Some(expr) = translate_rvalue(rvalue, &post_exprs, Some(body)) {
                            final_values.insert(root, expr);
                        }
                    }
                }
            }
        }

        // Soundness guard (#2085): if a post-loop block branches (SwitchInt),
        // we cannot determine which path will be taken, so deref final values
        // extracted from different branches would be unsound (last-write-wins
        // is path-insensitive). Bail conservatively with an empty map.
        if matches!(bb_data.terminator().kind, TerminatorKind::SwitchInt { .. }) {
            return ControlFlow::Break(());
        }

        ControlFlow::Continue(())
    });

    if bail.is_break() {
        return HashMap::new();
    }

    final_values
}

fn update_post_loop_deref_alias(
    place: &Place<'_>,
    rvalue: &Rvalue<'_>,
    local_to_name: &HashMap<Local, String>,
    deref_aliases: &mut HashMap<Local, String>,
) {
    if !place.projection.is_empty() {
        return;
    }
    if let Some(root) = rvalue_post_loop_deref_root(rvalue, local_to_name, deref_aliases) {
        deref_aliases.insert(place.local, root);
    } else {
        deref_aliases.remove(&place.local);
    }
}

fn rvalue_post_loop_deref_root(
    rvalue: &Rvalue<'_>,
    local_to_name: &HashMap<Local, String>,
    deref_aliases: &HashMap<Local, String>,
) -> Option<String> {
    let source_place = match rvalue {
        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), _)
        | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _) => Some(src),
        Rvalue::Ref(_, _, src) => Some(src),
        _ => None,
    }?;
    if matches!(source_place.projection.first(), Some(ProjectionElem::Deref)) {
        post_loop_deref_root_for_local(source_place.local, local_to_name, deref_aliases)
    } else if source_place.projection.is_empty() {
        deref_aliases.get(&source_place.local).cloned()
    } else {
        None
    }
}

fn post_loop_deref_write_root(
    place: &Place<'_>,
    local_to_name: &HashMap<Local, String>,
    deref_aliases: &HashMap<Local, String>,
) -> Option<String> {
    if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
        return None;
    }
    post_loop_deref_root_for_local(place.local, local_to_name, deref_aliases)
}

fn post_loop_deref_root_for_local(
    local: Local,
    local_to_name: &HashMap<Local, String>,
    deref_aliases: &HashMap<Local, String>,
) -> Option<String> {
    deref_aliases
        .get(&local)
        .cloned()
        .or_else(|| local_to_name.get(&local).cloned())
}
