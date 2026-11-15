// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A write the loop condition makes on the pass that leaves the loop.
//!
//! The path from a loop header to its exit switch runs once more after the
//! last state an invariant describes: `while { let b = lt3(n); i = 0; b }`
//! leaves with `i == 0` although `i == 7` holds at every header. The
//! loop-invariant path reads its exit VC and the post-loop continuation at
//! the header state, so a local that path writes and the code after the loop
//! reads is read there at a value the program does not hold
//! (loop_condition_block_write_before_exit_read_after.rs). Such a loop is
//! refused as one with a `break` is (`loop_has_unmodeled_exit`).
//!
//! A write counts when code after the exit can read what it wrote: the
//! written local is the return place, is used after the exit, or has its
//! address taken off the path while code after the exit uses a value that may
//! hold a pointer. A `Drop` after the exit uses the dropped
//! value only when its glue may write (D-140). A store through a pointer and
//! a callee handed write access count unless the access is a borrow the path
//! itself made of a local that does not count. A `for` loop's
//! `Iterator::next` is stated by the loop's own iterator facts and is left
//! out.

use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
        BasicBlock, Body, Local, Location, NonDivergingIntrinsic, Operand, Place, Rvalue,
        StatementKind, Terminator, TerminatorKind, RETURN_PLACE,
    },
    ty::{Mutability, Ty, TyCtxt, TyKind},
};

use super::{
    super::loops::LoopInfo,
    drop_glue_writes::{locals_changed_by_call, locals_changed_by_drop},
    loop_merges::{normal_successors, reach},
};

/// The first write on the path from `loop_info`'s header to the exit switch
/// of the edge `cond_block -> exit` that code after the loop can read,
/// described for the trace; `None` when there is none. The edge is the one
/// the loop lane reads (`loop_lane_exit`).
pub(crate) fn loop_condition_exit_write<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    loop_info: &LoopInfo,
    (cond_block, exit): (BasicBlock, BasicBlock),
) -> Option<String> {
    let header = loop_info.header;
    let post = reach(body, exit, |bb| bb == header);
    let region = reach(body, header, |bb| post.contains(&bb));
    let path = path_to_switch(body, header, cond_block, &region);
    let seen = AfterExit::new(tcx, body, &post, &path);
    let mut blocks: Vec<BasicBlock> = path.iter().copied().collect();
    blocks.sort();
    for bb in blocks {
        let data = &body.basic_blocks[bb];
        for stmt in &data.statements {
            let written = match &stmt.kind {
                StatementKind::Assign((place, _))
                | StatementKind::SetDiscriminant {
                    place: deref!(place),
                    ..
                } => place,
                StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(_)) => {
                    return Some(format!("a copy through a pointer in {bb:?}"));
                }
                _ => continue,
            };
            if seen.write_counts(written) {
                return Some(format!("a store to `{written:?}` in {bb:?}"));
            }
        }
        // The exit switch itself writes nothing.
        if bb == cond_block {
            continue;
        }
        let terminator = data.terminator();
        match &terminator.kind {
            TerminatorKind::Goto { .. }
            | TerminatorKind::FalseUnwind { .. }
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::Assert { .. }
            | TerminatorKind::SwitchInt { .. }
            | TerminatorKind::Unreachable => {}
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                if is_for_loop_next(tcx, terminator, func) {
                    continue;
                }
                if seen.write_counts(destination) {
                    return Some(format!("the call's result `{destination:?}` in {bb:?}"));
                }
                if let Some(arg) = args.iter().find(|arg| {
                    operand_lends_write(tcx, body, &arg.node) && !seen.lends_unseen(&arg.node)
                }) {
                    return Some(format!(
                        "a call handed write access by `{:?}` in {bb:?}",
                        arg.node
                    ));
                }
                if locals_changed_by_call(tcx, body, bb, func, args, destination)
                    .is_some_and(|changed| changed.into_iter().any(|local| seen.local(local)))
                {
                    return Some(format!(
                        "the drop glue of a value the call in {bb:?} is handed"
                    ));
                }
            }
            TerminatorKind::Drop { place, .. } => {
                if locals_changed_by_drop(tcx, body, place)
                    .is_some_and(|changed| changed.into_iter().any(|local| seen.local(local)))
                {
                    return Some(format!("the drop glue of `{place:?}` in {bb:?}"));
                }
            }
            _ => return Some(format!("a {:?} terminator in {bb:?}", terminator.kind)),
        }
    }
    None
}

/// The blocks of `region` from which `cond_block` is reached without passing
/// the header again: what runs between the last header and the exit switch.
fn path_to_switch(
    body: &Body<'_>,
    header: BasicBlock,
    cond_block: BasicBlock,
    region: &HashSet<BasicBlock>,
) -> HashSet<BasicBlock> {
    let mut preds: HashMap<BasicBlock, Vec<BasicBlock>> = HashMap::new();
    for &bb in region {
        for succ in normal_successors(body, bb) {
            if region.contains(&succ) {
                preds.entry(succ).or_default().push(bb);
            }
        }
    }
    let mut path = HashSet::new();
    let mut stack = vec![cond_block];
    while let Some(bb) = stack.pop() {
        if !path.insert(bb) || bb == header {
            continue;
        }
        stack.extend(preds.get(&bb).into_iter().flatten().copied());
    }
    path
}

/// Which locals code after the exit can read.
struct AfterExit<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    /// Used by a statement or terminator after the exit.
    used: HashSet<Local>,
    /// Borrowed by a statement off the path, while code after the exit uses
    /// a value that may hold a pointer: a borrow made before the loop may be
    /// read through after it.
    address_taken: HashSet<Local>,
    /// Per local, its projection-free assignment on the path.
    path_definitions: HashMap<Local, &'a Rvalue<'tcx>>,
    /// Per local, how often the body changes the local itself, the entry
    /// value of an argument included: a pointer's path definition is the
    /// value it holds at a store on the path only when it is its one change.
    /// A value from before the loop or from the body, `r = &mut x` before
    /// `zero(r); r = &mut u`, reaches the exit pass's first use.
    direct_changes: HashMap<Local, usize>,
}

impl<'a, 'tcx> AfterExit<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        post: &HashSet<BasicBlock>,
        path: &HashSet<BasicBlock>,
    ) -> Self {
        let mut uses = UsesAfterExit {
            tcx,
            body,
            used: HashSet::new(),
        };
        for &bb in post {
            uses.visit_basic_block_data(bb, &body.basic_blocks[bb]);
        }
        let mut address_taken = HashSet::new();
        let mut path_definitions: HashMap<Local, &'a Rvalue<'tcx>> = HashMap::new();
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            let on_path = path.contains(&bb);
            for stmt in &data.statements {
                let StatementKind::Assign((place, rvalue)) = &stmt.kind else {
                    continue;
                };
                if on_path {
                    if place.projection.is_empty() {
                        path_definitions.insert(place.local, rvalue);
                    }
                } else if let Rvalue::Ref(_, _, borrowed) | Rvalue::RawPtr(_, borrowed) = rvalue {
                    if !borrowed.is_indirect() {
                        address_taken.insert(borrowed.local);
                    }
                }
            }
        }
        let mut changes = DirectChanges(
            body.args_iter()
                .map(|arg| (arg, 1))
                .collect::<HashMap<Local, usize>>(),
        );
        changes.visit_body(body);
        let reads_a_pointer = std::iter::once(RETURN_PLACE)
            .chain(uses.used.iter().copied())
            .any(|local| {
                ty_may_hold_pointer(tcx, body.local_decls[local].ty, &mut HashSet::new(), 0)
            });
        if !reads_a_pointer {
            address_taken.clear();
        }
        Self {
            tcx,
            body,
            used: uses.used,
            address_taken,
            path_definitions,
            direct_changes: changes.0,
        }
    }

    fn local(&self, local: Local) -> bool {
        local == RETURN_PLACE || self.used.contains(&local) || self.address_taken.contains(&local)
    }

    /// Whether code after the exit can read what a store to `place` wrote.
    fn write_counts(&self, place: &Place<'tcx>) -> bool {
        if place.is_indirect() {
            return !self.points_to_unseen(place.local, 0);
        }
        self.local(place.local)
    }

    /// Whether `operand` is a borrow the path made of a local code after the
    /// exit cannot read.
    fn lends_unseen(&self, operand: &Operand<'tcx>) -> bool {
        match operand {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                self.points_to_unseen(place.local, 0)
            }
            _ => false,
        }
    }

    /// Whether `local` holds a borrow the path made, directly or through a
    /// reborrow or a copy the path also made, of a local code after the exit
    /// cannot read and whose value lends no write: a write through the borrow
    /// stays in that local. A local that holds a `&mut` or a raw pointer
    /// (`h = H { r: &mut x }`) hands a callee given `&mut h` the memory it
    /// points to, which code after the exit may read (`h.reset()`, then `x`).
    fn points_to_unseen(&self, local: Local, depth: usize) -> bool {
        if depth > 16 || self.local(local) || self.direct_changes.get(&local) != Some(&1) {
            return false;
        }
        match self.path_definitions.get(&local).copied() {
            Some(Rvalue::Ref(_, _, borrowed) | Rvalue::RawPtr(_, borrowed)) => {
                if borrowed.is_indirect() {
                    self.points_to_unseen(borrowed.local, depth + 1)
                } else {
                    !self.local(borrowed.local)
                        && !ty_lends_write(
                            self.tcx,
                            self.body,
                            self.body.local_decls[borrowed.local].ty,
                            &mut HashSet::new(),
                            0,
                        )
                }
            }
            Some(Rvalue::Use(Operand::Copy(source) | Operand::Move(source), _))
                if source.projection.is_empty() =>
            {
                self.points_to_unseen(source.local, depth + 1)
            }
            _ => false,
        }
    }
}

/// Per local, the statements and terminators that change the local itself:
/// an assignment, a call's destination, a `&mut` or raw borrow of it. A store
/// through it (`*r = 0`) changes memory, not `r`.
struct DirectChanges(HashMap<Local, usize>);

impl<'tcx> Visitor<'tcx> for DirectChanges {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, _location: Location) {
        let changes = match context {
            PlaceContext::MutatingUse(MutatingUseContext::Drop) => false,
            PlaceContext::MutatingUse(_)
            | PlaceContext::NonMutatingUse(NonMutatingUseContext::RawBorrow) => true,
            _ => false,
        };
        if changes && !place.is_indirect() {
            *self.0.entry(place.local).or_default() += 1;
        }
    }
}

struct UsesAfterExit<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    used: HashSet<Local>,
}

impl<'tcx> Visitor<'tcx> for UsesAfterExit<'_, 'tcx> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Drop { place, .. } = &terminator.kind {
            if locals_changed_by_drop(self.tcx, self.body, place).is_some() {
                self.used.insert(place.local);
            }
            return;
        }
        self.super_terminator(terminator, location);
    }

    fn visit_local(&mut self, local: Local, context: PlaceContext, _location: Location) {
        if !matches!(
            context,
            PlaceContext::NonUse(_) | PlaceContext::MutatingUse(MutatingUseContext::Drop)
        ) {
            self.used.insert(local);
        }
    }
}

/// The `Iterator::next` call a `for` loop's desugaring makes.
fn is_for_loop_next<'tcx>(
    tcx: TyCtxt<'tcx>,
    terminator: &Terminator<'tcx>,
    func: &Operand<'tcx>,
) -> bool {
    terminator
        .source_info
        .span
        .is_desugaring(rustc_span::DesugaringKind::ForLoop)
        && func.const_fn_def().is_some_and(|(def_id, _)| {
            tcx.is_lang_item(def_id, rustc_attr_ir::LangItem::IteratorNext)
        })
}

/// Whether a callee handed `operand` may write memory through it: it holds a
/// `&mut` or a raw pointer by value, or a shared reference to memory with
/// interior mutability. Through a shared reference nothing else is written,
/// and a type parameter behind one is stable, as
/// `ty_may_reach_interior_mutability` reads it.
fn operand_lends_write<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> bool {
    let ty = operand.ty(&body.local_decls, tcx);
    ty_lends_write(tcx, body, ty, &mut HashSet::new(), 0)
}

pub(super) fn ty_lends_write<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    ty: Ty<'tcx>,
    visited: &mut HashSet<Ty<'tcx>>,
    depth: usize,
) -> bool {
    if depth > 64 {
        return true;
    }
    if !visited.insert(ty) {
        return false;
    }
    let mut recurse = |t: Ty<'tcx>| ty_lends_write(tcx, body, t, visited, depth + 1);
    match ty.kind() {
        TyKind::Ref(_, _, Mutability::Mut) | TyKind::RawPtr(..) => true,
        TyKind::Ref(_, inner, Mutability::Not) => {
            super::loop_body::ty_may_reach_interior_mutability_in(tcx, body.typing_env(tcx), *inner)
        }
        // A standard type's raw pointers point into memory it owns, whose
        // values are its type arguments; one that holds a borrow has a
        // lifetime argument.
        TyKind::Adt(adt, args)
            if matches!(
                tcx.crate_name(adt.did().krate).as_str(),
                "core" | "alloc" | "std" | "hashbrown"
            ) =>
        {
            args.iter().any(|arg| arg.as_region().is_some()) || args.types().any(&mut recurse)
        }
        TyKind::Adt(adt, args) => adt
            .all_fields()
            .any(|field| recurse(field.ty(tcx, *args).skip_norm_wip())),
        TyKind::Tuple(tys) => tys.iter().any(&mut recurse),
        TyKind::Array(elem, _) | TyKind::Slice(elem) => recurse(*elem),
        TyKind::Closure(_, args) => args.as_closure().upvar_tys().iter().any(&mut recurse),
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Never
        | TyKind::FnDef(..)
        | TyKind::FnPtr(..) => false,
        _ => true,
    }
}

/// Whether a value of type `ty` may hold a reference or a raw pointer.
fn ty_may_hold_pointer<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    visited: &mut HashSet<Ty<'tcx>>,
    depth: usize,
) -> bool {
    if depth > 64 {
        return true;
    }
    if !visited.insert(ty) {
        return false;
    }
    let mut recurse = |t: Ty<'tcx>| ty_may_hold_pointer(tcx, t, visited, depth + 1);
    match ty.kind() {
        TyKind::Ref(..) | TyKind::RawPtr(..) => true,
        // As in `ty_lends_write`: a standard type's own pointers reach only
        // values of its type arguments.
        TyKind::Adt(adt, args)
            if matches!(
                tcx.crate_name(adt.did().krate).as_str(),
                "core" | "alloc" | "std" | "hashbrown"
            ) =>
        {
            args.iter().any(|arg| arg.as_region().is_some()) || args.types().any(&mut recurse)
        }
        TyKind::Adt(adt, args) => adt
            .all_fields()
            .any(|field| recurse(field.ty(tcx, *args).skip_norm_wip())),
        TyKind::Tuple(tys) => tys.iter().any(&mut recurse),
        TyKind::Array(elem, _) | TyKind::Slice(elem) => recurse(*elem),
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Never
        | TyKind::FnDef(..)
        | TyKind::FnPtr(..) => false,
        _ => true,
    }
}
