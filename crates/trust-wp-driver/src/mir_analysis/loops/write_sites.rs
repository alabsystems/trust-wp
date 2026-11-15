// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Which locals a MIR statement or terminator may change.
//!
//! The loop analyses (the pre-loop binding drop, a loop's changed-places set
//! and the post-loop frame, the multi-loop exit-fact staleness filter) all
//! consume this set. Counting only `Assign` and `Call` destinations as writes
//! leaves a write through a `&mut` borrow invisible:
//!
//! ```text
//! #[ensures(^x == -5i32)] fn setneg(x: &mut i32)
//! let mut x = 1; while i < n { setneg(&mut x); i += 1 }
//! while j < n { need_pos(x); j += 1 }          // verified with x == 1
//! ```
//!
//! [`WriteSites::writes_at`] reports every local whose value (or pointee) a
//! location may change:
//!
//! * every `MutatingUse` base local: stores, call destinations, `&mut` and
//!   `&raw` borrows (a borrow is where the capability to write is created),
//!   drops, discriminant writes, yield resume places, asm outputs;
//! * for a store through a pointer (`*p = v`, `(*p).f = v`, `&mut *p`), every
//!   local the base local's value may point to;
//! * for a call, tail call or drop whose operand may carry a write capability
//!   (`&mut`, raw pointer, or a value that may hide one), every local that
//!   operand may point to, and transitively every local the pointers stored
//!   in those locals may point to (the callee can write through them).
//!
//! "May point to" follows the definitions of a pointer-carrying local: a
//! borrow of a place, a copy / move / pointer cast of another local, an
//! aggregate of operands, or a call result (bounded by its arguments). A
//! reference parameter points to its own pointee. When a step is not
//! understood (the local is itself address-taken or written through a
//! projection, an int-to-pointer cast, a value read out of a projection...)
//! the answer is the FALLBACK: every address-taken local and every local whose
//! type may carry a write capability. Over-approximating only removes
//! premises.
//!
//! Shared references are not write capabilities. For `Freeze` pointees that
//! is Rust semantics; for interior-mutable pointees it is the value model the
//! rest of trust-wp (and Creusot) already uses, where a shared borrow does not
//! change the logical value. This module does not widen that model.

use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{
        visit::{MutatingUseContext, PlaceContext, Visitor},
        BasicBlock, Body, BorrowKind, CastKind, Local, Location, NonDivergingIntrinsic, Operand,
        Place, ProjectionElem, RawPtrKind, Rvalue, Statement, StatementKind, Terminator,
        TerminatorKind,
    },
    ty::{Mutability, Ty, TyKind},
};

use super::changed_places::{place_projection_to_tree, ChangedPlacesTree};

/// How a location may change one local.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LocalWrite {
    /// Which part of the local may change (`Deref(Changed)`: only the pointee
    /// of a reference / raw pointer local).
    pub(crate) tree: ChangedPlacesTree,
    /// `true` when the ONLY way this location changes the local is as the
    /// destination of an `Assign` or a `Call` (the lane the pre-existing
    /// analyses already track, with the written value known to them).
    pub(crate) direct: bool,
}

/// Locals a location (or set of locations) may change.
pub(crate) type LocalWrites = HashMap<Local, LocalWrite>;

fn add_write(out: &mut LocalWrites, local: Local, tree: ChangedPlacesTree, direct: bool) {
    out.entry(local)
        .and_modify(|existing| {
            existing.tree.merge(&tree);
            existing.direct &= direct;
        })
        .or_insert(LocalWrite { tree, direct });
}

fn merge_writes(out: &mut LocalWrites, other: LocalWrites) {
    for (local, write) in other {
        add_write(out, local, write.tree, write.direct);
    }
}

fn pointee_tree() -> ChangedPlacesTree {
    ChangedPlacesTree::Deref(Box::new(ChangedPlacesTree::Changed))
}

fn has_deref(place: &Place<'_>) -> bool {
    place
        .projection
        .iter()
        .any(|elem| matches!(elem, ProjectionElem::Deref))
}

/// Whether a value of type `ty` may carry a capability to write memory that is
/// not part of the value itself: a `&mut`, a raw pointer, or a type that may
/// hide one.
///
/// `opaque_pointers` is the body-level escape hatch: when the body creates a
/// raw pointer or performs a pointer cast, ANY aggregate may hide a pointer at
/// a local, and every ADT answers `true`.
///
/// The interesting case is an ADT. A struct, enum or closure can only hold a
/// borrow of a caller's local when it has a lifetime parameter (after borrowck
/// MIR still carries an erased region argument for one), or a type parameter
/// instantiated with a capability-carrying type, or a closure capture that
/// carries one. The remaining ways — a `&'static mut` field, or a raw pointer
/// aimed at a local — both need a raw-pointer or transmute step in this body
/// to aim at a local at all, which is what `opaque_pointers` reports. A union
/// hides its fields' types from this walk, so a union always answers `true`.
///
/// Shared references answer `false`: trust-wp's value model (like Creusot's)
/// treats `&T` as unable to change the pointee's logical value. This module
/// does not widen or narrow that model; interior mutability is a pre-existing
/// gap elsewhere in the tool, not one introduced here.
pub(crate) fn ty_may_carry_write_capability(ty: Ty<'_>, opaque_pointers: bool) -> bool {
    let rec = |t: Ty<'_>| ty_may_carry_write_capability(t, opaque_pointers);
    match ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Never
        | TyKind::FnDef(..)
        | TyKind::FnPtr(..) => false,
        TyKind::Ref(_, _, Mutability::Not) => false,
        TyKind::Ref(_, _, Mutability::Mut) | TyKind::RawPtr(..) => true,
        TyKind::Array(elem, _) | TyKind::Slice(elem) => rec(*elem),
        TyKind::Tuple(elems) => elems.iter().any(rec),
        TyKind::Closure(_, args) => {
            opaque_pointers || args.as_closure().upvar_tys().iter().any(rec)
        }
        TyKind::Adt(def, args) => {
            opaque_pointers
                || def.is_union()
                // A lifetime parameter may be the lifetime of a `&mut` field.
                || args.iter().any(|arg| {
                    arg.as_region().is_some() || arg.as_type().is_some_and(rec)
                })
        }
        // Coroutines, trait objects, projections, parameters and everything
        // else: may hide a `&mut`.
        _ => true,
    }
}

/// Whether `body` ever creates a raw pointer or casts one, so that a pointer
/// aimed at one of its locals can hide inside an aggregate ([`ty_may_carry_write_capability`]).
fn body_has_opaque_pointer_activity(body: &Body<'_>) -> bool {
    struct Scan(bool);
    impl<'tcx> Visitor<'tcx> for Scan {
        fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
            match rvalue {
                Rvalue::RawPtr(..) => self.0 = true,
                Rvalue::Cast(kind, _, _) => {
                    // Numeric, unsizing and closure-to-fn-pointer casts cannot
                    // turn a value into a pointer at one of this body's locals;
                    // every other cast may.
                    if !matches!(
                        kind,
                        CastKind::IntToInt
                            | CastKind::FloatToInt
                            | CastKind::FloatToFloat
                            | CastKind::IntToFloat
                            | CastKind::PointerCoercion(
                                rustc_middle::ty::adjustment::PointerCoercion::Unsize
                                    | rustc_middle::ty::adjustment::PointerCoercion::ClosureFnPointer(_)
                                    | rustc_middle::ty::adjustment::PointerCoercion::ReifyFnPointer(_),
                                _
                            )
                    ) {
                        self.0 = true;
                    }
                }
                _ => {}
            }
            self.super_rvalue(rvalue, location);
        }
        fn visit_terminator(&mut self, term: &Terminator<'tcx>, location: Location) {
            if matches!(term.kind, TerminatorKind::InlineAsm { .. }) {
                self.0 = true;
            }
            self.super_terminator(term, location);
        }
    }
    let mut scan = Scan(false);
    scan.visit_body(body);
    scan.0
}

/// Per-body write-site summary. Build once per body with [`WriteSites::new`].
pub(crate) struct WriteSites<'a, 'tcx> {
    body: &'a Body<'tcx>,
    /// Projection-free `Assign` / `Call` definition sites of each local.
    defs: HashMap<Local, Vec<Location>>,
    /// Locals whose own value may change other than by a projection-free
    /// `Assign` / `Call` definition: borrowed mutably or raw, written through a
    /// field projection, discriminant writes, yield / asm outputs.
    opaque: HashSet<Local>,
    fallback: LocalWrites,
    /// The body creates or casts raw pointers, so aggregates may hide a
    /// pointer at a local ([`ty_may_carry_write_capability`]).
    opaque_pointers: bool,
}

impl<'a, 'tcx> WriteSites<'a, 'tcx> {
    pub(crate) fn new(body: &'a Body<'tcx>) -> Self {
        struct Scan {
            defs: HashMap<Local, Vec<Location>>,
            opaque: HashSet<Local>,
            address_taken: HashMap<Local, ChangedPlacesTree>,
        }
        impl<'tcx> Visitor<'tcx> for Scan {
            fn visit_place(
                &mut self,
                place: &Place<'tcx>,
                context: PlaceContext,
                location: Location,
            ) {
                if let PlaceContext::MutatingUse(kind) = context {
                    if !has_deref(place) {
                        match kind {
                            MutatingUseContext::Store | MutatingUseContext::Call
                                if place.projection.is_empty() =>
                            {
                                self.defs.entry(place.local).or_default().push(location);
                            }
                            MutatingUseContext::Drop => {}
                            MutatingUseContext::Borrow | MutatingUseContext::RawBorrow => {
                                self.opaque.insert(place.local);
                                let tree = place_projection_to_tree(place.projection);
                                self.address_taken
                                    .entry(place.local)
                                    .and_modify(|existing| existing.merge(&tree))
                                    .or_insert(tree);
                            }
                            _ => {
                                self.opaque.insert(place.local);
                            }
                        }
                    }
                }
            }
            fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
                // `&raw const x` can be cast to `*mut` and written through.
                if let Rvalue::RawPtr(RawPtrKind::Const, place) = rvalue {
                    if !has_deref(place) {
                        self.opaque.insert(place.local);
                        self.address_taken
                            .entry(place.local)
                            .or_insert(ChangedPlacesTree::Changed)
                            .merge(&ChangedPlacesTree::Changed);
                    }
                }
                self.super_rvalue(rvalue, location);
            }
        }
        let opaque_pointers = body_has_opaque_pointer_activity(body);
        let mut scan = Scan {
            defs: HashMap::new(),
            opaque: HashSet::new(),
            address_taken: HashMap::new(),
        };
        scan.visit_body(body);
        let mut fallback = LocalWrites::new();
        for (local, tree) in scan.address_taken {
            add_write(&mut fallback, local, tree, false);
        }
        for (local, decl) in body.local_decls.iter_enumerated() {
            if ty_may_carry_write_capability(decl.ty, opaque_pointers) {
                let tree = if decl.ty.is_ref() || decl.ty.is_raw_ptr() {
                    pointee_tree()
                } else {
                    ChangedPlacesTree::Changed
                };
                add_write(&mut fallback, local, tree, false);
            }
        }
        Self {
            body,
            defs: scan.defs,
            opaque: scan.opaque,
            fallback,
            opaque_pointers,
        }
    }

    /// [`ty_may_carry_write_capability`] under this body's pointer activity.
    fn may_carry(&self, ty: Ty<'tcx>) -> bool {
        ty_may_carry_write_capability(ty, self.opaque_pointers)
    }

    /// Every local any location of `blocks` may change.
    pub(crate) fn writes_in_blocks(
        &self,
        blocks: impl IntoIterator<Item = BasicBlock>,
    ) -> LocalWrites {
        let mut out = LocalWrites::new();
        for bb in blocks {
            let data = &self.body.basic_blocks[bb];
            for statement_index in 0..=data.statements.len() {
                merge_writes(
                    &mut out,
                    self.writes_at(Location {
                        block: bb,
                        statement_index,
                    }),
                );
            }
        }
        out
    }

    /// Every local the statement or terminator at `location` may change.
    pub(crate) fn writes_at(&self, location: Location) -> LocalWrites {
        let data = &self.body.basic_blocks[location.block];
        let mut out = LocalWrites::new();
        if location.statement_index < data.statements.len() {
            self.statement_writes(
                &data.statements[location.statement_index],
                location,
                &mut out,
            );
        } else {
            self.terminator_writes(data.terminator(), location, &mut out);
        }
        out
    }

    fn statement_writes(&self, stmt: &Statement<'tcx>, location: Location, out: &mut LocalWrites) {
        let mut base = BaseWrites {
            sites: self,
            out: LocalWrites::new(),
        };
        base.visit_statement(stmt, location);
        merge_writes(out, base.out);
        if let StatementKind::Assign((place, _)) = &stmt.kind {
            if !has_deref(place) {
                // The destination of a plain assignment is the tracked lane.
                if let Some(write) = out.get_mut(&place.local) {
                    let only_store = !self.borrows_in_statement(stmt, place.local);
                    if only_store {
                        write.direct = true;
                    }
                }
            }
        }
        if let StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(copy)) =
            &stmt.kind
        {
            merge_writes(out, self.operand_targets(&copy.dst, true));
        }
    }

    /// Whether `stmt` also borrows or reads-for-write `local` besides storing
    /// into it (so the store is not its only effect on `local`).
    fn borrows_in_statement(&self, stmt: &Statement<'tcx>, local: Local) -> bool {
        let StatementKind::Assign((_, rvalue)) = &stmt.kind else {
            return true;
        };
        match rvalue {
            Rvalue::Ref(_, BorrowKind::Mut { .. }, borrowed)
            | Rvalue::RawPtr(RawPtrKind::Mut | RawPtrKind::Const, borrowed) => {
                borrowed.local == local
            }
            _ => false,
        }
    }

    fn terminator_writes(
        &self,
        term: &Terminator<'tcx>,
        location: Location,
        out: &mut LocalWrites,
    ) {
        let mut base = BaseWrites {
            sites: self,
            out: LocalWrites::new(),
        };
        base.visit_terminator(term, location);
        merge_writes(out, base.out);
        match &term.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                merge_writes(out, self.operand_targets(func, false));
                for arg in args {
                    merge_writes(out, self.operand_targets(&arg.node, false));
                }
                if !has_deref(destination) && destination.projection.is_empty() {
                    let own_arg = args.iter().any(|arg| {
                        matches!(&arg.node, Operand::Copy(p) | Operand::Move(p) if p.local == destination.local)
                    });
                    if let Some(write) = out.get_mut(&destination.local) {
                        if !own_arg && !self.opaque.contains(&destination.local) {
                            write.direct = true;
                        }
                    }
                }
            }
            TerminatorKind::TailCall { func, args, .. } => {
                merge_writes(out, self.operand_targets(func, false));
                for arg in args {
                    merge_writes(out, self.operand_targets(&arg.node, false));
                }
            }
            TerminatorKind::Drop { place, .. } => {
                if self.may_carry(self.body.local_decls[place.local].ty) {
                    // Drop glue may write through pointers the value holds.
                    let targets = if place.projection.is_empty() {
                        self.local_targets_deep(place.local)
                    } else {
                        None
                    };
                    merge_writes(out, targets.unwrap_or_else(|| self.fallback.clone()));
                }
            }
            TerminatorKind::Yield { .. } | TerminatorKind::InlineAsm { .. } => {
                merge_writes(out, self.fallback.clone());
            }
            _ => {}
        }
    }

    /// Locals a callee receiving `operand` may write through it.
    fn operand_targets(&self, operand: &Operand<'tcx>, pointer_itself: bool) -> LocalWrites {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                // A value read out of a projection carries at most the
                // pointers of the whole local, so the local's targets
                // over-approximate it.
                if let Some(ty) = place_ty_shallow(self.body, place) {
                    if !pointer_itself && !self.may_carry(ty) {
                        return LocalWrites::new();
                    }
                }
                self.local_targets_deep(place.local)
                    .unwrap_or_else(|| self.fallback.clone())
            }
            Operand::Constant(constant) => {
                if contains_raw_pointer(constant.ty()) {
                    self.fallback.clone()
                } else {
                    LocalWrites::new()
                }
            }
            Operand::RuntimeChecks(_) => LocalWrites::new(),
        }
    }

    /// Locals the pointers carried by `local`'s value may point to, closed
    /// under the pointers stored in those locals. `None`: not understood.
    pub(crate) fn local_targets_deep(&self, local: Local) -> Option<LocalWrites> {
        let mut out = self.local_targets(local, &mut HashSet::new())?;
        let mut expanded: HashSet<Local> = HashSet::from([local]);
        loop {
            let pending: Vec<(Local, ChangedPlacesTree)> = out
                .iter()
                .filter(|(target, _)| !expanded.contains(*target))
                .map(|(target, write)| (*target, write.tree.clone()))
                .collect();
            if pending.is_empty() {
                return Some(out);
            }
            for (target, tree) in pending {
                expanded.insert(target);
                let target_ty = self.body.local_decls[target].ty;
                if matches!(tree, ChangedPlacesTree::Deref(_)) {
                    // Only the pointee of `target` is reached; pointers stored
                    // in that pointee are not tracked.
                    let pointee_carries = match target_ty.kind() {
                        TyKind::Ref(_, pointee, _) | TyKind::RawPtr(pointee, _) => {
                            self.may_carry(*pointee)
                        }
                        _ => true,
                    };
                    if pointee_carries {
                        return None;
                    }
                } else if self.may_carry(target_ty) {
                    let more = self.local_targets(target, &mut HashSet::new())?;
                    merge_writes(&mut out, more);
                }
            }
        }
    }

    /// Locals the pointers carried by `local`'s value may point to (one
    /// level). `None`: not understood.
    fn local_targets(&self, local: Local, visited: &mut HashSet<Local>) -> Option<LocalWrites> {
        let ty = self.body.local_decls[local].ty;
        let mut out = LocalWrites::new();
        if !self.may_carry(ty) || !visited.insert(local) {
            return Some(out);
        }
        if ty.is_box() {
            // A box owns its pointee: writes through it change `local`.
            add_write(&mut out, local, ChangedPlacesTree::Changed, false);
            if !ty.boxed_ty().is_some_and(|t| self.may_carry(t)) {
                return Some(out);
            }
        }
        if self.opaque.contains(&local) {
            return None;
        }
        let is_parameter = local.as_usize() >= 1 && local.as_usize() <= self.body.arg_count;
        if is_parameter {
            let tree = if ty.is_ref() || ty.is_raw_ptr() {
                pointee_tree()
            } else {
                ChangedPlacesTree::Changed
            };
            add_write(&mut out, local, tree, false);
        }
        let defs = self.defs.get(&local).cloned().unwrap_or_default();
        if defs.is_empty() && !is_parameter {
            return None;
        }
        for def in defs {
            let data = &self.body.basic_blocks[def.block];
            if def.statement_index < data.statements.len() {
                let StatementKind::Assign((_, rvalue)) = &data.statements[def.statement_index].kind
                else {
                    return None;
                };
                merge_writes(&mut out, self.rvalue_targets(rvalue, visited)?);
            } else {
                let TerminatorKind::Call { func, args, .. } = &data.terminator().kind else {
                    return None;
                };
                if contains_raw_pointer(ty) {
                    // A raw pointer a callee returns need not derive from its
                    // arguments.
                    return None;
                }
                merge_writes(&mut out, self.value_operand_targets(func, visited)?);
                for arg in args {
                    merge_writes(&mut out, self.value_operand_targets(&arg.node, visited)?);
                }
            }
        }
        Some(out)
    }

    fn rvalue_targets(
        &self,
        rvalue: &Rvalue<'tcx>,
        visited: &mut HashSet<Local>,
    ) -> Option<LocalWrites> {
        match rvalue {
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                self.place_address_targets(place, visited)
            }
            Rvalue::Use(operand, ..) => self.value_operand_targets(operand, visited),
            Rvalue::CopyForDeref(place) => {
                self.value_operand_targets(&Operand::Copy(*place), visited)
            }
            Rvalue::Cast(
                CastKind::PtrToPtr | CastKind::PointerCoercion(..) | CastKind::FnPtrToPtr,
                operand,
                _,
            ) => self.value_operand_targets(operand, visited),
            Rvalue::Aggregate(_, operands) => {
                let mut out = LocalWrites::new();
                for operand in operands {
                    merge_writes(&mut out, self.value_operand_targets(operand, visited)?);
                }
                Some(out)
            }
            _ => None,
        }
    }

    /// Targets of a borrow / raw borrow of `place`.
    fn place_address_targets(
        &self,
        place: &Place<'tcx>,
        visited: &mut HashSet<Local>,
    ) -> Option<LocalWrites> {
        let mut out = LocalWrites::new();
        match place
            .projection
            .iter()
            .position(|elem| matches!(elem, ProjectionElem::Deref))
        {
            None => {
                add_write(
                    &mut out,
                    place.local,
                    place_projection_to_tree(place.projection),
                    false,
                );
            }
            // `&mut (*p).f`: whatever `p` points to.
            Some(0)
                if place
                    .projection
                    .iter()
                    .skip(1)
                    .all(|elem| !matches!(elem, ProjectionElem::Deref)) =>
            {
                merge_writes(&mut out, self.local_targets(place.local, visited)?);
            }
            Some(_) => return None,
        }
        Some(out)
    }

    fn value_operand_targets(
        &self,
        operand: &Operand<'tcx>,
        visited: &mut HashSet<Local>,
    ) -> Option<LocalWrites> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                if place.projection.is_empty() {
                    self.local_targets(place.local, visited)
                } else if self.may_carry(place_ty_shallow(self.body, place)?) {
                    None
                } else {
                    Some(LocalWrites::new())
                }
            }
            Operand::Constant(constant) => {
                (!contains_raw_pointer(constant.ty())).then(LocalWrites::new)
            }
            Operand::RuntimeChecks(_) => Some(LocalWrites::new()),
        }
    }
}

/// The type of `place` when it can be computed from local declarations alone
/// (field projections of tuples / `Deref` of references and boxes).
fn place_ty_shallow<'tcx>(body: &Body<'tcx>, place: &Place<'tcx>) -> Option<Ty<'tcx>> {
    let mut ty = body.local_decls[place.local].ty;
    for elem in place.projection {
        ty = match elem {
            ProjectionElem::Field(_, field_ty) => field_ty,
            ProjectionElem::Deref => match ty.kind() {
                TyKind::Ref(_, pointee, _) | TyKind::RawPtr(pointee, _) => *pointee,
                _ => ty.boxed_ty()?,
            },
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => match ty.kind() {
                TyKind::Array(elem, _) | TyKind::Slice(elem) => *elem,
                _ => return None,
            },
            _ => return None,
        };
    }
    Some(ty)
}

fn contains_raw_pointer(ty: Ty<'_>) -> bool {
    ty.walk()
        .any(|arg| arg.as_type().is_some_and(|t| t.is_raw_ptr()))
}

struct BaseWrites<'s, 'a, 'tcx> {
    sites: &'s WriteSites<'a, 'tcx>,
    out: LocalWrites,
}

impl<'tcx> Visitor<'tcx> for BaseWrites<'_, '_, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, _location: Location) {
        let PlaceContext::MutatingUse(_) = context else {
            return;
        };
        let local_ty = self.sites.body.local_decls[place.local].ty;
        if has_deref(place) {
            // A store / mutable reborrow through a pointer.
            let is_box_store = local_ty.is_box()
                && place
                    .projection
                    .iter()
                    .filter(|elem| matches!(elem, ProjectionElem::Deref))
                    .count()
                    == 1;
            let tree = if is_box_store {
                ChangedPlacesTree::Changed
            } else {
                pointee_tree()
            };
            add_write(&mut self.out, place.local, tree, false);
            let targets = if is_box_store {
                Some(LocalWrites::new())
            } else {
                self.sites.local_targets_deep(place.local)
            };
            merge_writes(
                &mut self.out,
                targets.unwrap_or_else(|| self.sites.fallback.clone()),
            );
        } else {
            add_write(
                &mut self.out,
                place.local,
                place_projection_to_tree(place.projection),
                false,
            );
        }
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::RawPtr(RawPtrKind::Const, place) = rvalue {
            if !has_deref(place) {
                add_write(
                    &mut self.out,
                    place.local,
                    ChangedPlacesTree::Changed,
                    false,
                );
            }
        }
        self.super_rvalue(rvalue, location);
    }
}
