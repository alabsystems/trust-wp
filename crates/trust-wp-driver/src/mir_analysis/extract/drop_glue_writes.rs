// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Drop glue as a write through what the dropped value holds (D-140).
//!
//! D-4 gave a `Drop` no logical effect: ownership forbids a use of the dropped
//! value afterwards. The memory a `&mut` inside that value points to is not the
//! dropped value, and a user `Drop::drop` may write it:
//!
//! ```text
//! impl Drop for G<'_> { fn drop(&mut self) { *self.0 = 5 } }
//! let mut c = 0; { let _g = G(&mut c); } c      // 5, not 0
//! ```
//!
//! Every lane translated `c` after the scope as its value before the borrow.
//! A HAND-OFF is a program point where glue that may run such code may run:
//!
//! * a MIR `Drop` of a place whose glue may write ([`drop_glue_may_write`]);
//! * a call handed a value BY MOVE whose glue may write, or handed mutable
//!   access to one (`&mut Vec<G>`, `&Cell<Option<G>>`), unless the callee is
//!   a standard-library function known not to drop values of its type
//!   arguments (`mem::forget`, `Vec::push`, `Box::new`, ...): the callee owns
//!   the value and may drop it (`mem::drop(g)`, a generic `consume(g)`), or
//!   drops it in place (`v.clear()`, `v.truncate(0)`, `o.insert(g2)`). This
//!   is the list the panic lane's `call_drop_obligation` already reads.
//!
//! At a hand-off every local the handed value may reach by reference flow is
//! re-bound to a fresh symbol ([`locals_changed_by_handoff`]). The flow is
//! `write_aliases`' with calls also joining their borrow-holding arguments,
//! because `v.push(G(&mut c))` stores the borrow of `c` in `v` with no flow
//! into the call's result. That only removes premises. A `Drop` impl's own
//! contract is not read: D-140 havocs even where the impl's `ensures` would
//! say what it wrote.
//!
//! What "may write" means for a `Drop` impl of this crate is a syntactic scan
//! of its MIR ([`dtor_body_is_write_free`]): no store through a dereference,
//! no mutable or raw borrow of memory behind one, no call or drop handed a
//! value that can carry a write capability or reach an `UnsafeCell`. A body
//! that only reads through `self` passes; anything else, and every impl of
//! another crate except the standard library's, may write. A standard-library
//! destructor writes memory its value owns (the buffer of a `Vec`), whose
//! values are walked through the type arguments and fields as the panic lane
//! walks them; memory the value borrowed at the call that made it (a
//! `Drain`'s vector, a `RefMut`'s borrow flag, a `MutexGuard`'s lock), which
//! is either the referent of a `&mut` that call was handed, whose final value
//! the call lane gives from the callee's `^` or leaves fresh, or state no
//! specification here reads; or whatever a method of a type argument it uses
//! writes (`BufWriter<W>` flushes through `W::write`), which
//! [`std_dtor_may_call_user_code`] counts as a write.

use std::collections::HashSet;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        BasicBlock, Body, BorrowKind, Local, NonDivergingIntrinsic, Operand, ProjectionElem,
        Rvalue, StatementKind, Terminator, TerminatorKind,
    },
    ty::{Ty, TyCtxt, TyKind, TypingEnv},
};

/// Whether running the drop glue of a value of type `ty` may run code that
/// writes memory the value reaches.
pub(in crate::mir_analysis) fn drop_glue_may_write<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> bool {
    let mut visited = HashSet::new();
    glue_may_write(tcx, typing_env, ty, true, &mut visited, 0)
}

/// [`drop_glue_may_write`], except that a value of a type parameter is taken
/// to write nothing: the caller chose the type, so no borrow of this body's
/// locals is in it, and memory reachable from interior mutability is
/// re-bound at calls by its own lane. Used for what a callee may drop IN
/// PLACE, where a generic `&mut Vec<T>` is handed to nearly every call, and
/// for how far a `Drop`'s glue reaches ([`locals_changed_by_drop`]).
fn drop_glue_may_write_here<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> bool {
    let mut visited = HashSet::new();
    glue_may_write(tcx, typing_env, ty, false, &mut visited, 0)
}

fn glue_may_write<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    param_may_write: bool,
    visited: &mut HashSet<Ty<'tcx>>,
    depth: usize,
) -> bool {
    let ty = tcx
        .try_normalize_erasing_regions(
            typing_env,
            rustc_middle::ty::set_aliases_to_non_rigid(tcx, ty),
        )
        .unwrap_or(ty);
    if !ty.needs_drop(tcx, typing_env) || !visited.insert(ty) {
        return false;
    }
    if depth > 64 {
        return true;
    }
    let recurse = |t: Ty<'tcx>, visited: &mut HashSet<Ty<'tcx>>| {
        glue_may_write(tcx, typing_env, t, param_may_write, visited, depth + 1)
    };
    match ty.kind() {
        TyKind::Adt(adt, args) => {
            if is_std_crate(tcx, adt.did()) {
                return std_dtor_may_call_user_code(tcx, typing_env, *adt, *args, param_may_write)
                    || args.types().any(|arg| recurse(arg, visited))
                    || adt
                        .all_fields()
                        .any(|field| recurse(field.ty(tcx, *args).skip_norm_wip(), visited));
            }
            if let Some(dtor) = tcx.adt_destructor(adt.did()) {
                if !dtor.did.is_local() {
                    if !is_std_crate(tcx, dtor.did) {
                        return true;
                    }
                } else if !dtor_body_is_write_free(tcx, dtor.did) {
                    return true;
                }
            }
            adt.all_fields()
                .any(|field| recurse(field.ty(tcx, *args).skip_norm_wip(), visited))
        }
        TyKind::Tuple(tys) => tys.iter().any(|t| recurse(t, visited)),
        TyKind::Array(elem, _) | TyKind::Slice(elem) => recurse(*elem, visited),
        TyKind::Closure(_, args) => args
            .as_closure()
            .upvar_tys()
            .iter()
            .any(|t| recurse(t, visited)),
        // A coroutine's glue drops what it holds in the state it is dropped
        // in: its captures before it first runs, the locals it saved at a
        // suspension point, the value it was resumed with. `needs_drop`
        // answers `true` for every coroutine, so what it holds is read here.
        TyKind::Coroutine(def_id, args) => {
            let coroutine = args.as_coroutine();
            coroutine.upvar_tys().iter().any(|t| recurse(t, visited))
                || recurse(coroutine.resume_ty(), visited)
                || tcx.mir_coroutine_witnesses(*def_id).is_none_or(|layout| {
                    layout.field_tys.iter().any(|saved| {
                        let saved_ty = rustc_middle::ty::EarlyBinder::bind(tcx, saved.ty)
                            .instantiate(tcx, args)
                            .skip_norm_wip();
                        recurse(saved_ty, visited)
                    })
                })
        }
        TyKind::Param(_) => param_may_write,
        // An alias, a trait object: the glue is whatever the instantiation's
        // is, which this site cannot see.
        _ => true,
    }
}

/// The standard library, and `hashbrown`, whose tables are the private
/// fields of `std::collections::HashMap` and whose destructors are the same
/// kind as `Vec`'s.
fn is_std_crate(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    matches!(
        tcx.crate_name(def_id.krate).as_str(),
        "core" | "alloc" | "std" | "hashbrown"
    )
}

/// Whether the standard library's own `Drop` impl of `adt` may call a method
/// of a value of a type argument that can write: a type parameter of the impl
/// that is not `#[may_dangle]` (`tcx.destructor_constraints`) is one the
/// destructor may use, not only drop, and `BufWriter<W>` flushes through
/// `W::write`, `Splice<I>` drains `I::next`. Instantiated with a type that
/// holds write access or reaches interior mutability, that call may write
/// whatever the value reaches. A lifetime the destructor uses is memory the
/// value borrowed at the call that made it (A2 in docs/soundness.md).
fn std_dtor_may_call_user_code<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    adt: rustc_middle::ty::AdtDef<'tcx>,
    args: rustc_middle::ty::GenericArgs<'tcx>,
    param_may_write: bool,
) -> bool {
    tcx.destructor_constraints(adt)
        .into_iter()
        .any(|constraint| {
            let Some(param) = constraint.as_type() else {
                return false;
            };
            let TyKind::Param(param) = param.kind() else {
                return true;
            };
            let Some(ty) = args.get(param.index as usize).and_then(|arg| arg.as_type()) else {
                return true;
            };
            ty_holds_write_access(tcx, ty, param_may_write, &mut HashSet::new(), 0)
                || super::loop_body::ty_may_reach_interior_mutability_in(tcx, typing_env, ty)
        })
}

/// Whether the callee of a call may write, through an argument, memory the
/// caller can read afterwards: an argument holds write access
/// ([`ty_holds_write_access`], a type parameter included) or reaches interior
/// mutability. `mem::drop` and `mem::forget` write nothing but the glue the
/// hand-off question asks about. The loop-body and recursive-call walks,
/// which bind no callee's `^`, forget what such a call may have written.
pub(in crate::mir_analysis) fn call_may_write_through_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
) -> bool {
    if func.const_fn_def().is_some_and(|(callee, _)| {
        tcx.is_diagnostic_item(rustc_span::sym::mem_drop, callee)
            || tcx.is_diagnostic_item(rustc_span::sym::mem_forget, callee)
    }) {
        return false;
    }
    let typing_env = glue_typing_env(tcx, body);
    args.iter().any(|arg| {
        let ty = arg.node.ty(&body.local_decls, tcx);
        ty_holds_write_access(tcx, ty, true, &mut HashSet::new(), 0)
            || super::loop_body::ty_may_reach_interior_mutability_in(tcx, typing_env, ty)
    })
}

/// Whether a method called on a value of type `ty` could write memory outside
/// it: the value holds a `&mut` or a raw pointer, anywhere in its fields, or
/// something whose content is not visible here (a trait object, an alias, a
/// coroutine, a type parameter when `param_may_write`).
fn ty_holds_write_access<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    param_may_write: bool,
    visited: &mut HashSet<Ty<'tcx>>,
    depth: usize,
) -> bool {
    if !visited.insert(ty) {
        return false;
    }
    if depth > 64 {
        return true;
    }
    let recurse = |t: Ty<'tcx>, visited: &mut HashSet<Ty<'tcx>>| {
        ty_holds_write_access(tcx, t, param_may_write, visited, depth + 1)
    };
    match ty.kind() {
        TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut) | TyKind::RawPtr(..) => true,
        TyKind::Ref(_, inner, rustc_middle::ty::Mutability::Not) => recurse(*inner, visited),
        // A standard type's raw pointers point into memory it owns, whose
        // values are its type arguments; one that holds a borrow has a
        // lifetime argument.
        TyKind::Adt(adt, args) if is_std_crate(tcx, adt.did()) => {
            args.iter().any(|arg| arg.as_region().is_some())
                || args.types().any(|arg| recurse(arg, visited))
        }
        TyKind::Adt(adt, args) => adt
            .all_fields()
            .any(|field| recurse(field.ty(tcx, *args).skip_norm_wip(), visited)),
        TyKind::Tuple(tys) => tys.iter().any(|t| recurse(t, visited)),
        TyKind::Array(elem, _) | TyKind::Slice(elem) | TyKind::Pat(elem, _) => {
            recurse(*elem, visited)
        }
        TyKind::Closure(_, args) => args
            .as_closure()
            .upvar_tys()
            .iter()
            .any(|t| recurse(t, visited)),
        TyKind::Param(_) => param_may_write,
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

/// Whether a value of type `ty` holds, by value, one whose glue may write
/// ([`drop_glue_may_write_here`]), including one its own glue never drops: a
/// holder of `&mut ManuallyDrop<G>` or `&mut MaybeUninit<G>` drops the `G` in
/// place (`ManuallyDrop::drop`, `assume_init_drop`).
fn ty_holds_writing_glue<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    visited: &mut HashSet<Ty<'tcx>>,
    depth: usize,
) -> bool {
    if drop_glue_may_write_here(tcx, typing_env, ty) {
        return true;
    }
    if !visited.insert(ty) {
        return false;
    }
    if depth > 64 {
        return true;
    }
    let recurse = |t: Ty<'tcx>, visited: &mut HashSet<Ty<'tcx>>| {
        ty_holds_writing_glue(tcx, typing_env, t, visited, depth + 1)
    };
    match ty.kind() {
        TyKind::Adt(adt, args) if is_std_crate(tcx, adt.did()) => {
            args.types().any(|arg| recurse(arg, visited))
        }
        TyKind::Adt(adt, args) => adt
            .all_fields()
            .any(|field| recurse(field.ty(tcx, *args).skip_norm_wip(), visited)),
        TyKind::Tuple(tys) => tys.iter().any(|t| recurse(t, visited)),
        TyKind::Array(elem, _) | TyKind::Slice(elem) => recurse(*elem, visited),
        _ => false,
    }
}

/// Whether a value of type `ty` gives whoever holds it mutable access to a
/// value whose glue may write, so that a callee handed it can drop that value
/// in place: a `&mut` or raw pointer to one, a shared reference to one that
/// reaches interior mutability (`&RefCell<Option<G>>`), or an aggregate or
/// closure holding such an access. A type parameter lends nothing of this
/// body's ([`drop_glue_may_write_here`]).
fn ty_lends_writing_glue<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    visited: &mut HashSet<Ty<'tcx>>,
    depth: usize,
) -> bool {
    let ty = tcx
        .try_normalize_erasing_regions(
            typing_env,
            rustc_middle::ty::set_aliases_to_non_rigid(tcx, ty),
        )
        .unwrap_or(ty);
    if !visited.insert(ty) {
        return false;
    }
    if depth > 64 {
        return true;
    }
    let recurse = |t: Ty<'tcx>, visited: &mut HashSet<Ty<'tcx>>| {
        ty_lends_writing_glue(tcx, typing_env, t, visited, depth + 1)
    };
    match ty.kind() {
        TyKind::Ref(_, inner, rustc_middle::ty::Mutability::Mut) | TyKind::RawPtr(inner, _) => {
            ty_holds_writing_glue(tcx, typing_env, *inner, &mut HashSet::new(), 0)
                || recurse(*inner, visited)
        }
        // Through a shared reference only interior mutability writes, and it
        // writes everything behind it (`&RefCell<&mut Vec<G>>`).
        TyKind::Ref(_, inner, rustc_middle::ty::Mutability::Not) => {
            super::loop_body::ty_may_reach_interior_mutability_in(tcx, typing_env, *inner)
                && (ty_holds_writing_glue(tcx, typing_env, *inner, &mut HashSet::new(), 0)
                    || recurse(*inner, visited))
        }
        TyKind::Adt(adt, args) => {
            if is_std_crate(tcx, adt.did()) {
                args.types().any(|arg| recurse(arg, visited))
            } else {
                adt.all_fields()
                    .any(|field| recurse(field.ty(tcx, *args).skip_norm_wip(), visited))
            }
        }
        TyKind::Tuple(tys) => tys.iter().any(|t| recurse(t, visited)),
        TyKind::Array(elem, _) | TyKind::Slice(elem) => recurse(*elem, visited),
        TyKind::Closure(_, args) => args
            .as_closure()
            .upvar_tys()
            .iter()
            .any(|t| recurse(t, visited)),
        TyKind::Param(_) => false,
        // A trait object, an alias, a coroutine: what it holds is not visible
        // here.
        TyKind::Dynamic(..)
        | TyKind::Alias(..)
        | TyKind::Coroutine(..)
        | TyKind::CoroutineClosure(..)
        | TyKind::CoroutineWitness(..) => true,
        _ => false,
    }
}

/// Whether a local `Drop::drop` body provably writes no memory `self` reaches.
///
/// The scan is over the body's own MIR and is deliberately blunt: any store
/// through a dereference, any `&mut` or raw borrow of a place behind one, any
/// call or drop that is handed a value able to carry a write capability or to
/// reach an `UnsafeCell`, and any inline assembly answers `false`. A body the
/// driver cannot read answers `false`. One store is let through: into a field
/// of `*self` itself (`self.active = false`) whose type can carry no write
/// capability. That memory is the dying value's own, and what the glue drops
/// next from it can reach nothing the host holds.
pub(in crate::mir_analysis) fn dtor_body_is_write_free<'tcx>(
    tcx: TyCtxt<'tcx>,
    dtor: DefId,
) -> bool {
    let Ok(body) =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| tcx.optimized_mir(dtor)))
    else {
        return false;
    };
    let typing_env = body.typing_env(tcx);
    let behind_deref = |place: &rustc_middle::mir::Place<'_>| {
        place
            .projection
            .iter()
            .any(|elem| matches!(elem, ProjectionElem::Deref))
    };
    let carries = |ty: Ty<'tcx>| {
        crate::mir_analysis::loops::ty_may_carry_write_capability(ty, true)
            || super::loop_body::ty_may_reach_interior_mutability_in(tcx, typing_env, ty)
    };
    // `(*self).f.. = v` with no further dereference, of a type that carries
    // nothing: a write to the dying value's own memory.
    let own_plain_field = |place: &rustc_middle::mir::Place<'tcx>| {
        place.local == Local::from_u32(1)
            && matches!(place.projection.first(), Some(ProjectionElem::Deref))
            && place
                .projection
                .iter()
                .skip(1)
                .all(|elem| !matches!(elem, ProjectionElem::Deref))
            && !carries(place.ty(&body.local_decls, tcx).ty)
    };
    let operand_carries = |operand: &Operand<'tcx>| match operand {
        Operand::Copy(place) | Operand::Move(place) => carries(place.ty(&body.local_decls, tcx).ty),
        Operand::Constant(constant) => carries(constant.ty()),
        Operand::RuntimeChecks(_) => false,
    };
    for data in body.basic_blocks.iter() {
        for stmt in &data.statements {
            match &stmt.kind {
                StatementKind::Assign((place, rvalue)) => {
                    if behind_deref(place) && !own_plain_field(place) {
                        return false;
                    }
                    match rvalue {
                        Rvalue::Ref(_, BorrowKind::Mut { .. }, borrowed)
                            if behind_deref(borrowed) =>
                        {
                            return false;
                        }
                        Rvalue::RawPtr(..) => return false,
                        _ => {}
                    }
                }
                StatementKind::SetDiscriminant { place, .. }
                    if behind_deref(place) && !own_plain_field(place) =>
                {
                    return false;
                }
                StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(_)) => {
                    return false;
                }
                _ => {}
            }
        }
        match &data.terminator().kind {
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => {
                if operand_carries(func) || args.iter().any(|arg| operand_carries(&arg.node)) {
                    return false;
                }
            }
            TerminatorKind::Drop { place, .. } => {
                if carries(place.ty(&body.local_decls, tcx).ty) {
                    return false;
                }
            }
            TerminatorKind::InlineAsm { .. } | TerminatorKind::Yield { .. } => return false,
            _ => {}
        }
    }
    true
}

/// The environment a host's glue question is asked in. The glue that runs
/// is the glue of the value's actual type, so an opaque type is revealed to
/// its hidden type, as codegen reveals it: an `async fn`'s future is the
/// coroutine it builds, whose glue drops its captures and saved locals and
/// writes only when one of theirs may. The MIR this module reads is from
/// before drop elaboration, whose own environment keeps opaque types opaque
/// and so reads every future as glue that may write.
fn glue_typing_env<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> TypingEnv<'tcx> {
    TypingEnv::post_analysis(tcx, body.source.def_id())
}

/// The type of what `place` hands a callee, read through the unsizing
/// coercion that made it: `apply(&mut || c == 0)` into a `&mut dyn FnMut()`
/// lends the closure and nothing else, and the coercion erased only the type
/// the glue question reads. Read through only when that coercion is the
/// local's one definition and the local is never borrowed mutably, so no
/// later write can point it elsewhere.
fn type_before_unsizing<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: &rustc_middle::mir::Place<'tcx>,
) -> Ty<'tcx> {
    use rustc_middle::{mir::CastKind, ty::adjustment::PointerCoercion};
    let ty = place.ty(&body.local_decls, tcx).ty;
    if !place.projection.is_empty() {
        return ty;
    }
    let local = place.local;
    let mut source = None;
    for data in body.basic_blocks.iter() {
        for stmt in &data.statements {
            let StatementKind::Assign((dst, rvalue)) = &stmt.kind else {
                continue;
            };
            let borrows_local = match rvalue {
                Rvalue::Ref(_, BorrowKind::Mut { .. }, borrowed) | Rvalue::RawPtr(_, borrowed) => {
                    borrowed.local == local
                }
                _ => false,
            };
            if borrows_local {
                return ty;
            }
            if dst.local != local {
                continue;
            }
            match rvalue {
                Rvalue::Cast(
                    CastKind::PointerCoercion(PointerCoercion::Unsize, _),
                    Operand::Copy(from) | Operand::Move(from),
                    _,
                ) if dst.projection.is_empty() && source.is_none() => source = Some(*from),
                _ => return ty,
            }
        }
        if let TerminatorKind::Call { destination, .. } = &data.terminator().kind {
            if destination.local == local {
                return ty;
            }
        }
    }
    source.map_or(ty, |from| from.ty(&body.local_decls, tcx).ty)
}

/// The operands of a call through which the callee may run writing drop
/// glue: the body the call enters (for a trait method, the impl rustc resolves
/// it to) is not a standard-library function known never to drop a value of
/// its type arguments, and the operand either is handed BY MOVE with
/// glue [`drop_glue_may_write`] cannot clear, or lends mutable access to such
/// a value ([`ty_lends_writing_glue`]), which the callee may drop in place.
/// `mem::drop` runs its argument's glue and nothing else: it neither calls
/// nor resumes what it is handed, so only the glue is asked of it.
fn call_handoff_roots<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
) -> Vec<Local> {
    let typing_env = glue_typing_env(tcx, body);
    // Per operand: whether it hands over glue that may write, and whether it
    // lends access to a value whose glue may write.
    let candidates: Vec<(Local, bool, bool)> = args
        .iter()
        .filter_map(|arg| match &arg.node {
            Operand::Move(place) => Some((place, true)),
            Operand::Copy(place) => Some((place, false)),
            Operand::Constant(_) | Operand::RuntimeChecks(_) => None,
        })
        .map(|(place, by_move)| {
            let ty = place.ty(&body.local_decls, tcx).ty;
            let glue = by_move && drop_glue_may_write(tcx, typing_env, ty);
            let lends = ty_lends_writing_glue(
                tcx,
                typing_env,
                type_before_unsizing(tcx, body, place),
                &mut HashSet::new(),
                0,
            );
            (place.local, glue, lends)
        })
        .filter(|(_, glue, lends)| *glue || *lends)
        .collect();
    if candidates.is_empty() {
        return Vec::new();
    }
    let Some((callee, callee_args)) =
        super::call_resolve_util::resolve_obligation_callee(tcx, body, bb, func)
    else {
        return candidates.into_iter().map(|(local, ..)| local).collect();
    };
    if super::assertion::call_never_drops_type_args(tcx, body, callee, callee_args) {
        return Vec::new();
    }
    let runs_glue_only = tcx.is_diagnostic_item(rustc_span::sym::mem_drop, callee);
    candidates
        .into_iter()
        .filter(|(_, glue, _)| *glue || !runs_glue_only)
        .map(|(local, ..)| local)
        .collect()
}

/// The locals a `Drop` of `place` may change, or `None` when its glue cannot
/// write or reaches nothing. A whole local being dropped is left out: it is
/// uninitialized afterwards, and its glue writes through the borrows it holds,
/// never into itself, so a generic `T` dropped at its scope end re-binds
/// nothing but what interior mutability reaches.
///
/// Glue that may write only through a type parameter's value (`**x = v` with
/// `v: T`, a `(T, &mut u32)`) re-binds only what interior mutability reaches,
/// wherever the dropped place lives. The caller chose `T`, so a borrow in its
/// value outlives this body: it names no local of the body, and memory of the
/// caller it names is reachable from no live borrow of the body, since a
/// borrow lent into a `T` for a caller lifetime keeps the lender unusable for
/// the rest of the body.
pub(in crate::mir_analysis) fn locals_changed_by_drop<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: &rustc_middle::mir::Place<'tcx>,
) -> Option<HashSet<Local>> {
    let typing_env = glue_typing_env(tcx, body);
    let ty = place.ty(&body.local_decls, tcx).ty;
    if !drop_glue_may_write(tcx, typing_env, ty) {
        return None;
    }
    let roots: &[Local] = if drop_glue_may_write_here(tcx, typing_env, ty) {
        &[place.local]
    } else {
        &[]
    };
    let mut changed = reachable_by_reference_flow(tcx, body, roots);
    if place.projection.is_empty() {
        changed.remove(&place.local);
    }
    (!changed.is_empty()).then_some(changed)
}

/// The locals the call lane itself gives a post-call value at a call: its
/// destination, each argument, and each local an argument borrows mutably
/// (`_t = &mut v`, the `v` of `v.clear()`), whose post-call value is the
/// callee's `^` or fresh. Glue run inside the callee writes through borrows
/// the dropped values hold, which cannot point into the memory lent to them
/// (a value cannot hold a borrow of the place it lives in), so leaving these
/// out keeps what the callee's contract says of them.
fn bound_by_call_lane<'tcx>(
    body: &Body<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    destination: &rustc_middle::mir::Place<'tcx>,
) -> HashSet<Local> {
    let mut bound = HashSet::from([destination.local]);
    for arg in args {
        let (Operand::Copy(place) | Operand::Move(place)) = &arg.node else {
            continue;
        };
        bound.insert(place.local);
        if !place.projection.is_empty() {
            continue;
        }
        let mut definitions = body.basic_blocks.iter().flat_map(|data| {
            data.statements.iter().filter_map(|stmt| match &stmt.kind {
                StatementKind::Assign((dst, rvalue)) if dst.local == place.local => {
                    Some((dst.projection.is_empty(), rvalue))
                }
                _ => None,
            })
        });
        if let (Some((true, Rvalue::Ref(_, BorrowKind::Mut { .. }, borrowed))), None) =
            (definitions.next(), definitions.next())
        {
            bound.insert(borrowed.local);
        }
    }
    bound
}

/// The locals a call in block `bb` may change through the drop glue of what
/// it is handed by move, or `None` when it is handed nothing whose glue can
/// write. The call's own destination is left out: the call lane binds it.
pub(in crate::mir_analysis) fn locals_changed_by_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    destination: &rustc_middle::mir::Place<'tcx>,
) -> Option<HashSet<Local>> {
    let roots = call_handoff_roots(tcx, body, bb, func, args);
    if roots.is_empty() {
        return None;
    }
    let bound = bound_by_call_lane(body, args, destination);
    // A local that reaches interior mutability stays: glue may write it
    // through a shared borrow no flow records, whatever the callee's `^`
    // says of it.
    let changed: HashSet<Local> = reachable_by_reference_flow(tcx, body, &roots)
        .into_iter()
        .filter(|local| {
            !bound.contains(local)
                || super::loop_body::local_type_may_reach_interior_mutability(tcx, body, *local)
        })
        .collect();
    (!changed.is_empty()).then_some(changed)
}

/// The locals a hand-off at `terminator` (the terminator of `bb`) may change,
/// or `None` when it is not a hand-off.
pub(in crate::mir_analysis) fn locals_changed_by_handoff<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    terminator: &Terminator<'tcx>,
) -> Option<HashSet<Local>> {
    match &terminator.kind {
        TerminatorKind::Drop { place, .. } => locals_changed_by_drop(tcx, body, place),
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => locals_changed_by_call(tcx, body, bb, func, args, destination),
        _ => None,
    }
}

/// The locals whose REFERENTS a hand-off at `terminator` (the terminator of
/// `bb`) may write, for the lane that gives a parameter holding a `&mut` its
/// final value (`mut_borrow`), or `None` when it is not a hand-off.
///
/// That lane reads the final value of a borrow a by-value parameter holds
/// (`^g.0` of `g: G<'_>`) as what the body last stored through it, and the
/// glue stores after that store: at the `Drop` of `g` itself (its scope end,
/// or the scope end of a local it was moved into) and inside a callee handed
/// `g` by move (`mem::drop(g)`, a generic `consume(g)`). So the reach here
/// keeps the dropped local and every argument, which
/// [`locals_changed_by_handoff`] leaves out because no walk reads them again.
/// The lane itself leaves out the parameters whose final value a call takes
/// from the callee's `^`, which the callee's glue is inside of.
pub(in crate::mir_analysis) fn locals_reached_by_handoff<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    terminator: &Terminator<'tcx>,
) -> Option<HashSet<Local>> {
    let roots = match &terminator.kind {
        TerminatorKind::Drop { place, .. } => {
            let typing_env = glue_typing_env(tcx, body);
            let ty = place.ty(&body.local_decls, tcx).ty;
            if !drop_glue_may_write(tcx, typing_env, ty) {
                return None;
            }
            // As in `locals_changed_by_drop`: glue that writes only through a
            // type parameter's value reaches no borrow this body can name.
            if drop_glue_may_write_here(tcx, typing_env, ty) {
                vec![place.local]
            } else {
                Vec::new()
            }
        }
        TerminatorKind::Call { func, args, .. } => {
            let roots = call_handoff_roots(tcx, body, bb, func, args);
            if roots.is_empty() {
                return None;
            }
            roots
        }
        _ => return None,
    };
    let reached = reachable_by_reference_flow(tcx, body, &roots);
    (!reached.is_empty()).then_some(reached)
}

/// The argument locals a hand-off may re-bind before block `at` is entered:
/// the arguments in [`locals_changed_by_handoff`] of every `Drop` or call
/// whose terminator can run before `at`. That is the question the
/// substitution walk answers at each `Drop` and call it follows
/// (`locals_changed_by_drop`, `locals_changed_by_call`), asked of every
/// terminator on a path into `at` instead of the paths the walk takes, so it
/// names every parameter the walk re-binds and possibly more.
///
/// The `proof_assert` lane equates a parameter's name with its binding at
/// the assertion, and a `#[requires]` over that name describes its entry
/// value; once a hand-off re-binds the parameter to a fresh symbol, the entry
/// fact would become a premise about the value the glue wrote. A consumer
/// withdraws the entry facts naming these parameters, which can only lose a
/// proof.
///
/// `at = None` asks without a program point: every hand-off in the body.
pub(crate) fn params_rebound_by_handoffs<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    at: Option<BasicBlock>,
) -> HashSet<Local> {
    let runs_before = at.map(|at| blocks_that_may_run_before(body, at));
    let mut rebound = HashSet::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if runs_before
            .as_ref()
            .is_some_and(|before| !before.contains(&bb))
        {
            continue;
        }
        let Some(terminator) = &data.terminator else {
            continue;
        };
        if let Some(changed) = locals_changed_by_handoff(tcx, body, bb, terminator) {
            rebound.extend(
                changed
                    .into_iter()
                    .filter(|local| (1..=body.arg_count).contains(&local.as_usize())),
            );
        }
    }
    rebound
}

/// The blocks whose terminator can run before `at` is entered: every block
/// from which a predecessor of `at` is reachable. `at` itself is among them
/// only when it lies on a cycle, since its own terminator runs after its
/// statements.
fn blocks_that_may_run_before(body: &Body<'_>, at: BasicBlock) -> HashSet<BasicBlock> {
    let predecessors = body.basic_blocks.predecessors();
    let mut seen = HashSet::new();
    let mut stack: Vec<BasicBlock> = predecessors[at].to_vec();
    while let Some(bb) = stack.pop() {
        if seen.insert(bb) {
            stack.extend(predecessors[bb].iter().copied());
        }
    }
    seen
}

/// The locals changed by every CALL hand-off whose return edge enters `bb`.
pub(in crate::mir_analysis) fn locals_changed_by_call_handoff_into<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
) -> HashSet<Local> {
    let mut changed = HashSet::new();
    for pred in &body.basic_blocks.predecessors()[bb] {
        let terminator = body.basic_blocks[*pred].terminator();
        if matches!(&terminator.kind, TerminatorKind::Call { target: Some(t), .. } if *t == bb) {
            if let Some(locals) = locals_changed_by_handoff(tcx, body, *pred, terminator) {
                changed.extend(locals);
            }
        }
    }
    changed
}

/// `roots`, their reference-flow component, and every local whose type can
/// reach interior mutability (which no flow bounds):
/// `write_aliases::locals_drop_glue_may_change`.
///
/// A type parameter is not taken to hold a borrow there, and need not be: it
/// is fixed by the caller, so it cannot name the lifetime of a borrow of one
/// of this body's locals. A value that can is typed with a region, a closure,
/// a trait object or an alias, and each of those joins the flow.
fn reachable_by_reference_flow<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    roots: &[Local],
) -> HashSet<Local> {
    super::write_aliases::locals_drop_glue_may_change(tcx, body, roots)
}
