// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Raw-pointer-to-raw-pointer casts, read the way Creusot reads them
//! (`backend/program.rs::ptr_cast_kind`): a cast that keeps the pointer's
//! metadata is the identity, and a cast from a pointer that may carry
//! metadata to a thin one is the uninterpreted `thin`.
//!
//! A fat pointer is its address AND its metadata, so two slice pointers that
//! differ only in length are different, and their thin casts are equal.
//! Reading every cast as its operand therefore proves those thin casts
//! different. The MIR translation of `PtrToPtr` and a clause's
//! `e as *const T` both ask [`ptr_cast_kind`], in the typing environment of
//! the item that owns the body or the clause, so the clause and the body it
//! describes read one cast the same way. A MIR cast of neither kind is its
//! type pair's uninterpreted function; the clause refuses it.
//!
//! Unsizing a raw pointer (`PointerCoercion::Unsize`) ADDS metadata, so it is
//! not its operand either: `p as *const [u8; 4]` and `p as *const [u8; 8]`
//! unsized to `*const [u8]` differ. [`mir_raw_unsize_fn`] names one
//! uninterpreted function per (source pointee, target pointee) pair.
//!
//! Neither is left untranslated: an untranslated right-hand side is bound to
//! its source name, which a shadowing binding shares
//! (untranslated_local_shares_shadowed_symbol_in_postcondition.rs).

use std::hash::{Hash, Hasher};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Operand, Place, ProjectionElem},
    ty::{self, Ty, TyCtxt, TyKind, TypeVisitableExt, TypingEnv},
};
use trust_wp_core::formula::{
    internal::builtins::{PTR_PAIR_LOGIC_FN_PREFIX, PTR_THIN_LOGIC_FN},
    PureExpr,
};

/// How a raw-pointer cast relates its result to its operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PtrCastKind {
    /// The same pointer value: both thin, both carrying the same kind of
    /// metadata, or the same pointee.
    Id,
    /// The metadata is dropped: `thin(operand)`.
    Thin,
}

/// Whether `ty` is a type every pointer to which is fat.
fn definitely_unsized(ty: Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        TyKind::Str | TyKind::Slice(_) | TyKind::Dynamic(..)
    )
}

/// The kind of a cast from `*_ from` to `*_ to` in the item `owner`, or `None`
/// when it is neither: a pointee whose sizedness this environment does not
/// fix, or a sized pointee cast to a fat one. Creusot's rule reads the last as
/// the identity, which holds only for the casts MIR spells `PtrToPtr`.
pub(crate) fn ptr_cast_kind<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    from: Ty<'tcx>,
    to: Ty<'tcx>,
) -> Option<PtrCastKind> {
    let from = tcx.erase_and_anonymize_regions(from);
    let to = tcx.erase_and_anonymize_regions(to);
    if from == to {
        return Some(PtrCastKind::Id);
    }
    let typing_env = TypingEnv::post_analysis(tcx, owner);
    let sized_from = from.is_sized(tcx, typing_env);
    let sized_to = to.is_sized(tcx, typing_env);
    // A fat target keeps the operand's metadata only when the operand has
    // some: from a sized pointee it is an unsizing coercion, which ADDS a
    // length or a vtable. MIR spells that `PointerCoercion::Unsize`, never
    // `PtrToPtr`, but a clause's `p as *const [u8]` from `*const [u8; 4]`
    // reaches this function untyped.
    if (sized_from && sized_to) || (!sized_from && definitely_unsized(to)) {
        Some(PtrCastKind::Id)
    } else if sized_to {
        Some(PtrCastKind::Thin)
    } else {
        None
    }
}

/// `operand` read through a cast of `kind`.
pub(crate) fn apply_ptr_cast(kind: PtrCastKind, operand: PureExpr) -> PureExpr {
    match kind {
        PtrCastKind::Id => operand,
        PtrCastKind::Thin => PureExpr::LogicFnCall {
            name: PTR_THIN_LOGIC_FN.to_string(),
            args: vec![operand],
        },
    }
}

/// The pointee of a raw pointer type.
pub(crate) fn raw_pointee(ty: Ty<'_>) -> Option<Ty<'_>> {
    match ty.kind() {
        TyKind::RawPtr(pointee, _) => Some(*pointee),
        _ => None,
    }
}

/// The type of `place` in `body`, lifted into `tcx` and followed through
/// every projection MIR has.
fn place_ty<'a>(tcx: TyCtxt<'a>, body: &Body<'_>, place: &Place<'_>) -> Option<Ty<'a>> {
    let mut ty = tcx.lift(body.local_decls.get(place.local)?.ty);
    for elem in place.projection {
        ty = match elem {
            ProjectionElem::Deref => ty.builtin_deref(true)?,
            ProjectionElem::Field(_, field_ty) => tcx.lift(field_ty),
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                ty.builtin_index()?
            }
            // Only its element is read after a subslice (a raw pointer is
            // never an array), so its length is not computed.
            ProjectionElem::Subslice { .. } => Ty::new_slice(tcx, ty.builtin_index()?),
            ProjectionElem::Downcast(..) => ty,
            ProjectionElem::OpaqueCast(cast_ty) | ProjectionElem::UnwrapUnsafeBinder(cast_ty) => {
                tcx.lift(cast_ty)
            }
            // A phantom deref names an indeterminate place: no type.
            ProjectionElem::PhantomDeref => return None,
        };
    }
    Some(ty)
}

/// The type of `operand` in `body`, lifted into `tcx`.
fn operand_ty<'a>(tcx: TyCtxt<'a>, body: &Body<'_>, operand: &Operand<'_>) -> Option<Ty<'a>> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_ty(tcx, body, place),
        Operand::Constant(constant) => Some(tcx.lift(constant.const_.ty())),
        #[allow(unreachable_patterns)]
        _ => None,
    }
}

/// What a MIR raw-pointer cast denotes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MirPtrCast {
    /// The identity or `thin`, as [`ptr_cast_kind`] reads it.
    Kind(PtrCastKind),
    /// The uninterpreted function of this name, applied to the operand.
    PairFn(String),
}

impl MirPtrCast {
    /// `operand` read through this cast.
    pub(crate) fn apply(self, operand: PureExpr) -> PureExpr {
        match self {
            Self::Kind(kind) => apply_ptr_cast(kind, operand),
            Self::PairFn(name) => PureExpr::LogicFnCall {
                name,
                args: vec![operand],
            },
        }
    }
}

/// The uninterpreted function of the raw-pointer cast `tag` from `*_ from` to
/// `*_ to` in `owner`, named by a hash of the triple printed with full paths.
/// A pair that names a generic parameter prints the same in every body that
/// spells it while each body instantiates it itself, so its function is also
/// keyed by the body's owner.
fn pair_fn<'a>(tcx: TyCtxt<'a>, owner: DefId, tag: &str, from: Ty<'a>, to: Ty<'a>) -> String {
    let from = tcx.erase_and_anonymize_regions(from);
    let to = tcx.erase_and_anonymize_regions(to);
    let pair = ty::print::with_no_trimmed_paths!(format!("{tag}: {from} => {to}"));
    let key = if from.has_non_region_param() || to.has_non_region_param() {
        format!("{:?} :: {pair}", tcx.def_path_hash(owner))
    } else {
        pair
    };
    let mut hasher = std::hash::DefaultHasher::new();
    key.hash(&mut hasher);
    format!("{PTR_PAIR_LOGIC_FN_PREFIX}{:016x}", hasher.finish())
}

/// What the MIR `PtrToPtr` cast `operand as target` in `body` denotes: its
/// [`ptr_cast_kind`], or its pair's function where the kind is neither (a
/// cast between custom unsized pointees keeps metadata the classifier does
/// not read). `None` only without a compiler session, or when a pointee is
/// not a raw pointer's.
///
/// The translator this serves carries no `TyCtxt`; the compiler's thread-local
/// one is the context the body was built in, and the types are lifted into
/// it.
pub(crate) fn mir_ptr_cast<'tcx>(
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
    target: Ty<'tcx>,
) -> Option<MirPtrCast> {
    let owner = body.source.def_id();
    ty::tls::with_opt(|tcx| {
        let tcx = tcx?;
        let from = raw_pointee(operand_ty(tcx, body, operand)?)?;
        let to = raw_pointee(tcx.lift(target))?;
        Some(match ptr_cast_kind(tcx, owner, from, to) {
            Some(kind) => MirPtrCast::Kind(kind),
            None => MirPtrCast::PairFn(pair_fn(tcx, owner, "cast", from, to)),
        })
    })
}

/// The uninterpreted function the raw-pointer unsizing `operand as target`
/// is read as in `body`, one per (source pointee, target pointee) pair, or
/// `None` without a compiler session.
pub(crate) fn mir_raw_unsize_fn<'tcx>(
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
    target: Ty<'tcx>,
) -> Option<String> {
    let owner = body.source.def_id();
    ty::tls::with_opt(|tcx| {
        let tcx = tcx?;
        let from = raw_pointee(operand_ty(tcx, body, operand)?)?;
        let to = raw_pointee(tcx.lift(target))?;
        Some(pair_fn(tcx, owner, "unsize", from, to))
    })
}
