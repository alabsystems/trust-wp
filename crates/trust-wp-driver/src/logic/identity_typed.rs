// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type-directed resolution of colliding logic-function calls.
//!
//! A receiver-style call `x.m(..)` (or `Tr::m(x, ..)`, `T::k()`) denotes the
//! definition Rust selects for the TYPE of the receiver / qualifying type.
//! That type is known only here, in the driver:
//!
//! - a concrete type selects the one local impl whose self type is that type
//!   (anything else is refused);
//! - a generic parameter `T` of the function being verified selects the trait
//!   DECLARATION of the one bound trait of `T` that declares the method — the
//!   abstract method at an unknown `Self`. That symbol is only meaningful in
//!   the verification of that very function: instantiated with two different
//!   types it would equate their impls whenever their values share a solver
//!   sort. So a callee contract never carries it: callee clause TEXT spells a
//!   generic receiver with a generic MARKER (callee, generic parameter index),
//!   re-resolved at each call site against the call's generic arguments.
//!   Markers that reach the encoder unresolved are refused there.

use std::{cell::RefCell, collections::HashMap};

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{GenericArgs, Ty, TyCtxt, TyKind, TypeVisitableExt};
use trust_wp_core::{
    formula::{MatchArm, Pattern, PureExpr},
    logic::identity::{
        dispatches_on_receiver, logic_fn_identity_registry, LogicFnFamilyMember, LogicFnOwnerKind,
        LOGIC_FN_GENERIC_PREFIX,
    },
};
use trust_wp_driver::StdSpec;

use super::{
    identity::{member_def_id, refused_call_marker, GenericTypeParam},
    spec_calls::{CallForm, ClauseRef, SpecCalls},
};

/// Outcome of resolving a call on a Rust type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TypedOutcome {
    /// The unique id of the one definition Rust selects.
    Id(String),
    /// The type is the generic parameter with this index.
    Generic(u32),
    /// The type is the associated type (this `DefId`) of a generic parameter,
    /// e.g. `<Self as Trait>::Assoc`.
    Projection(DefId),
    /// No single definition.
    Refused,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct GenericMarker {
    callee: DefId,
    param_index: u32,
    short: String,
    arity: usize,
    by_receiver: bool,
    /// The one bound trait of the parameter that declares `short`: Rust
    /// reads the call as that trait's method, so a call site selects among
    /// that trait's definitions only.
    trait_id: DefId,
    /// The trait method rustc resolved the call to in the callee, at the
    /// callee's generic parameter: what the call names at every
    /// instantiation of it.
    decl: DefId,
}

thread_local! {
    static GENERIC_MARKERS: RefCell<(Vec<GenericMarker>, HashMap<GenericMarker, usize>)> =
        RefCell::new((Vec::new(), HashMap::new()));
}

fn generic_marker_name(marker: GenericMarker) -> String {
    GENERIC_MARKERS.with(|cell| {
        let mut guard = cell.borrow_mut();
        let (list, index) = &mut *guard;
        let next = list.len();
        let slot = *index.entry(marker.clone()).or_insert_with(|| {
            list.push(marker);
            next
        });
        format!("{LOGIC_FN_GENERIC_PREFIX}{slot}")
    })
}

fn generic_marker(slot: usize) -> Option<GenericMarker> {
    GENERIC_MARKERS.with(|cell| cell.borrow().0.get(slot).cloned())
}

/// Resolve a call to the colliding short name `family` with `arity` arguments
/// on the Rust type `ty` (the receiver's type when `by_receiver`, else the
/// qualifying `Self` type). `scope` is the item the call is written in, when
/// known: a trait declared in its module is certainly in scope there.
pub(crate) fn resolve_family_on_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    family: &[LogicFnFamilyMember],
    arity: usize,
    ty: Ty<'tcx>,
    by_receiver: bool,
    scope: Option<DefId>,
) -> TypedOutcome {
    let members: Vec<&LogicFnFamilyMember> = family
        .iter()
        .filter(|member| member.arity == arity)
        .collect();
    if members.is_empty() || (by_receiver && !members.iter().all(|m| m.receiver_is_self)) {
        return TypedOutcome::Refused;
    }
    let levels = peel_transparent_boxes(tcx, tcx.erase_and_anonymize_regions(ty.peel_refs()));
    let Some((&innermost, outer)) = levels.split_last() else {
        return TypedOutcome::Refused;
    };
    // Rust's method probe tries the receiver, then each type an autoderef of
    // a box reaches, and selects at the FIRST level where a method of that
    // name is in scope. Which traits are in scope where the call is written is
    // not known here, so a candidate at one level decides the call only where
    // no other level has one, or where Rust cannot pass it by (below).
    let mut found: Vec<(Ty<'tcx>, LevelCandidates<'_>)> = Vec::new();
    for &level in outer {
        let candidates = candidates_at(tcx, &members, level);
        if !candidates.hits.is_empty() {
            found.push((level, candidates));
        }
    }
    let special = innermost_special(innermost);
    if let Some(special) = special {
        return if found.is_empty() {
            special
        } else {
            TypedOutcome::Refused
        };
    }
    let inner = candidates_at(tcx, &members, innermost);
    if !inner.hits.is_empty() {
        found.push((innermost, inner));
    }
    match found.as_slice() {
        [] if !innermost.has_non_region_param() => inherited_default(tcx, &members, innermost),
        [] => TypedOutcome::Refused,
        [(level, only)] => only.answer(tcx, *level),
        [(level, first), deeper @ ..] => {
            // The first level's one certain candidate is what Rust selects
            // when its trait is in scope, and then the deeper levels are never
            // reached. That is settled where the trait is declared in the
            // module the call is written in, or where every deeper candidate
            // belongs to the same trait (in scope together or not at all).
            let passed_by = match first.hits.as_slice() {
                [(_, def_id)] if !first.uncertain => {
                    trait_of_member(tcx, *def_id).is_some_and(|trait_id| {
                        trait_certainly_in_scope(tcx, trait_id, scope)
                            || deeper.iter().all(|(_, candidates)| {
                                candidates.hits.iter().all(|(_, deeper_id)| {
                                    trait_of_member(tcx, *deeper_id) == Some(trait_id)
                                })
                            })
                    })
                }
                _ => false,
            };
            if passed_by {
                first.answer(tcx, *level)
            } else {
                TypedOutcome::Refused
            }
        }
    }
}

/// The candidates of one autoderef level of a receiver.
struct LevelCandidates<'a> {
    hits: Vec<(&'a str, DefId)>,
    /// Some hit may or may not be what Rust selects there: no answer.
    uncertain: bool,
    open: bool,
}

impl LevelCandidates<'_> {
    fn answer<'tcx>(&self, tcx: TyCtxt<'tcx>, level: Ty<'tcx>) -> TypedOutcome {
        match self.hits.as_slice() {
            [(id, _)] if super::identity::is_ambiguous_id(id) => TypedOutcome::Refused,
            [(id, def_id)]
                if !self.uncertain && (!self.open || impl_self_covers_all(tcx, *def_id, level)) =>
            {
                TypedOutcome::Id((*id).to_string())
            }
            _ => TypedOutcome::Refused,
        }
    }
}

/// The outcome a generic, projected or higher-ranked innermost receiver
/// decides without looking at candidates.
fn innermost_special(ty: Ty<'_>) -> Option<TypedOutcome> {
    if let TyKind::Param(param) = ty.kind() {
        return Some(TypedOutcome::Generic(param.index));
    }
    if let TyKind::Alias(_, alias) = ty.kind() {
        if let rustc_middle::ty::AliasTyKind::Projection { def_id } = alias.kind {
            let self_is_param = alias
                .args
                .iter()
                .find_map(|arg| arg.as_type())
                .is_some_and(|self_ty| matches!(self_ty.kind(), TyKind::Param(_)));
            if self_is_param {
                return Some(TypedOutcome::Projection(def_id));
            }
        }
    }
    ty.has_escaping_bound_vars()
        .then_some(TypedOutcome::Refused)
}

/// The family members that may be what Rust selects at the reference-peeled
/// receiver type `ty`.
fn candidates_at<'tcx, 'a>(
    tcx: TyCtxt<'tcx>,
    members: &[&'a LogicFnFamilyMember],
    ty: Ty<'tcx>,
) -> LevelCandidates<'a> {
    // A receiver type carrying type parameters (`List<T>` inside
    // `impl<T> List<T>`) is still resolvable: an impl whose self type is the
    // SAME ADT with a distinct parameter for every argument applies to every
    // instantiation of it, and no other definition of the family can apply to
    // any of them. `may_apply` OVER-approximates (a second candidate refuses),
    // `covers_all` UNDER-approximates (the one candidate must answer for every
    // instantiation), so an uncertain receiver is refused, never guessed.
    //
    // A CLOSED receiver asks each impl whether it applies at `ty`
    // (`applies_at_closed`): an impl whose self type is not `ty` itself (a
    // blanket `impl<T: B> Tr for T`, an impl on `&S`) may still be the one
    // Rust selects, and an impl the question cannot settle is a candidate
    // that refuses, never one that is skipped.
    let open = ty.has_non_region_param();
    let mut uncertain = false;
    let mut hits: Vec<(&'a str, DefId)> = Vec::new();
    for (member, def_id) in members
        .iter()
        .filter(|member| {
            matches!(
                member.kind,
                LogicFnOwnerKind::TraitImpl | LogicFnOwnerKind::Inherent
            )
        })
        .filter_map(|member| member_def_id(&member.id).map(|def_id| (*member, def_id)))
    {
        let applies = if open {
            if impl_self_may_apply(tcx, def_id, ty) {
                Applies::Yes
            } else {
                Applies::No
            }
        } else {
            applies_at_closed(tcx, def_id, ty)
        };
        match applies {
            Applies::Yes => hits.push((member.id.as_str(), def_id)),
            Applies::Maybe => {
                uncertain = true;
                hits.push((member.id.as_str(), def_id));
            }
            Applies::No => {}
        }
    }
    // A trait method's DEFAULT body runs at `ty` where the impl Rust selects
    // there does not define the method, and that impl then has no member in
    // this family: a lookup over impl members alone binds the one it does
    // see -- another trait's method at `ty`, whose trait need not be in scope
    // where the call is written -- instead of the default Rust runs. So a
    // default that may run at `ty` is a candidate beside the impl members,
    // and the answer only where it is the one candidate and
    // `inherited_default` would read it.
    for (member, def_id) in members
        .iter()
        .filter(|member| member.kind == LogicFnOwnerKind::TraitDecl)
        .filter_map(|member| member_def_id(&member.id).map(|def_id| (*member, def_id)))
    {
        match default_runs_at(tcx, def_id, ty, open) {
            Applies::No => {}
            Applies::Yes
                if inherited_default(tcx, &[member], ty) == TypedOutcome::Id(member.id.clone()) =>
            {
                hits.push((member.id.as_str(), def_id));
            }
            Applies::Yes | Applies::Maybe => {
                uncertain = true;
                hits.push((member.id.as_str(), def_id));
            }
        }
    }
    LevelCandidates {
        hits,
        uncertain,
        open,
    }
}

/// The trait a family member belongs to: its trait for a declaration or a
/// trait impl, none for an inherent method or a free function.
fn trait_of_member(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
    let parent = tcx.parent(def_id);
    match tcx.def_kind(parent) {
        DefKind::Trait => Some(parent),
        DefKind::Impl { of_trait: true } => tcx.impl_opt_trait_id(parent),
        _ => None,
    }
}

/// Whether the trait `trait_id` is in scope wherever `scope` is written: it
/// is declared directly in the module that encloses `scope`. Rust's
/// traits-in-scope for a method call hold every trait of the nearest
/// enclosing module, whatever blocks lie between. Anything else -- an import,
/// the prelude, a trait of another module -- is not known here, and counts as
/// possibly out of scope.
fn trait_certainly_in_scope(tcx: TyCtxt<'_>, trait_id: DefId, scope: Option<DefId>) -> bool {
    let Some(scope) = scope.and_then(DefId::as_local) else {
        return false;
    };
    trait_id.is_local()
        && tcx.opt_parent(trait_id) == Some(tcx.parent_module_from_def_id(scope).to_def_id())
}

/// Whether the DEFAULT body of the trait method `decl` may be what runs at
/// the reference-peeled receiver type `ty`: the impl Rust selects there does
/// not define the method.
///
/// At a closed receiver of a trait whose one parameter is `Self`, rustc's
/// selection is asked at `ty` and at `&ty` / `&mut ty`, as
/// `applies_at_closed` asks it of an impl: the default runs (`Yes`) where the
/// impl selected at `ty` itself lacks the method and no other level selects
/// one that does; selected only at a reference, or at a selection rustc does
/// not settle, it is a candidate that refuses (`Maybe`). Anywhere else, every
/// impl of the trait that lacks the method and may apply at `ty` makes the
/// default a candidate that refuses. A method with no default body never
/// runs one (`No`): every impl defines it and is a member of the family.
fn default_runs_at<'tcx>(tcx: TyCtxt<'tcx>, decl: DefId, ty: Ty<'tcx>, open: bool) -> Applies {
    let trait_id = tcx.parent(decl);
    if tcx.def_kind(trait_id) != DefKind::Trait || !tcx.defaultness(decl).has_value() {
        return Applies::No;
    }
    let lacks = |impl_id: DefId| !tcx.impl_item_implementor_ids(impl_id).contains_key(&decl);
    if open
        || tcx.generics_of(trait_id).count() != 1
        || ty.has_aliases()
        || ty.has_escaping_bound_vars()
    {
        let may_run = tcx
            .all_impls(trait_id)
            .any(|impl_id| lacks(impl_id) && impl_may_apply(tcx, impl_id, ty));
        return if may_run { Applies::Maybe } else { Applies::No };
    }
    let erased = tcx.lifetimes.re_erased;
    let at = |receiver: Ty<'tcx>| -> Applies {
        let trait_ref = rustc_middle::ty::TraitRef::new(tcx, trait_id, [receiver]);
        match tcx.codegen_select_candidate(
            rustc_middle::ty::TypingEnv::fully_monomorphized().as_query_input(trait_ref),
        ) {
            Ok(rustc_middle::traits::ImplSource::UserDefined(data)) => {
                if lacks(data.impl_def_id) {
                    Applies::Yes
                } else {
                    Applies::No
                }
            }
            Err(rustc_middle::traits::CodegenObligationError::Unimplemented) => Applies::No,
            Ok(_) | Err(_) => Applies::Maybe,
        }
    };
    let by_value = at(ty);
    let by_ref = [
        at(Ty::new_imm_ref(tcx, erased, ty)),
        at(Ty::new_mut_ref(tcx, erased, ty)),
    ];
    if by_value == Applies::Maybe || by_ref.iter().any(|level| *level != Applies::No) {
        Applies::Maybe
    } else {
        by_value
    }
}

/// Whether one impl applies at a closed receiver type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Applies {
    Yes,
    /// The impl may be the one Rust selects, but that is not settled here:
    /// it counts as a candidate and can never be the answer.
    Maybe,
    No,
}

/// Whether the impl containing `def_id` applies at the CLOSED, reference-
/// peeled receiver type `ty`.
///
/// `impl_self_matches` compares self types, so on its own it never sees an
/// impl whose self type is not `ty`: a blanket `impl<T: Marker> Tr for T`, an
/// impl on `&S`, or an ADT impl whose parameters are repeated or bounded.
/// Such an impl is exactly the one Rust selects when it is the only one in
/// scope, and a lookup blind to it binds the one it does see -- another
/// trait's method, or an inherent one -- which is a wrong definition, not a
/// refusal. So a trait impl with a generic self type is asked of rustc's own
/// selection, at `ty` and at `&ty` / `&mut ty`: the receiver's references
/// were peeled before this point, so an impl selected at any of them may be
/// the one the call names. It applies when selection picks it at one of them
/// and settles every one. An impl on a reference to a closed `ty`, and a
/// selection rustc does not settle, are candidates that refuse (`Maybe`). A
/// trait with parameters besides `Self` has no trait reference to select
/// with here, so its impl is read by self type as an inherent one is: it
/// applies when it covers every instantiation of `ty`'s ADT, and otherwise
/// (a blanket impl among them) it is a candidate that refuses.
fn applies_at_closed<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, ty: Ty<'tcx>) -> Applies {
    let impl_id = tcx.parent(def_id);
    if !matches!(tcx.def_kind(impl_id), DefKind::Impl { .. }) {
        return Applies::No;
    }
    let self_ty = tcx
        .erase_and_anonymize_regions(tcx.type_of(impl_id).instantiate_identity().skip_norm_wip());
    let trait_id = tcx.impl_opt_trait_id(impl_id);
    if !self_ty.has_non_region_param() {
        return if self_ty == ty {
            Applies::Yes
        } else if self_ty.peel_refs() == ty {
            Applies::Maybe
        } else {
            Applies::No
        };
    }
    let may_apply = || {
        if impl_self_may_apply(tcx, def_id, ty) {
            Applies::Maybe
        } else {
            Applies::No
        }
    };
    // A generic inherent impl, or a trait impl selection cannot be asked of
    // here: one covering every instantiation of its ADT applies (the
    // self-type reading every other candidate is now checked against); one
    // with a repeated or bounded parameter may.
    let by_self_type = || {
        if impl_self_matches(tcx, def_id, ty) {
            Applies::Yes
        } else {
            may_apply()
        }
    };
    let Some(trait_id) = trait_id else {
        return by_self_type();
    };
    if tcx.generics_of(trait_id).count() != 1 || ty.has_aliases() || ty.has_escaping_bound_vars() {
        return by_self_type();
    }
    let erased = tcx.lifetimes.re_erased;
    let at = |receiver: Ty<'tcx>| -> Applies {
        let trait_ref = rustc_middle::ty::TraitRef::new(tcx, trait_id, [receiver]);
        match tcx.codegen_select_candidate(
            rustc_middle::ty::TypingEnv::fully_monomorphized().as_query_input(trait_ref),
        ) {
            Ok(rustc_middle::traits::ImplSource::UserDefined(data)) => {
                if data.impl_def_id == impl_id {
                    Applies::Yes
                } else {
                    Applies::No
                }
            }
            Err(rustc_middle::traits::CodegenObligationError::Unimplemented) => Applies::No,
            Ok(_) | Err(_) => Applies::Maybe,
        }
    };
    let levels = [
        at(ty),
        at(Ty::new_imm_ref(tcx, erased, ty)),
        at(Ty::new_mut_ref(tcx, erased, ty)),
    ];
    if levels.contains(&Applies::Maybe) {
        Applies::Maybe
    } else if levels.contains(&Applies::Yes) {
        Applies::Yes
    } else {
        Applies::No
    }
}

/// The levels a receiver-style call's autoderef reaches through `Box`
/// wrappers: the reference-peeled receiver type first, then each box's
/// reference-peeled pointee.
///
/// Every level is kept, because Rust's method probe selects at the first one
/// where a method of that name is IN SCOPE: a member defined on the box, or a
/// blanket impl that applies to it, is what the call names only where its
/// trait is in scope, and otherwise the probe passes it by and derefs. The
/// encoder gives `Box<T>` exactly `T`'s solver sort
/// (`mir_analysis::translate::ty_sort`), so a definition selected at a deeper
/// level reads the same value.
fn peel_transparent_boxes<'tcx>(tcx: TyCtxt<'tcx>, mut ty: Ty<'tcx>) -> Vec<Ty<'tcx>> {
    let mut levels = vec![ty];
    // Bounded: `Box<Box<..>>` nests finitely, the cap only guards against a
    // pathological type.
    for _ in 0..16 {
        let TyKind::Adt(adt, args) = ty.kind() else {
            break;
        };
        if !adt.is_box() {
            break;
        }
        let Some(inner) = args.types().next() else {
            break;
        };
        ty = tcx.erase_and_anonymize_regions(inner.peel_refs());
        levels.push(ty);
    }
    levels
}

/// Whether the impl containing `def_id` can apply to SOME instantiation of the
/// open type `ty`. Over-approximate on purpose: a `true` it did not have to
/// give only costs a refusal (two candidates), never a wrong pick.
fn impl_self_may_apply<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, ty: Ty<'tcx>) -> bool {
    let impl_id = tcx.parent(def_id);
    matches!(tcx.def_kind(impl_id), DefKind::Impl { .. }) && impl_may_apply(tcx, impl_id, ty)
}

/// `impl_self_may_apply` asked of the impl `impl_id` itself.
fn impl_may_apply<'tcx>(tcx: TyCtxt<'tcx>, impl_id: DefId, ty: Ty<'tcx>) -> bool {
    let self_ty = tcx
        .erase_and_anonymize_regions(tcx.type_of(impl_id).instantiate_identity().skip_norm_wip());
    match (self_ty.peel_refs().kind(), ty.peel_refs().kind()) {
        // Two different ADTs never unify; nothing can instantiate one into the
        // other.
        (TyKind::Adt(impl_adt, _), TyKind::Adt(adt, _)) => impl_adt.did() == adt.did(),
        // An ADT against a non-ADT, neither of them a parameter, cannot unify.
        (TyKind::Adt(..), other) | (other, TyKind::Adt(..)) => {
            matches!(other, TyKind::Param(_) | TyKind::Alias(..))
        }
        _ => true,
    }
}

/// Whether the impl containing `def_id` applies to EVERY instantiation of the
/// open type `ty`: the same ADT, with the impl covering all of its arguments
/// (a distinct type parameter in every slot and no const arguments).
fn impl_self_covers_all<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, ty: Ty<'tcx>) -> bool {
    let impl_id = tcx.parent(def_id);
    let self_ty = tcx
        .erase_and_anonymize_regions(tcx.type_of(impl_id).instantiate_identity().skip_norm_wip());
    match (self_ty.kind(), ty.kind()) {
        (TyKind::Adt(impl_adt, impl_args), TyKind::Adt(adt, _)) if impl_adt.did() == adt.did() => {
            let mut seen = std::collections::HashSet::new();
            impl_args.consts().next().is_none()
                && impl_args
                    .types()
                    .all(|arg| matches!(arg.kind(), TyKind::Param(p) if seen.insert(p.index)))
        }
        _ => false,
    }
}

/// A concrete type whose impl does not override a trait method with a
/// visible default body: Rust's `Instance` resolution at that type selects
/// the TRAIT ITEM itself, so the callee is exactly the default body. Only a
/// default body that calls nothing is used (a call inside it would reach a
/// declaration symbol shared by every instantiation).
pub(crate) fn inherited_default<'tcx>(
    tcx: TyCtxt<'tcx>,
    members: &[&LogicFnFamilyMember],
    ty: Ty<'tcx>,
) -> TypedOutcome {
    let hits: Vec<&str> = members
        .iter()
        .filter(|member| {
            member.kind == LogicFnOwnerKind::TraitDecl
                && member.decl_has_visible_body
                && super::identity::is_self_contained_default(&member.id)
        })
        .filter(|member| {
            member_def_id(&member.id).is_some_and(|def_id| {
                let trait_id = tcx.parent(def_id);
                tcx.def_kind(trait_id) == DefKind::Trait
                    && tcx.generics_of(trait_id).count() == 1
                    && tcx.generics_of(def_id).own_params.is_empty()
                    && rustc_middle::ty::Instance::try_resolve(
                        tcx,
                        rustc_middle::ty::TypingEnv::fully_monomorphized(),
                        def_id,
                        tcx.mk_args(&[ty.into()]),
                    )
                    .ok()
                    .flatten()
                    .is_some_and(|instance| {
                        instance.def == rustc_middle::ty::InstanceKind::Item(def_id)
                    })
            })
        })
        .map(|member| member.id.as_str())
        .collect();
    match hits.as_slice() {
        [id] if !super::identity::is_ambiguous_id(id) => TypedOutcome::Id((*id).to_string()),
        _ => TypedOutcome::Refused,
    }
}

/// Whether the impl containing `def_id` applies to the concrete type `ty`:
/// its self type is exactly `ty`, or it is the same ADT with distinct type
/// parameters for every argument (an impl covering every instantiation).
fn impl_self_matches<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, ty: Ty<'tcx>) -> bool {
    let impl_id = tcx.parent(def_id);
    if !matches!(tcx.def_kind(impl_id), DefKind::Impl { .. }) {
        return false;
    }
    let self_ty = tcx
        .erase_and_anonymize_regions(tcx.type_of(impl_id).instantiate_identity().skip_norm_wip());
    if !self_ty.has_non_region_param() {
        return self_ty == ty;
    }
    match (self_ty.kind(), ty.kind()) {
        (TyKind::Adt(impl_adt, impl_args), TyKind::Adt(adt, _)) if impl_adt.did() == adt.did() => {
            let mut seen = std::collections::HashSet::new();
            impl_args.consts().next().is_none()
                && impl_args
                    .types()
                    .all(|arg| matches!(arg.kind(), TyKind::Param(p) if seen.insert(p.index)))
        }
        _ => false,
    }
}

/// The trait declaration a call on the generic parameter `param_index` of
/// `owner` denotes: the one bound trait of that parameter (direct bounds of
/// `owner` and its parents) declaring an arity-matching method of the family
/// without a visible default body.
pub(crate) fn decl_for_generic_param(
    tcx: TyCtxt<'_>,
    owner: DefId,
    family: &[LogicFnFamilyMember],
    arity: usize,
    param_index: u32,
) -> Option<String> {
    let mut bound_traits = std::collections::HashSet::new();
    let mut current = Some(owner);
    while let Some(did) = current {
        let predicates = tcx.clauses_of(did);
        for (clause, _) in predicates.clauses {
            let Some(trait_clause) = clause.as_trait_clause() else {
                continue;
            };
            let trait_ref = trait_clause.skip_binder().trait_ref;
            if matches!(trait_ref.self_ty().kind(), TyKind::Param(p) if p.index == param_index) {
                bound_traits.insert(trait_ref.def_id);
            }
        }
        current = predicates.parent;
    }
    let hits: Vec<&LogicFnFamilyMember> = family
        .iter()
        .filter(|member| {
            member.kind == LogicFnOwnerKind::TraitDecl
                && member.arity == arity
                && (!member.decl_has_visible_body || decl_body_is_sealed(tcx, member))
        })
        .filter(|member| {
            member_def_id(&member.id)
                .is_some_and(|def_id| bound_traits.contains(&tcx.parent(def_id)))
        })
        .collect();
    match hits.as_slice() {
        [decl] if !super::identity::is_ambiguous_id(&decl.id) => Some(decl.id.clone()),
        _ => None,
    }
}

/// A trait declaration whose visible default body NO implementation may
/// override: Creusot's `#[logic(.., sealed)]`. The driver enforces the seal —
/// `validate_impl_does_not_override_sealed_trait_method` rejects any impl that
/// overrides a sealed trait method — so the default body holds at every
/// `Self`, which is exactly what an abstract receiver of a bound generic
/// parameter needs. A default body that is NOT sealed is a fact about no
/// `Self` at all (any impl may replace it), so those declarations stay
/// unbindable here.
fn decl_body_is_sealed(tcx: TyCtxt<'_>, member: &LogicFnFamilyMember) -> bool {
    member_def_id(&member.id).is_some_and(|def_id| {
        tcx.get_all_attrs(def_id)
            .iter()
            .filter_map(crate::attr_utils::doc_marker_str)
            .any(|value| value.as_str().starts_with("trust-wp:logic_sealed:"))
    })
}

/// The trait declaration a call on the associated type `assoc` (of a generic
/// parameter) denotes: the one trait bounding `assoc` in its declaration
/// (`type Assoc: Trait`) that declares an arity-matching method of the family
/// without a visible default body.
pub(crate) fn decl_for_projection(
    tcx: TyCtxt<'_>,
    assoc: DefId,
    family: &[LogicFnFamilyMember],
    arity: usize,
) -> Option<String> {
    let mut bound_traits = std::collections::HashSet::new();
    for (clause, _) in tcx.explicit_item_bounds(assoc).skip_binder() {
        if let rustc_middle::ty::ClauseKind::Trait(predicate) = clause.kind().skip_binder() {
            bound_traits.insert(predicate.trait_ref.def_id);
        }
    }
    let hits: Vec<&LogicFnFamilyMember> = family
        .iter()
        .filter(|member| {
            member.kind == LogicFnOwnerKind::TraitDecl
                && member.arity == arity
                && !member.decl_has_visible_body
        })
        .filter(|member| {
            member_def_id(&member.id)
                .is_some_and(|def_id| bound_traits.contains(&tcx.parent(def_id)))
        })
        .collect();
    match hits.as_slice() {
        [decl] if !super::identity::is_ambiguous_id(&decl.id) => Some(decl.id.clone()),
        _ => None,
    }
}

/// Whether every member of `family` is an impl of the external `View` trait,
/// so that `x.view()` is exactly the model operator `x@` for any receiver
/// without a local impl.
pub(crate) fn is_external_view_family(family: &[LogicFnFamilyMember]) -> bool {
    !family.is_empty()
        && family.iter().all(|member| {
            member.short_name == "view"
                && member.arity == 1
                && member.receiver_is_self
                && member.kind == LogicFnOwnerKind::TraitImpl
                && member
                    .trait_path
                    .as_deref()
                    .is_some_and(|path| path == "creusot_std::View" || path.ends_with("::View"))
        })
}

/// `x.view()` on a PRIMITIVE receiver (`bool`, `char`, machine integers) in a
/// `view` family that is not purely external `View` impls: exactly `x@` when
/// no member can be the callee. Free functions never answer a method call,
/// no local inherent impl or local `View` impl can have a primitive self
/// type, and a local trait (declaration or impl of a trait other than `View`)
/// might be implemented for the primitive, so any such member refuses.
pub(crate) fn model_view_applies_to_primitive<'tcx>(
    tcx: TyCtxt<'tcx>,
    family: &[LogicFnFamilyMember],
    ty: Ty<'tcx>,
) -> bool {
    let ty = tcx.erase_and_anonymize_regions(ty.peel_refs());
    if !matches!(
        ty.kind(),
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_)
    ) {
        return false;
    }
    !family.is_empty()
        && family.iter().all(|member| {
            member.short_name == "view"
                && match member.kind {
                    LogicFnOwnerKind::Free | LogicFnOwnerKind::Inherent => true,
                    LogicFnOwnerKind::TraitImpl => {
                        member.trait_path.as_deref().is_some_and(|path| {
                            path == "creusot_std::View" || path.ends_with("::View")
                        })
                    }
                    LogicFnOwnerKind::TraitDecl => false,
                }
        })
        && !has_local_view_impl(tcx, family, ty)
}

/// The value-parameter types and the return type of a function-like owner.
pub(crate) fn owner_signature<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
) -> Option<(Vec<Ty<'tcx>>, Ty<'tcx>)> {
    if !matches!(tcx.def_kind(owner), DefKind::Fn | DefKind::AssocFn) {
        return None;
    }
    let sig = tcx.fn_sig(owner).instantiate_identity().skip_binder();
    Some((sig.inputs().to_vec(), sig.output()))
}

/// A callee's clause is a `requires`/`ensures`: read at the top of its body.
fn generic_param_by_name(tcx: TyCtxt<'_>, owner: DefId, name: &str) -> GenericTypeParam {
    super::identity::visible_generic_type_param(
        tcx,
        owner,
        name,
        super::identity::ClausePosition::Signature,
    )
}

/// The value-parameter types and return type of `trait_method` as they read
/// at `impl_method`, the impl item implementing it: the trait signature
/// instantiated with the impl's trait arguments (the impl method's own
/// generics rebased onto them, as rustc compares an impl item with its trait
/// item) and normalized in the impl method's environment, so an associated
/// type of `Self` is the impl's choice. `None` when any type does not
/// normalize.
pub(crate) fn trait_signature_at_impl<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_method: DefId,
    impl_method: DefId,
) -> Option<(Vec<Ty<'tcx>>, Ty<'tcx>)> {
    if !matches!(tcx.def_kind(trait_method), DefKind::AssocFn)
        || !matches!(tcx.def_kind(impl_method), DefKind::AssocFn)
    {
        return None;
    }
    let impl_id = tcx.parent(impl_method);
    let trait_ref = tcx.impl_trait_ref(impl_id).skip_binder();
    if trait_ref.def_id != tcx.parent(trait_method) {
        return None;
    }
    let impl_args = rustc_middle::ty::GenericArgs::identity_for_item(tcx, impl_method);
    let trait_args = impl_args.rebase_onto(tcx, impl_id, trait_ref.args);
    let sig = tcx.instantiate_bound_regions_with_erased(
        tcx.fn_sig(trait_method)
            .instantiate(tcx, trait_args)
            .skip_norm_wip(),
    );
    let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, impl_method);
    let normalize = |ty: Ty<'tcx>| {
        tcx.try_normalize_erasing_regions(
            typing_env,
            rustc_middle::ty::set_aliases_to_non_rigid(tcx, ty),
        )
        .ok()
    };
    let inputs = sig
        .inputs()
        .iter()
        .map(|ty| normalize(*ty))
        .collect::<Option<Vec<_>>>()?;
    Some((inputs, normalize(sig.output())?))
}

/// A receiver spelled `(^x)`, `(*x)`, `(&*x)` …: the offset of the opening
/// parenthesis, the identifier the prefix operators apply to, and the
/// operators as written (outermost first, spaces removed).
///
/// `None` unless `text` ENDS with exactly such a parenthesised expression and
/// nothing binds tighter in front of it, so `(a + b).m()` and `y.f(z).m()` are
/// left unresolved rather than typed on the wrong name.
fn prefixed_paren_receiver(text: &str) -> Option<(usize, String, String)> {
    let bytes = text.as_bytes();
    if bytes.last() != Some(&b')') {
        return None;
    }
    let close = text.len() - 1;
    let mut depth = 0i32;
    let mut index = text.len();
    let open = loop {
        if index == 0 {
            return None;
        }
        index -= 1;
        match bytes[index] {
            b')' => depth += 1,
            b'(' => {
                depth -= 1;
                if depth == 0 {
                    break index;
                }
            }
            _ => {}
        }
    };
    // A call head, a field/path chain or another parenthesised expression in
    // front means this is not the whole receiver.
    if open > 0
        && (is_ident_byte(bytes[open - 1])
            || matches!(bytes[open - 1], b'.' | b':' | b'@' | b')' | b']'))
    {
        return None;
    }
    let inner = text[open + 1..close].trim();
    let name = inner.trim_start_matches(|ch| matches!(ch, '^' | '*' | '&' | ' '));
    if name.is_empty()
        || name.len() == inner.len()
        || !name.bytes().all(is_ident_byte)
        || name.as_bytes()[0].is_ascii_digit()
    {
        return None;
    }
    let ops: String = inner[..inner.len() - name.len()]
        .chars()
        .filter(|ch| *ch != ' ')
        .collect();
    Some((open, name.to_string(), ops))
}

/// The Rust type of `ops` (prefix operators as written, outermost first)
/// applied to a value of type `ty`, which is where Rust's method lookup on
/// `(ops x).m()` starts: `*` and `^` read through one reference or box.
/// Anything else is refused. A borrow `&`: the clause text the call sites
/// parse reads `&x` as `x` (method_call_borrowed_receiver_callee_contract_granted.rs),
/// so no resolution may rest on the reference's type. A `*`/`^` of any other
/// type (a snapshot's or a model type's `Deref`): the lookup starts at the
/// `Deref` target, which this does not compute, and the operand's own type
/// may take a method the target never has
/// (method_call_deref_snapshot_receiver_callee_contract_granted.rs).
fn prefixed_receiver_type<'tcx>(ops: &str, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let mut ty = ty;
    for op in ops.chars().rev() {
        ty = match (op, ty.kind()) {
            ('&', _) => return None,
            (_, TyKind::Ref(_, pointee, _)) => *pointee,
            (_, TyKind::Adt(adt, args)) if adt.is_box() => args.type_at(0),
            _ => return None,
        };
    }
    Some(ty)
}

fn is_ident_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

/// Index of the `)` matching the `(` at `open`.
fn matching_paren(text: &str, open: usize) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut depth = 0usize;
    for (offset, &byte) in bytes[open..].iter().enumerate() {
        match byte {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return (byte == b')').then_some(open + offset);
                }
            }
            _ => {}
        }
    }
    None
}

/// Number of top-level arguments in `args` (`None` when a closure or other
/// construct makes the count uncertain).
fn argument_count(args: &str) -> Option<usize> {
    if args.contains('|') {
        return None;
    }
    if args.trim().is_empty() {
        return Some(0);
    }
    let mut depth = 0usize;
    let mut count = 1;
    for byte in args.bytes() {
        match byte {
            b'(' | b'[' | b'{' | b'<' => depth += 1,
            b')' | b']' | b'}' | b'>' => depth = depth.saturating_sub(1),
            b',' if depth == 0 => count += 1,
            _ => {}
        }
    }
    Some(count)
}

/// Every name bound inside `expr` (quantifiers, `let`, match arms, closures).
fn collect_binders(expr: &PureExpr, out: &mut std::collections::HashSet<String>) {
    fn pattern_names(pattern: &Pattern, out: &mut std::collections::HashSet<String>) {
        match pattern {
            Pattern::Binding(name) => {
                out.insert(name.clone());
            }
            Pattern::Alias { alias, pattern } => {
                out.insert(alias.clone());
                pattern_names(pattern, out);
            }
            Pattern::Constructor { inner, .. } => {
                if let Some(inner) = inner {
                    pattern_names(inner, out);
                }
            }
            Pattern::Tuple(items) => {
                for item in items {
                    pattern_names(item, out);
                }
            }
            _ => {}
        }
    }
    expr.for_each_recursive(|node| match node {
        PureExpr::Forall { var, .. } | PureExpr::Exists { var, .. } | PureExpr::Let { var, .. } => {
            out.insert(var.clone());
        }
        PureExpr::Match { arms, .. } => {
            for MatchArm { pattern, .. } in arms {
                pattern_names(pattern, out);
            }
        }
        PureExpr::Closure { params, .. } => {
            for (name, _) in params {
                out.insert(name.clone());
            }
        }
        _ => {}
    });
}

/// How one written occurrence is rewritten.
enum Rewrite {
    /// Replace `[start, end)` by `text`.
    Span(usize, usize, String),
    /// Leave the occurrence to static path resolution.
    Skip,
}

/// Rewrite receiver-style and type-qualified calls to colliding logic
/// functions in the clause TEXT of `owner` (a callee contract kept as text and
/// re-parsed at call sites).
///
/// - `x.m(a)` / `Tr::m(x, a)` / `m(x, a)` with `x` a parameter (or `result`)
///   of concrete type -> `<id>(x, a)`;
/// - the same on a generic parameter type -> `<generic marker>(x, a)`;
/// - `T::k(..)` / `Self::k(..)` / `<T as Tr>::k(..)` on a generic parameter ->
///   `<generic marker>(..)`;
/// - any other receiver-style or generic-qualified occurrence of a colliding
///   name -> the refusal marker.
///
/// Static paths (`a::k`, `<A as Tr>::k`, `Type::k`) are left to
/// `resolve_clause_text_in_scope`.
///
/// `clause` is the specification of `owner` the text is. A call bound on a
/// receiver's type is kept only where rustc's type check of that
/// specification resolved it to the same definition, and a generic receiver
/// is marked with the trait method rustc resolved it to there
/// (`spec_calls`); otherwise it is refused.
pub(crate) fn resolve_family_calls_in_text<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    text: &str,
    clause: &ClauseRef,
) -> String {
    let Some(registry) = logic_fn_identity_registry() else {
        return text.to_string();
    };
    if registry.is_empty() || !owner.is_local() {
        return text.to_string();
    }
    let parsed = trust_wp_core::contract_parser::parse_contract(text).ok();
    let mut binders = std::collections::HashSet::new();
    if let Some(parsed) = parsed.as_ref() {
        collect_binders(parsed, &mut binders);
    }
    let parse_failed = parsed.is_none();
    let param_names: Vec<String> = if matches!(tcx.def_kind(owner), DefKind::Fn | DefKind::AssocFn)
    {
        tcx.fn_arg_idents(owner)
            .iter()
            .map(|ident| ident.map_or_else(String::new, |ident| ident.name.to_string()))
            .collect()
    } else {
        Vec::new()
    };
    let signature = owner_signature(tcx, owner);
    let spec_calls: std::cell::OnceCell<Option<SpecCalls<'tcx>>> = std::cell::OnceCell::new();
    let spec_calls = || {
        spec_calls
            .get_or_init(|| SpecCalls::of(tcx, owner, clause))
            .as_ref()
    };

    // Candidate occurrences: identifier starts naming a colliding short name
    // followed by `(`, processed right to left so earlier offsets stay valid.
    let mut starts = Vec::new();
    {
        let bytes = text.as_bytes();
        let mut index = 0;
        while index < bytes.len() {
            if is_ident_byte(bytes[index]) && (index == 0 || !is_ident_byte(bytes[index - 1])) {
                let mut end = index;
                while end < bytes.len() && is_ident_byte(bytes[end]) {
                    end += 1;
                }
                let word = &text[index..end];
                let after = text[end..].trim_start();
                if after.starts_with('(') && registry.family(word).is_some() {
                    starts.push((index, end));
                }
                index = end;
            } else {
                index += 1;
            }
        }
    }

    let mut out = text.to_string();
    for (start, end) in starts.into_iter().rev() {
        let word = out[start..end].to_string();
        let Some(family) = registry.family(&word) else {
            continue;
        };
        let open = end + (out[end..].len() - out[end..].trim_start().len());
        let Some(close) = matching_paren(&out, open) else {
            continue;
        };
        let args_text = out[open + 1..close].to_string();
        let receiver_style = family.iter().all(|member| member.receiver_is_self);
        let before = out[..start].trim_end();
        let refused = refused_call_marker(&word);

        // A name the owner's body redeclares is not the one the module has.
        let shadowed_in_scope = |path: &str| {
            super::identity::path_scope_names(path)
                .any(|written| super::identity::shadowed_by_body_item(tcx, owner, written))
        };
        let typed_on_param = |name: &str| -> Option<Ty<'_>> {
            if binders.contains(name) || parse_failed {
                return None;
            }
            let (inputs, output) = signature.as_ref()?;
            if name == "result" {
                return Some(*output);
            }
            match param_names.iter().position(|param| param == name) {
                Some(position) => inputs.get(position).copied(),
                None => super::identity::unit_struct_value_type(tcx, owner, name),
            }
        };
        // What a call written as `form` (a path call's callee path `path`)
        // with `arity` arguments on `receiver` names, where the hand lookup
        // read `outcome`: the id rustc's type check confirms, a generic
        // marker carrying the trait method rustc resolved a generic
        // receiver's call to, or the refusal.
        let outcome_head = |outcome: TypedOutcome,
                            arity: usize,
                            by_receiver: bool,
                            form: CallForm,
                            path: Option<&str>,
                            receiver: Option<Ty<'tcx>>,
                            root: Option<&str>|
         -> String {
            let path_beside = |calls: &SpecCalls<'tcx>| {
                form == CallForm::Method && calls.holds(CallForm::Path, &word, arity)
            };
            match outcome {
                TypedOutcome::Id(id) => {
                    let confirmed = member_def_id(&id).is_some_and(|chosen| {
                        spec_calls().is_some_and(|calls| {
                            calls.confirms(tcx, form, &word, path, arity, receiver, root, chosen)
                                && !path_beside(calls)
                        })
                    });
                    if confirmed {
                        id
                    } else {
                        refused.clone()
                    }
                }
                TypedOutcome::Generic(param_index) => {
                    // The trait rustc resolved the call to, which must also be
                    // the one bound trait declaring the name.
                    let trait_id = bound_trait_declaring(tcx, owner, param_index, &word);
                    let decl = spec_calls()
                        .filter(|calls| !path_beside(calls))
                        .and_then(|calls| {
                            calls.trait_method_resolved(
                                tcx, form, &word, path, arity, receiver, root,
                            )
                        })
                        .filter(|decl| {
                            family.iter().any(|member| {
                                member.kind == LogicFnOwnerKind::TraitDecl
                                    && member.arity == arity
                                    && member_def_id(&member.id) == Some(*decl)
                            })
                        });
                    match (trait_id, decl) {
                        (Some(trait_id), Some(decl)) if tcx.parent(decl) == trait_id => {
                            generic_marker_name(GenericMarker {
                                callee: owner,
                                param_index,
                                short: word.clone(),
                                arity,
                                by_receiver,
                                trait_id,
                                decl,
                            })
                        }
                        _ => refused.clone(),
                    }
                }
                TypedOutcome::Projection(_) | TypedOutcome::Refused => refused.clone(),
            }
        };

        let rewrite = if before.ends_with('.') && !before.ends_with("..") {
            // Method syntax `recv.m(args)`.
            let dot = before.len() - 1;
            let recv_end = out[..dot].trim_end().len();
            let bytes = out.as_bytes();
            let mut recv_start = recv_end;
            while recv_start > 0 && is_ident_byte(bytes[recv_start - 1]) {
                recv_start -= 1;
            }
            let mut simple = recv_start < recv_end
                && !bytes[recv_start].is_ascii_digit()
                && (recv_start == 0 || !matches!(bytes[recv_start - 1], b'.' | b':' | b'@'))
                && !(recv_start > 0 && is_ident_byte(bytes[recv_start - 1]));
            // `(^x).m(..)` / `(*x).m(..)`: the prophecy, or the pointee, of a
            // parameter, typed as Rust types that receiver
            // (`prefixed_receiver_type`), where its method lookup starts. The
            // receiver TEXT is re-emitted verbatim, so the clause keeps saying
            // `^x`.
            let mut type_name: Option<String> = None;
            let mut prefix_ops = String::new();
            if !simple {
                if let Some((paren, name, ops)) = prefixed_paren_receiver(&out[..recv_end]) {
                    recv_start = paren;
                    type_name = Some(name);
                    prefix_ops = ops;
                    simple = true;
                }
            }
            let arity = argument_count(&args_text).map(|count| count + 1);
            match (simple, arity) {
                (true, Some(arity)) if receiver_style => {
                    let receiver = out[recv_start..recv_end].to_string();
                    let receiver_ty = typed_on_param(type_name.as_deref().unwrap_or(&receiver))
                        .and_then(|ty| prefixed_receiver_type(&prefix_ops, ty));
                    let outcome = receiver_ty.map_or(TypedOutcome::Refused, |ty| {
                        resolve_family_on_type(tcx, family, arity, ty, true, Some(owner))
                    });
                    let no_local_impl = matches!(
                        outcome,
                        TypedOutcome::Refused
                            | TypedOutcome::Generic(_)
                            | TypedOutcome::Projection(_)
                    );
                    let model_view = if is_external_view_family(family) {
                        no_local_impl
                            && receiver_ty.is_some_and(|ty| !has_local_view_impl(tcx, family, ty))
                    } else {
                        outcome == TypedOutcome::Refused
                            && receiver_ty
                                .is_some_and(|ty| model_view_applies_to_primitive(tcx, family, ty))
                    };
                    // A method call names the logic pick only where Rust's
                    // method lookup can select nothing else there.
                    let outcome = match outcome {
                        TypedOutcome::Id(id)
                            if !receiver_ty.zip(member_def_id(&id)).is_some_and(
                                |(ty, def_id)| {
                                    crate::logic::method_lookup::selects_only(
                                        tcx, &word, ty, def_id, true,
                                    )
                                },
                            ) =>
                        {
                            TypedOutcome::Refused
                        }
                        other => other,
                    };
                    if receiver_ty.is_some() && arity == 1 && model_view {
                        // `x.view()` without a local impl for `x`'s type is
                        // exactly the model operator `x@`.
                        Rewrite::Span(recv_start, close + 1, format!("({receiver})@"))
                    } else if outcome == TypedOutcome::Refused
                        || matches!(outcome, TypedOutcome::Projection(_))
                    {
                        Rewrite::Span(start, end, refused.clone())
                    } else {
                        let head = outcome_head(
                            outcome,
                            arity,
                            true,
                            CallForm::Method,
                            None,
                            receiver_ty,
                            Some(type_name.as_deref().unwrap_or(&receiver)),
                        );
                        let joined = if args_text.trim().is_empty() {
                            format!("{head}({receiver})")
                        } else {
                            format!("{head}({receiver}, {args_text})")
                        };
                        Rewrite::Span(recv_start, close + 1, joined)
                    }
                }
                _ => Rewrite::Span(start, end, refused.clone()),
            }
        } else if before.ends_with("::") {
            // Path head `Q::m(args)`: find the qualifier.
            let qualifier_end = before.len() - 2;
            let bytes = out.as_bytes();
            let mut q_start = qualifier_end;
            if q_start > 0 && bytes[q_start - 1] == b'>' {
                let mut depth = 0i32;
                while q_start > 0 {
                    q_start -= 1;
                    match bytes[q_start] {
                        b'>' => depth += 1,
                        b'<' => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => {}
                    }
                }
            }
            while q_start > 0 && (is_ident_byte(bytes[q_start - 1]) || bytes[q_start - 1] == b':') {
                q_start -= 1;
            }
            let qualifier = out[q_start..qualifier_end].trim().to_string();
            if shadowed_in_scope(&format!("{qualifier}::{word}")) {
                out.replace_range(q_start..end, &refused);
                continue;
            }
            let generic_self = if let Some(inner) = qualifier
                .strip_prefix('<')
                .and_then(|rest| rest.strip_suffix('>'))
            {
                inner
                    .split_once(" as ")
                    .map(|(ty, _)| ty.trim().to_string())
            } else if !qualifier.contains("::") {
                Some(qualifier.clone())
            } else {
                None
            };
            let generic = generic_self
                .as_deref()
                .filter(|name| !binders.contains(*name))
                .map_or(GenericTypeParam::NotParam, |name| {
                    generic_param_by_name(tcx, owner, name)
                });
            let arity = argument_count(&args_text);
            let callee_path = out[q_start..end].to_string();
            match (generic, arity) {
                (GenericTypeParam::Visible(param_index), Some(arity)) => {
                    let first = args_text.split(',').next().unwrap_or("").trim();
                    let head = outcome_head(
                        TypedOutcome::Generic(param_index),
                        arity,
                        false,
                        CallForm::Path,
                        Some(&callee_path),
                        typed_on_param(first),
                        (!first.is_empty() && first.bytes().all(is_ident_byte)).then_some(first),
                    );
                    Rewrite::Span(q_start, end, head)
                }
                (GenericTypeParam::Visible(_), None) | (GenericTypeParam::Refused, _) => {
                    Rewrite::Span(q_start, end, refused.clone())
                }
                // `Q::m(x, ..)` / `<X as Q>::m(x, ..)`: `Q` read in the owner's
                // scope, block scopes first (`qualified_path_rewrite`), and the
                // head confirmed by rustc's type check of the clause.
                (GenericTypeParam::NotParam, Some(arity)) if receiver_style && arity > 0 => {
                    let named = qualifier
                        .strip_prefix('<')
                        .and_then(|rest| rest.strip_suffix('>'))
                        .map(|inner| {
                            inner
                                .split_once(" as ")
                                .map(|(_, trait_text)| trait_text.trim())
                        });
                    match named {
                        // `<X as Q>` with no trait to read: the encoder's dispatch.
                        Some(None) => Rewrite::Skip,
                        Some(Some(trait_text)) => qualified_path_rewrite(
                            tcx,
                            owner,
                            family,
                            trait_text,
                            &word,
                            &callee_path,
                            &args_text,
                            arity,
                            &typed_on_param,
                            &outcome_head,
                        )
                        .map_or(Rewrite::Skip, |head| Rewrite::Span(q_start, end, head)),
                        None => qualified_path_rewrite(
                            tcx,
                            owner,
                            family,
                            &qualifier,
                            &word,
                            &callee_path,
                            &args_text,
                            arity,
                            &typed_on_param,
                            &outcome_head,
                        )
                        .map_or(Rewrite::Skip, |head| Rewrite::Span(q_start, end, head)),
                    }
                }
                _ => continue,
            }
        } else if !before.ends_with(':')
            && !before
                .as_bytes()
                .last()
                .is_some_and(|byte| is_ident_byte(*byte))
            && argument_count(&args_text).map_or(receiver_style, |arity| {
                arity > 0 && dispatches_on_receiver(family, arity)
            })
        {
            if shadowed_in_scope(&word) {
                out.replace_range(start..end, &refused);
                continue;
            }
            // Bare `m(x, ..)` where every definition of its arity is a method
            // (the call the encoder would dispatch on `x`'s sort): Rust reads
            // the name's value-namespace binding, never a method, so it is a
            // method only as the model `view`/`resolve`, at the first
            // argument's type.
            let own = crate::logic::identity::bare_call_model_trait(tcx, owner, &word)
                .map(|model_trait| {
                    crate::logic::identity::model_trait_impls(tcx, family, model_trait)
                })
                .unwrap_or_default();
            match argument_count(&args_text) {
                Some(arity) if arity > 0 && !own.is_empty() => self_typed_first_argument(
                    tcx,
                    &own,
                    &word,
                    &args_text,
                    arity,
                    &typed_on_param,
                    &outcome_head,
                )
                .map_or(Rewrite::Span(start, end, refused.clone()), |head| {
                    Rewrite::Span(start, end, head)
                }),
                _ => Rewrite::Span(start, end, refused.clone()),
            }
        } else {
            continue;
        };
        if let Rewrite::Span(from, to, replacement) = rewrite {
            out.replace_range(from..to, &replacement);
        }
    }
    out
}

/// The one trait bounding the generic parameter `param_index` of `owner` (its
/// bounds' supertraits included) that declares an associated function
/// `short`: the trait Rust reads a call of `short` on that parameter as a
/// method of. `None` when there is no such trait or more than one.
fn bound_trait_declaring(
    tcx: TyCtxt<'_>,
    owner: DefId,
    param_index: u32,
    short: &str,
) -> Option<DefId> {
    let mut bound = std::collections::HashSet::new();
    let mut current = Some(owner);
    while let Some(did) = current {
        let predicates = tcx.clauses_of(did);
        for (clause, _) in predicates.clauses {
            if let Some(trait_clause) = clause.as_trait_clause() {
                let trait_ref = trait_clause.skip_binder().trait_ref;
                if matches!(trait_ref.self_ty().kind(), TyKind::Param(p) if p.index == param_index)
                {
                    bound.insert(trait_ref.def_id);
                }
            }
        }
        current = predicates.parent;
    }
    // A trait's supertraits are `Self: Super` clauses of the trait itself.
    let mut stack: Vec<DefId> = bound.iter().copied().collect();
    while let Some(trait_id) = stack.pop() {
        for (clause, _) in tcx.clauses_of(trait_id).clauses {
            if let Some(trait_clause) = clause.as_trait_clause() {
                let trait_ref = trait_clause.skip_binder().trait_ref;
                if matches!(trait_ref.self_ty().kind(), TyKind::Param(p) if p.index == 0)
                    && bound.insert(trait_ref.def_id)
                {
                    stack.push(trait_ref.def_id);
                }
            }
        }
    }
    let symbol = rustc_span::Symbol::intern(short);
    let declaring: Vec<DefId> = bound
        .into_iter()
        .filter(|trait_id| {
            tcx.associated_items(*trait_id)
                .filter_by_name_unhygienic(symbol)
                .any(|item| matches!(item.kind, rustc_middle::ty::AssocKind::Fn { .. }))
        })
        .collect();
    match declaring.as_slice() {
        [trait_id] => Some(*trait_id),
        _ => None,
    }
}

/// Whether some local impl in `family` could apply to `ty` (or `ty` is not
/// yet known to exclude one: a generic parameter may be instantiated with a
/// local type, which `x@` handles by that type's own view).
fn has_local_view_impl<'tcx>(
    tcx: TyCtxt<'tcx>,
    family: &[LogicFnFamilyMember],
    ty: Ty<'tcx>,
) -> bool {
    let ty = tcx.erase_and_anonymize_regions(ty.peel_refs());
    if ty.has_non_region_param() {
        return false;
    }
    family.iter().any(|member| {
        member_def_id(&member.id)
            .is_some_and(|def_id| applies_at_closed(tcx, def_id, ty) != Applies::No)
    })
}

/// The head a written `Q::m(x, ..)` or `<X as Q>::m(x, ..)` gets in callee
/// clause text, where `m`'s every local logic definition is a method. `Q` is
/// read in the owner's scope: a trait names ITS method at `x`'s type, an impl
/// or its default body (refused when a local trait gives none); a local type
/// names its inherent function `m` (the scope resolver reads that one), else
/// the one logic method Rust's lookup at that type can select, else refused.
/// Anything else is left to the scope resolver (`None`). `callee_path` is the
/// call's callee path as written; rustc's type check must confirm the head
/// (`outcome_head`).
#[allow(clippy::too_many_arguments)]
fn qualified_path_rewrite<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    family: &[LogicFnFamilyMember],
    qualifier: &str,
    word: &str,
    callee_path: &str,
    args_text: &str,
    arity: usize,
    typed_on_param: &dyn Fn(&str) -> Option<Ty<'tcx>>,
    outcome_head: &dyn Fn(
        TypedOutcome,
        usize,
        bool,
        CallForm,
        Option<&str>,
        Option<Ty<'tcx>>,
        Option<&str>,
    ) -> String,
) -> Option<String> {
    use crate::logic::identity::{qualifier_in_scope, trait_members, QualifierTarget};
    let refused = refused_call_marker(word);
    match qualifier_in_scope(tcx, owner, qualifier) {
        QualifierTarget::Trait(trait_id) => {
            let own = trait_members(tcx, family, trait_id);
            self_typed_first_argument(
                tcx,
                &own,
                callee_path,
                args_text,
                arity,
                typed_on_param,
                outcome_head,
            )
            .or_else(|| trait_id.is_local().then_some(refused))
        }
        QualifierTarget::Adt(adt) if adt.is_local() => {
            let symbol = rustc_span::Symbol::intern(word);
            let has_inherent = tcx.inherent_impls(adt).iter().any(|impl_id| {
                tcx.associated_items(*impl_id)
                    .filter_by_name_unhygienic(symbol)
                    .next()
                    .is_some()
            });
            if has_inherent {
                return None;
            }
            let first = args_text.split(',').next()?.trim();
            let at_type = typed_on_param(first)
                .map(|ty| tcx.erase_and_anonymize_regions(ty.peel_refs()))
                .filter(|ty| matches!(ty.kind(), TyKind::Adt(def, _) if def.did() == adt));
            let head = at_type.and_then(|ty| {
                match resolve_family_on_type(tcx, family, arity, ty, true, None) {
                    TypedOutcome::Id(id)
                        if member_def_id(&id).is_some_and(|def_id| {
                            crate::logic::method_lookup::selects_only(tcx, word, ty, def_id, true)
                        }) =>
                    {
                        Some(outcome_head(
                            TypedOutcome::Id(id),
                            arity,
                            true,
                            CallForm::Path,
                            Some(callee_path),
                            Some(ty),
                            Some(first),
                        ))
                    }
                    _ => None,
                }
            });
            Some(head.unwrap_or(refused))
        }
        QualifierTarget::Adt(_) | QualifierTarget::Other => None,
    }
}

/// `callee_path` is the call's callee path as written (`Tr::m`, `m`).
fn self_typed_first_argument<'tcx>(
    tcx: TyCtxt<'tcx>,
    family: &[LogicFnFamilyMember],
    callee_path: &str,
    args_text: &str,
    arity: usize,
    typed_on_param: &dyn Fn(&str) -> Option<Ty<'tcx>>,
    outcome_head: &dyn Fn(
        TypedOutcome,
        usize,
        bool,
        CallForm,
        Option<&str>,
        Option<Ty<'tcx>>,
        Option<&str>,
    ) -> String,
) -> Option<String> {
    let first = args_text.split(',').next()?.trim();
    if first.is_empty() || !first.bytes().all(is_ident_byte) {
        return None;
    }
    let ty = typed_on_param(first)?;
    // A path call names no receiver to probe, so no trait counts as in scope.
    match resolve_family_on_type(tcx, family, arity, ty, true, None) {
        TypedOutcome::Refused => None,
        outcome => Some(outcome_head(
            outcome,
            arity,
            true,
            CallForm::Path,
            Some(callee_path),
            Some(ty),
            Some(first),
        )),
    }
}

/// Re-resolve the generic markers in a callee contract at one call site.
///
/// `caller` is the function whose body contains the call, `callee` the spec's
/// owner and `substs` the call's generic arguments. Each marker becomes the
/// id of the impl its instantiated type selects, the declaration symbol when
/// the instantiated type is a generic parameter of the caller (the caller's
/// own verification), or the refusal marker.
pub(crate) fn instantiate_generic_markers<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    callee: DefId,
    substs: GenericArgs<'tcx>,
    spec: &StdSpec,
) -> Option<StdSpec> {
    let mentions = |clause: &String| clause.contains(LOGIC_FN_GENERIC_PREFIX);
    if !spec
        .requires
        .iter()
        .chain(spec.ensures.iter())
        .any(mentions)
    {
        return None;
    }
    let registry = logic_fn_identity_registry()?;
    let rewrite = |clause: &String| -> String {
        let mut out = String::with_capacity(clause.len());
        let mut rest = clause.as_str();
        while let Some(position) = rest.find(LOGIC_FN_GENERIC_PREFIX) {
            out.push_str(&rest[..position]);
            let after = &rest[position + LOGIC_FN_GENERIC_PREFIX.len()..];
            let digits = after.bytes().take_while(u8::is_ascii_digit).count();
            let slot = after[..digits].parse::<usize>().ok();
            let marker = slot.and_then(generic_marker);
            let replacement = match marker {
                Some(marker) if marker.callee == callee => {
                    // `<T as Tr>::m` at the call's `T`: Tr's impl for it, or
                    // Tr's default body there, never another definition of
                    // the name (generic_callee_*_granted.rs).
                    let own = registry
                        .family(&marker.short)
                        .map(|family| super::identity::trait_members(tcx, family, marker.trait_id));
                    let family = own.as_deref().filter(|own| !own.is_empty());
                    let ty = substs
                        .get(marker.param_index as usize)
                        .and_then(|arg| arg.as_type());
                    match (family, ty) {
                        (Some(family), Some(ty)) => {
                            instantiated_marker(tcx, family, &marker, ty, callee)
                                .unwrap_or_else(|| refused_call_marker(&marker.short))
                        }
                        _ => refused_call_marker(&marker.short),
                    }
                }
                Some(marker) => refused_call_marker(&marker.short),
                None => refused_call_marker("generic"),
            };
            if std::env::var_os("TRUST_WP_LOGIC_IDENTITY_TRACE").is_some() {
                eprintln!(
                    "trust-wp: logic-identity call-site callee={} caller={} marker={} -> {replacement}",
                    tcx.def_path_str(callee),
                    tcx.def_path_str(caller),
                    &after[..digits]
                );
            }
            out.push_str(&replacement);
            rest = &after[digits..];
        }
        out.push_str(rest);
        out
    };
    Some(StdSpec {
        // The synthesized type-invariant clauses carry no generic marker to
        // re-resolve: they are `PureExpr` over the callee's own parameters,
        // minted from its signature, not contract text. Rebuilding the spec
        // without them handed the call site a callee that owes nothing while
        // `clause_enrichment` still grants the body the premise — the free
        // grant this vector exists to close.
        inv_requires: spec.inv_requires.clone(),
        // Carried for the same reason: the capture vector is minted from the
        // closure's environment, not from contract text, and dropping it would
        // leave the construction site owing nothing.
        capture_inv_requires: spec.capture_inv_requires.clone(),
        requires: spec.requires.iter().map(rewrite).collect(),
        ensures: spec.ensures.iter().map(rewrite).collect(),
        param_names: spec.param_names.clone(),
    })
}

/// What the call `marker` stands for names where the callee's generic
/// parameter is `ty`. rustc resolved the call in the callee to the trait
/// method `marker.decl`, so at `ty` it names that method's instance there,
/// never a re-reading of the call at `ty` (which would see an inherent method
/// or another trait's): the one family member Rust may select at `ty` that
/// implements `marker.decl` or is its default, or at a generic `ty` the
/// declaration itself where it may stand for an abstract `Self`.
fn instantiated_marker<'tcx>(
    tcx: TyCtxt<'tcx>,
    family: &[LogicFnFamilyMember],
    marker: &GenericMarker,
    ty: Ty<'tcx>,
    callee: DefId,
) -> Option<String> {
    let implements_decl = |id: &str| {
        member_def_id(id).is_some_and(|def_id| {
            def_id == marker.decl
                || tcx
                    .opt_associated_item(def_id)
                    .and_then(|item| item.trait_item_def_id())
                    == Some(marker.decl)
        })
    };
    match resolve_family_on_type(
        tcx,
        family,
        marker.arity,
        ty,
        marker.by_receiver,
        Some(callee),
    ) {
        TypedOutcome::Id(id) => implements_decl(&id).then_some(id),
        TypedOutcome::Generic(_) => family
            .iter()
            .find(|member| {
                member.kind == LogicFnOwnerKind::TraitDecl
                    && member.arity == marker.arity
                    && member_def_id(&member.id) == Some(marker.decl)
                    && (!member.decl_has_visible_body || decl_body_is_sealed(tcx, member))
            })
            .map(|member| member.id.clone()),
        TypedOutcome::Projection(_) | TypedOutcome::Refused => None,
    }
}

/// [`instantiate_generic_markers`] for a MIR call operand: the caller is the
/// body's owner, the generic arguments come from the callee's `FnDef` type.
/// A non-`FnDef` operand leaves no way to instantiate, so every generic marker
/// becomes the refusal marker.
pub(crate) fn instantiate_generic_markers_for_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    func: &rustc_middle::mir::Operand<'tcx>,
    callee: DefId,
    spec: StdSpec,
) -> StdSpec {
    let substs = match func {
        rustc_middle::mir::Operand::Constant(constant) => match constant.const_.ty().kind() {
            TyKind::FnDef(_, substs) => Some(substs.skip_binder()),
            _ => None,
        },
        _ => None,
    };
    let substs = substs.unwrap_or_else(rustc_middle::ty::GenericArgs::empty);
    instantiate_generic_markers(tcx, body.source.def_id(), callee, substs, &spec).unwrap_or(spec)
}

#[cfg(test)]
#[path = "identity_typed_tests.rs"]
mod tests;
