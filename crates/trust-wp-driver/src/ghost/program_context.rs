// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! What runs at run time, decided from what trust-wp's own macros wrote and
//! from what rustc resolved, never from a path spelled in user code.
//!
//! `ghost!` and `snapshot!` keep the code they wrap under `cfg(trust_wp)`, and
//! behind `if false` in every other build, so it never runs; the verifier
//! reads it as ghost or logic. The shapes they write (a `Snapshot::capture`
//! call, a block ending in `Snapshot::new_phantom()` or in the dispatch
//! `snapshot_capture_select(..).capture()`) are ordinary Rust, and the same
//! shape spelled in user source, or written by a user's `macro_rules!`, runs in
//! every build (snapshot_capture_spelled_in_program_context_runs_ghost_deref,
//! snapshot_capture_in_user_macro_runs_ghost_deref). Each recogniser here
//! therefore asks for the span of a `trust-wp-macros` expansion as well as the
//! definition rustc resolved.
//!
//! The second half names the trust-wp-std operations whose run-time body is
//! not the logical operation the verifier reads: a logic type's (`Int` is an
//! `i128` whose arithmetic overflows or divides by zero, a `Seq` a `Vec` whose
//! index panics), a snapshot shim's (the `Snapshot<Seq<T>>` shims return an
//! empty value), and a ghost's by a trait a caller's bound asks of it (`Deref`
//! and `Borrow` of a `Ghost` panic).

use rustc_hir::{
    def::{DefKind, Res},
    def_id::DefId,
    Block, Expr, ExprKind,
};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind, TypeVisitableExt, TypeckResults};

use super::type_helpers;
use crate::callbacks::spec_typecheck::span_is_from_trust_wp_macros;

/// The crates whose items are trust-wp-std's ghost and logic API.
fn is_trust_wp_std_crate(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    matches!(
        tcx.crate_name(def_id.krate).as_str(),
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts"
    )
}

/// The definition a call's callee resolves to, as typeck resolved it.
pub(crate) fn resolved_callee(
    typeck_results: &TypeckResults<'_>,
    callee: &Expr<'_>,
) -> Option<DefId> {
    if let Some(ty) = typeck_results.node_type_opt(callee.hir_id) {
        if let TyKind::FnDef(def_id, _) = ty.kind() {
            return Some(*def_id);
        }
    }
    if let ExprKind::Path(qpath) = &callee.kind {
        if let Res::Def(_, def_id) = typeck_results.qpath_res(qpath, callee.hir_id) {
            return Some(def_id);
        }
    }
    None
}

/// The name of the trust-wp-std type whose inherent impl defines `def_id`.
fn trust_wp_inherent_owner(tcx: TyCtxt<'_>, def_id: DefId) -> Option<rustc_span::Symbol> {
    if !is_trust_wp_std_crate(tcx, def_id) {
        return None;
    }
    let parent = tcx.opt_parent(def_id)?;
    if !matches!(tcx.def_kind(parent), DefKind::Impl { of_trait: false }) {
        return None;
    }
    let TyKind::Adt(adt, _) = tcx
        .type_of(parent)
        .instantiate_identity()
        .skip_norm_wip()
        .kind()
    else {
        return None;
    };
    Some(tcx.item_name(adt.did()))
}

fn is_inherent_method(tcx: TyCtxt<'_>, def_id: DefId, owner: &str, names: &[&str]) -> bool {
    trust_wp_inherent_owner(tcx, def_id).is_some_and(|name| name.as_str() == owner)
        && names.contains(&tcx.item_name(def_id).as_str())
}

/// A `Snapshot::capture` call the `snapshot!` expansion wrote.
pub(crate) fn is_macro_snapshot_capture_call(
    tcx: TyCtxt<'_>,
    typeck_results: &TypeckResults<'_>,
    callee: &Expr<'_>,
) -> bool {
    span_is_from_trust_wp_macros(tcx, callee.span)
        && resolved_callee(typeck_results, callee)
            .is_some_and(|def_id| is_inherent_method(tcx, def_id, "Snapshot", &["capture"]))
}

/// A block the `snapshot!` expansion wrote around a capture: the statement
/// form `{ #[cfg(trust_wp)] { .. } Snapshot::<()>::new_phantom() }`, or the
/// dispatch `{ snapshot_capture_select(&(..)).capture() }`. The block itself
/// must be the macro's: a user's block whose tail is a macro-written
/// `new_phantom()` (`{ let v = *g; snapshot!(S {}) }`) holds statements that run.
pub(crate) fn is_macro_snapshot_block(
    tcx: TyCtxt<'_>,
    typeck_results: &TypeckResults<'_>,
    block: &Block<'_>,
) -> bool {
    if !span_is_from_trust_wp_macros(tcx, block.span) {
        return false;
    }
    let Some(tail) = block.expr else {
        return false;
    };
    match tail.kind {
        ExprKind::Call(callee, _) => {
            span_is_from_trust_wp_macros(tcx, callee.span)
                && resolved_callee(typeck_results, callee).is_some_and(|def_id| {
                    is_inherent_method(tcx, def_id, "Snapshot", &["new_phantom"])
                })
        }
        ExprKind::MethodCall(segment, receiver, _, _) if segment.ident.as_str() == "capture" => {
            let ExprKind::Call(select, _) = receiver.kind else {
                return false;
            };
            span_is_from_trust_wp_macros(tcx, select.span)
                && resolved_callee(typeck_results, select).is_some_and(|def_id| {
                    is_trust_wp_std_crate(tcx, def_id)
                        && tcx.def_kind(def_id) == DefKind::Fn
                        && tcx.item_name(def_id).as_str() == "snapshot_capture_select"
                })
        }
        _ => false,
    }
}

/// The trait-method or function call `expr` makes, with the arguments rustc
/// instantiated it at: an operator, a method call, a path call, or a function
/// named as a value.
pub(crate) fn call_instantiation<'tcx>(
    typeck_results: &TypeckResults<'tcx>,
    expr: &Expr<'tcx>,
) -> Option<(DefId, ty::GenericArgs<'tcx>)> {
    match expr.kind {
        ExprKind::Binary(..)
        | ExprKind::AssignOp(..)
        | ExprKind::Unary(..)
        | ExprKind::Index(..)
        | ExprKind::MethodCall(..) => typeck_results
            .type_dependent_def_id(expr.hir_id)
            .map(|def_id| (def_id, typeck_results.node_args(expr.hir_id))),
        ExprKind::Path(_) => match typeck_results.node_type_opt(expr.hir_id)?.kind() {
            TyKind::FnDef(def_id, args) => Some((*def_id, args.skip_binder())),
            _ => None,
        },
        _ => None,
    }
}

/// A trait bound a call asks, with whether only trust-wp-std asked it: the
/// callee's own where-clause, or one reached from it through trust-wp-std's
/// own traits and impls alone.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct AskedBound<'tcx> {
    pub(crate) trait_ref: ty::TraitRef<'tcx>,
    pub(crate) by_trust_wp_std: bool,
}

/// How many bounds one call's elaboration may reach before it is refused
/// rather than read in part.
const ELABORATION_LIMIT: usize = 512;

/// Every trait bound the call asks, as it instantiates them, and every bound
/// the instance must meet to meet those.
///
/// The callee's own where-clauses (a trait method's `Self: Trait` among
/// them), and, where the call resolves to an impl's item, that impl's
/// (`u128::into` selects `impl<T, U: From<T>> Into<U> for T`, whose
/// `Int: From<u128>` runs). Then, for each bound on a type the call fixes:
/// its trait's supertraits (`T: ReadsI32` with `ReadsI32: Deref` asks
/// `Deref`) with the associated-type bounds written beside them (`trait Lends:
/// Src<Out: Borrow<i32>>`, implied for `T: Lends` as a supertrait is), the
/// bounds of its trait's associated types as the instance fixes them
/// (`type Lender: Borrow<i32>` with `Lender = Ghost<Box<i32>>`), and the
/// where-clauses of the impl rustc selects for it (`T: Get` met by
/// `impl<T: Borrow<i32>> Get for T`). A generic body runs on its instance only
/// what these give it, so a ghost or logic type it is handed is asked here or
/// nowhere. A bound on a type parameter or an unnormalized projection is met
/// by the caller's own bounds, which its own callers are asked.
///
/// `Err` names a bound the elaboration could not read through: rustc's
/// selection panicked on it, or the bounds exceeded `ELABORATION_LIMIT`.
pub(crate) fn asked_trait_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    def_id: DefId,
    args: ty::GenericArgs<'tcx>,
) -> Result<Vec<AskedBound<'tcx>>, ty::TraitRef<'tcx>> {
    let by_trust_wp_std = is_trust_wp_std_crate(tcx, def_id);
    let mut work: Vec<AskedBound<'tcx>> = Vec::new();
    let push_clauses = |work: &mut Vec<AskedBound<'tcx>>,
                        clauses: &mut dyn Iterator<Item = ty::Clause<'tcx>>,
                        by_trust_wp_std: bool| {
        for clause in clauses {
            if let Some(pred) = clause.as_trait_clause() {
                work.push(AskedBound {
                    trait_ref: tcx.instantiate_bound_regions_with_erased(
                        pred.map_bound(|pred| pred.trait_ref),
                    ),
                    by_trust_wp_std,
                });
            }
        }
    };
    let predicates_of = |def_id: DefId, args: ty::GenericArgs<'tcx>| {
        tcx.clauses_of(def_id)
            .instantiate(tcx, args)
            .clauses
            .into_iter()
            .map(|clause| clause.skip_norm_wip())
            .collect::<Vec<_>>()
    };
    push_clauses(
        &mut work,
        &mut predicates_of(def_id, args).into_iter(),
        by_trust_wp_std,
    );
    if let Some(trait_id) = tcx.trait_of_assoc(def_id) {
        work.push(AskedBound {
            trait_ref: ty::TraitRef::new_from_args(
                tcx,
                trait_id,
                args.truncate_to(tcx, tcx.generics_of(trait_id)),
            ),
            by_trust_wp_std,
        });
        if !args.has_escaping_bound_vars() {
            // Resolution normalizes and reaches trait selection; a panic
            // there leaves the impl's own bounds unread, so the call is
            // refused.
            let instance = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let args = tcx
                    .try_normalize_erasing_regions(
                        typing_env,
                        rustc_middle::ty::set_aliases_to_non_rigid(tcx, args),
                    )
                    .ok()?;
                ty::Instance::try_resolve(tcx, typing_env, def_id, args)
                    .ok()
                    .flatten()
            }))
            .map_err(|_| {
                ty::TraitRef::new_from_args(
                    tcx,
                    trait_id,
                    args.truncate_to(tcx, tcx.generics_of(trait_id)),
                )
            })?;
            if let Some(instance) = instance {
                if instance.def_id() != def_id {
                    push_clauses(
                        &mut work,
                        &mut predicates_of(instance.def_id(), instance.args).into_iter(),
                        by_trust_wp_std && is_trust_wp_std_crate(tcx, instance.def_id()),
                    );
                }
            }
        }
    }

    elaborate_asked_bounds(tcx, typing_env, work)
}

/// The bounds `work` asks and every bound their instances must meet to meet
/// them: supertraits, associated-type bounds and the where-clauses of the impl
/// rustc selects (`asked_trait_bounds`).
fn elaborate_asked_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    mut work: Vec<AskedBound<'tcx>>,
) -> Result<Vec<AskedBound<'tcx>>, ty::TraitRef<'tcx>> {
    let push_clauses = |work: &mut Vec<AskedBound<'tcx>>,
                        clauses: &mut dyn Iterator<Item = ty::Clause<'tcx>>,
                        by_trust_wp_std: bool| {
        for clause in clauses {
            if let Some(pred) = clause.as_trait_clause() {
                work.push(AskedBound {
                    trait_ref: tcx.instantiate_bound_regions_with_erased(
                        pred.map_bound(|pred| pred.trait_ref),
                    ),
                    by_trust_wp_std,
                });
            }
        }
    };
    let predicates_of = |def_id: DefId, args: ty::GenericArgs<'tcx>| {
        tcx.clauses_of(def_id)
            .instantiate(tcx, args)
            .clauses
            .into_iter()
            .map(|clause| clause.skip_norm_wip())
            .collect::<Vec<_>>()
    };
    let mut seen = std::collections::HashSet::new();
    let mut bounds = Vec::new();
    while let Some(bound) = work.pop() {
        let trait_ref = tcx
            .try_normalize_erasing_regions(
                typing_env,
                rustc_middle::ty::set_aliases_to_non_rigid(tcx, bound.trait_ref),
            )
            .unwrap_or(bound.trait_ref);
        let bound = AskedBound {
            trait_ref,
            by_trust_wp_std: bound.by_trust_wp_std,
        };
        if !seen.insert(bound) {
            continue;
        }
        if seen.len() > ELABORATION_LIMIT {
            return Err(trait_ref);
        }
        bounds.push(bound);
        if matches!(
            trait_ref.self_ty().kind(),
            TyKind::Param(_)
                | TyKind::Alias(..)
                | TyKind::Placeholder(_)
                | TyKind::Bound(..)
                | TyKind::Infer(_)
                | TyKind::Error(_)
        ) || trait_ref.has_escaping_bound_vars()
        {
            continue;
        }
        let through = |item: DefId| bound.by_trust_wp_std && is_trust_wp_std_crate(tcx, item);
        push_clauses(
            &mut work,
            &mut tcx
                .explicit_implied_clauses_of(trait_ref.def_id)
                .iter_instantiated_copied(tcx, trait_ref.args)
                .map(|clause| clause.skip_norm_wip().0),
            through(trait_ref.def_id),
        );
        for item in tcx.associated_items(trait_ref.def_id).in_definition_order() {
            if matches!(item.kind, ty::AssocKind::Type { .. })
                && tcx.generics_of(item.def_id).own_params.is_empty()
            {
                push_clauses(
                    &mut work,
                    &mut tcx
                        .explicit_item_bounds(item.def_id)
                        .iter_instantiated_copied(tcx, trait_ref.args)
                        .map(|clause| clause.skip_norm_wip().0),
                    through(trait_ref.def_id),
                );
            }
        }
        let selected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            match tcx.codegen_select_candidate(typing_env.as_query_input(trait_ref)) {
                Ok(rustc_middle::traits::ImplSource::UserDefined(data)) => {
                    Some((data.impl_def_id, data.args))
                }
                _ => None,
            }
        }))
        .map_err(|_| trait_ref)?;
        if let Some((impl_def_id, impl_args)) = selected {
            push_clauses(
                &mut work,
                &mut predicates_of(impl_def_id, impl_args).into_iter(),
                through(impl_def_id),
            );
        }
    }
    Ok(bounds)
}

/// What a call runs that program code may not: a named trust-wp-std
/// operation whose run-time body is not what the verifier reads, or a bound
/// whose instance could not be read.
pub(crate) enum Divergence<'tcx> {
    Operation(String),
    Unread(ty::TraitRef<'tcx>),
}

/// What the call runs that program code may not; `None` when it runs none.
pub(crate) fn divergent_run_time_operation<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    typeck_results: &TypeckResults<'tcx>,
    expr: &Expr<'tcx>,
) -> Option<Divergence<'tcx>> {
    // A path call is seen at its callee, a function named as a value.
    let (def_id, args) = call_instantiation(typeck_results, expr)?;
    if let Some(name) = divergent_inherent_method(tcx, def_id) {
        return Some(Divergence::Operation(name));
    }
    let bounds = match asked_trait_bounds(tcx, typing_env, def_id, args) {
        Ok(bounds) => bounds,
        Err(trait_ref) => return Some(Divergence::Unread(trait_ref)),
    };
    // trust-wp-std's permission APIs bound their permission by `Borrow`
    // (`PermCell::borrow`'s `P: Borrow<Perm<PermCell<T>>>`, met by a
    // `Ghost<Box<Perm<_>>>`) and never read it at run time; a bound reached
    // through anything of the user's or of std's is asked whatever asked it.
    bounds.into_iter().find_map(|bound| {
        divergent_trait_use(tcx, bound.trait_ref, !bound.by_trust_wp_std).map(Divergence::Operation)
    })
}

/// What an unsizing coercion of `expr` makes runnable that program code may
/// not; `None` when it makes nothing so.
///
/// A coercion to a trait object asks the object's traits of the type it
/// erases, without a call, and a call through the object later runs that
/// type's impls by the vtable: `Box::new(g)` made a `Box<dyn Borrow<i32>>`
/// runs `<Ghost<Box<i32>> as Borrow<i32>>::borrow` at `d.borrow()`, a call
/// whose own self type is `dyn Borrow<i32>`
/// (ghost_unsized_to_dyn_borrow_in_program_context_panics). So the coercion
/// asks them as a call asks its bounds, elaborated alike.
pub(crate) fn divergent_unsize_coercion<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    typeck_results: &TypeckResults<'tcx>,
    expr: &Expr<'tcx>,
) -> Option<Divergence<'tcx>> {
    use rustc_middle::ty::adjustment::{Adjust, PointerCoercion};
    let mut clauses = Vec::new();
    let mut source = typeck_results.expr_ty(expr);
    for adjustment in typeck_results.expr_adjustments(expr) {
        if matches!(adjustment.kind, Adjust::Pointer(PointerCoercion::Unsize)) {
            unsize_trait_clauses(tcx, source, adjustment.target, &mut clauses);
        }
        source = adjustment.target;
    }
    if clauses.is_empty() {
        return None;
    }
    let work = clauses
        .into_iter()
        .filter_map(|clause| clause.as_trait_clause())
        .map(|pred| AskedBound {
            trait_ref: tcx
                .instantiate_bound_regions_with_erased(pred.map_bound(|pred| pred.trait_ref)),
            by_trust_wp_std: false,
        })
        .collect();
    match elaborate_asked_bounds(tcx, typing_env, work) {
        Ok(bounds) => bounds.into_iter().find_map(|bound| {
            divergent_trait_use(tcx, bound.trait_ref, true).map(Divergence::Operation)
        }),
        Err(trait_ref) => Some(Divergence::Unread(trait_ref)),
    }
}

/// The trait clauses unsizing `source` to `target` asks: where `target` holds
/// a trait object at a position `source` holds a type, each of the object's
/// traits with that type as `Self`. Pointers and references are followed to
/// their pointees and an ADT (`Box`, `Rc`, a user's struct with an unsized
/// tail) through its type arguments. A trait object coerced to another
/// (upcasting) asks nothing new: its own coercion asked its traits.
fn unsize_trait_clauses<'tcx>(
    tcx: TyCtxt<'tcx>,
    source: Ty<'tcx>,
    target: Ty<'tcx>,
    out: &mut Vec<ty::Clause<'tcx>>,
) {
    if source == target {
        return;
    }
    match (source.kind(), target.kind()) {
        (TyKind::Dynamic(..), _) => {}
        (_, TyKind::Dynamic(predicates, ..)) => {
            out.extend(
                predicates
                    .iter()
                    .map(|predicate| predicate.with_self_ty(tcx, source)),
            );
        }
        (
            TyKind::Ref(_, source, _) | TyKind::RawPtr(source, _),
            TyKind::Ref(_, target, _) | TyKind::RawPtr(target, _),
        ) => unsize_trait_clauses(tcx, *source, *target, out),
        (TyKind::Adt(source_adt, source_args), TyKind::Adt(target_adt, target_args))
            if source_adt.did() == target_adt.did() =>
        {
            for (source, target) in source_args.types().zip(target_args.types()) {
                unsize_trait_clauses(tcx, source, target, out);
            }
        }
        (TyKind::Tuple(sources), TyKind::Tuple(targets)) => {
            for (source, target) in sources.iter().zip(targets.iter()) {
                unsize_trait_clauses(tcx, source, target, out);
            }
        }
        _ => {}
    }
}

/// An inherent method of trust-wp-std that program code may not run.
///
/// `Snapshot`'s value-building shims (`push_back`, `concat`, `insert`, `set`)
/// return an empty value, since a snapshot carries none: only a capture,
/// `from_fn`, `new_phantom` and `into_ghost` run as the verifier reads them.
/// `Ghost::clone(&self) -> T`, `inner`, `inner_mut` and `into_inner` panic,
/// and a function named as a value runs where it is called
/// (ghost_extraction_named_as_value_in_program_context_panics). A logic type's
/// own methods are logic functions under Creusot, which program code cannot
/// call: `Seq`'s index, `subsequence` and `set` panic out of bounds, and `get`
/// truncates an index past `usize::MAX`; `Int::abs_diff` overflows. The
/// constructors of an empty collection (should_succeed `ghost/ghost_vec.rs`
/// makes its `Seq` in program code, where Creusot's is a ghost), `Int::new` (a
/// ghost) and `Int::try_from_str` are exact.
fn divergent_inherent_method(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    let owner = trust_wp_inherent_owner(tcx, def_id)?;
    let name = tcx.item_name(def_id);
    let divergent = match owner.as_str() {
        "Snapshot" => !matches!(
            name.as_str(),
            "capture" | "from_fn" | "new_phantom" | "into_ghost"
        ),
        "Ghost" => matches!(
            name.as_str(),
            "clone" | "inner" | "inner_mut" | "into_inner"
        ),
        "Int" => !matches!(name.as_str(), "new" | "try_from_str"),
        "Seq" | "FSet" | "FMap" => !matches!(name.as_str(), "new" | "empty"),
        "Mapping" => true,
        _ => false,
    };
    divergent.then(|| format!("{owner}::{name}"))
}

/// A trait bound a call asks whose selected trust-wp-std impl runs a body
/// that is not the logical operation.
///
/// On a `Ghost` or `Snapshot` itself, `Deref`/`DerefMut` and
/// `Borrow`/`BorrowMut` panic (a holder such as `Box<Ghost<T>>` derefs to the
/// ghost without running it). On a logic type, every trait but the
/// structural ones and, for `Int`, the exact conversions: `Int`'s arithmetic
/// is `i128` arithmetic, which overflows and divides by zero where the logic
/// reading owes nothing, and its comparisons with a `u128` convert through a
/// `From<u128>` that panics past `i128::MAX`.
fn divergent_trait_use<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
    asks_ghost_traits: bool,
) -> Option<String> {
    let self_ty = trait_ref.self_ty();
    let trait_name = tcx.item_name(trait_ref.def_id);
    let lang_items = tcx.lang_items();
    let diagnostic = |name: &str| {
        tcx.get_diagnostic_item(rustc_span::Symbol::intern(name)) == Some(trait_ref.def_id)
    };
    let is_ghost = |ty: Ty<'tcx>| {
        matches!(ty.kind(), TyKind::Adt(..)) && type_helpers::is_ghost_like_type(tcx, ty)
    };
    if asks_ghost_traits
        && is_ghost(self_ty)
        && (Some(trait_ref.def_id) == lang_items.deref_trait()
            || Some(trait_ref.def_id) == lang_items.deref_mut_trait()
            || diagnostic("Borrow")
            || diagnostic("BorrowMut"))
    {
        return Some(format!("<{self_ty} as {trait_name}>"));
    }
    let logic_types = trait_ref
        .args
        .types()
        .filter(|ty| is_logic_adt(tcx, *ty))
        .collect::<Vec<_>>();
    if logic_types.is_empty() {
        return None;
    }
    // A trait with no method runs nothing (`Sized`, `Copy`, an auto trait);
    // its supertraits are asked as bounds of their own (`asked_trait_bounds`).
    // `Clone`, `Debug`, `Hash`, `Default`, `Eq` (whose one method asserts
    // nothing) and `Ord` run a logic type's structural impls, which are exact.
    let runs_nothing = !tcx
        .associated_items(trait_ref.def_id)
        .in_definition_order()
        .any(|item| matches!(item.kind, ty::AssocKind::Fn { .. }));
    let structural = runs_nothing
        || Some(trait_ref.def_id) == lang_items.clone_trait()
        || ["Debug", "Hash", "Default", "Eq", "Ord"]
            .iter()
            .any(|name| diagnostic(name));
    if structural {
        return None;
    }
    // A comparison between two values of one logic type compares their
    // run-time representations, which are exact.
    let same_type_comparison = (Some(trait_ref.def_id) == lang_items.eq_trait()
        || Some(trait_ref.def_id) == lang_items.partial_ord_trait())
        && trait_ref.args.types().all(|ty| ty == self_ty);
    if same_type_comparison {
        return None;
    }
    // `Int::from` of a machine integer of at most 64 bits, or of an `i128`,
    // is that integer.
    if diagnostic("From") && is_int(tcx, self_ty) {
        let source = trait_ref.args.type_at(1);
        if matches!(
            source.kind(),
            TyKind::Int(_)
                | TyKind::Uint(
                    ty::UintTy::U8
                        | ty::UintTy::U16
                        | ty::UintTy::U32
                        | ty::UintTy::U64
                        | ty::UintTy::Usize
                )
        ) {
            return None;
        }
    }
    Some(format!(
        "<{self_ty} as {}>",
        tcx.def_path_str(trait_ref.def_id)
    ))
}

/// `Int`, `Seq`, `FSet`, `FMap` or `Mapping` of trust-wp-std, or a reference
/// to one: the types whose operations are logic functions under Creusot.
fn is_logic_adt(tcx: TyCtxt<'_>, ty: Ty<'_>) -> bool {
    matches!(ty.peel_refs().kind(), TyKind::Adt(..))
        && type_helpers::is_trust_wp_logic_type(tcx, ty)
}

fn is_int(tcx: TyCtxt<'_>, ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Adt(adt, _) => {
            is_trust_wp_std_crate(tcx, adt.did()) && tcx.item_name(adt.did()).as_str() == "Int"
        }
        _ => false,
    }
}
