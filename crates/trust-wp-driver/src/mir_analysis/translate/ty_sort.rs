// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MIR Type -> ExprSort conversion (#717).

use rustc_middle::ty::{Mutability, TyKind, TypeVisitableExt, TypingEnv};
use trust_wp_core::formula::{intern_sort_name, ExprSort};

const PREDCELL_SLICE_SORT: &str = "trust_wp_internal::PredCellSlice";

/// Convert a MIR type to an `ExprSort` annotation.
///
/// Returns `Some(ExprSort::Bool)` for boolean types, `Some(ExprSort::Int)` for
/// integer types, `Some(ExprSort::Tuple(arity))` for tuple types,
/// `Some(ExprSort::Ref(inner))` / `Some(ExprSort::MutRef(inner))` for
/// reference types, `Some(ExprSort::Unit)` for
/// the unit type, and `None` for types that don't have a direct ExprSort mapping
/// without `TyCtxt` (ADTs, closures, etc.). `None` preserves backward compatibility
/// by falling back to the encoder's sort inference.
///
/// For ADT sort annotations, use `ty_to_expr_sort_enriched` which accepts `TyCtxt`.
pub(crate) fn ty_to_expr_sort(ty: rustc_middle::ty::Ty<'_>) -> Option<ExprSort> {
    match ty.kind() {
        TyKind::Bool => Some(ExprSort::Bool),
        TyKind::Int(_) | TyKind::Uint(_) | TyKind::Char => Some(ExprSort::Int),
        TyKind::Tuple(fields) if fields.is_empty() => Some(ExprSort::Unit),
        TyKind::Tuple(fields) => {
            // Truncation is safe: Rust tuples have arity <= 12 in practice.
            #[allow(clippy::cast_possible_truncation)]
            Some(ExprSort::Tuple(fields.len() as u8))
        }
        TyKind::Ref(_, inner, mutability) => ty_to_expr_sort(*inner).map(|s| match mutability {
            Mutability::Mut => ExprSort::MutRef(Box::new(s)),
            Mutability::Not => ExprSort::Ref(Box::new(s)),
        }),
        // Generic type parameter → opaque uninterpreted sort. Prevents collapse
        // to Int which causes sort_fallback demotions and silent unsoundness. (#2062)
        TyKind::Param(param) => Some(ExprSort::TypeParam(intern_sort_name(param.name.as_str()))),
        // Float types → SMT Real (exact rational arithmetic, no IEEE 754). (#1802)
        TyKind::Float(_) => Some(ExprSort::Float),
        // `dyn Trait` types → opaque uninterpreted sort. Without `TyCtxt` we
        // cannot resolve the principal trait name, so use a generic placeholder.
        // This prevents sort_fallback_to_int (SortFallbackToInt unsoundness)
        // which would silently assign Int to trait-object values. (#2685)
        TyKind::Dynamic(..) => Some(ExprSort::Datatype(intern_sort_name("dyn"))),
        // The never type `!` is uninhabited — any value of type `!` is vacuously
        // true. Map to Unit (zero-sized) since no runtime value exists. (#2685)
        TyKind::Never => Some(ExprSort::Unit),
        // Seq sort is not inferred from Rust types here because Vec<T>/Slice
        // become Seq only after View (@) application in contracts, not at the
        // MIR level. The encoder's existing View/Seq inference handles this.
        _ => None,
    }
}

fn is_predcell_ty<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    let TyKind::Adt(adt_def, _) = ty.kind() else {
        return false;
    };
    tcx.def_path_str(adt_def.did())
        .rsplit("::")
        .next()
        .is_some_and(|name| name == "PredCell")
}

fn predcell_collection_sort<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<ExprSort> {
    match ty.kind() {
        TyKind::Slice(inner) | TyKind::Array(inner, _) if is_predcell_ty(tcx, *inner) => {
            Some(ExprSort::Datatype(intern_sort_name(PREDCELL_SLICE_SORT)))
        }
        _ => None,
    }
}

fn transparent_wrapper_inner_sort<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    adt_def: rustc_middle::ty::AdtDef<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
) -> Option<ExprSort> {
    if adt_def.is_box() {
        let inner_ty = substs.types().next()?;
        return ty_to_expr_sort_enriched(tcx, inner_ty);
    }

    let crate_name = tcx.crate_name(def_id.krate).to_string();
    let def_path = tcx.def_path_str(def_id);
    let is_transparent_wrapper = matches!(
        (crate_name.as_str(), def_path.as_str()),
        (
            "trust_wp_std",
            "trust_wp_std::ghost::Ghost"
                | "trust_wp_std::ghost::Snapshot"
                | "trust_wp_std::Ghost"
                | "trust_wp_std::Snapshot"
                | "creusot_std::Ghost"
                | "creusot_std::Snapshot"
                | "ghost::Ghost"
                | "ghost::Snapshot"
        ) | (
            "trust-wp",
            "trust_wp::Ghost" | "trust_wp::Snapshot" | "Ghost" | "Snapshot"
        ) | (
            "creusot_std",
            "creusot_std::ghost::Ghost"
                | "creusot_std::ghost::Snapshot"
                | "creusot_std::Ghost"
                | "creusot_std::Snapshot"
                | "ghost::Ghost"
                | "ghost::Snapshot"
        ) | (
            "creusot_contracts",
            "creusot_contracts::Ghost"
                | "creusot_contracts::Snapshot"
                | "creusot_contracts::ghost::Ghost"
                | "creusot_contracts::ghost::Snapshot"
        )
    );
    if !is_transparent_wrapper {
        return None;
    }

    let inner_ty = substs.types().next()?;
    ty_to_expr_sort_enriched(tcx, inner_ty)
}

/// #prophecy-slots (Fix B M2): the payload `ExprSort` of an `Option` whose
/// payload embeds a mutable reference — the two shapes this campaign lowers to
/// real prophecy carriers.
///
/// * `Option<&mut T>` (M1): the payload IS a mutable reference.
/// * `Option<(&mut T, ..)>` (M2): the payload is a TUPLE with at least one
///   `&mut` element — the `split_first_mut` / take_first_mut sibling-binder
///   shape. The carrier tuple sort names each element, so the positional
///   getters are declared per instantiation with the mutref record sort as
///   their range instead of the punned `Tuple{n}` / `Int` pair.
///
/// Deeper embeddings (`Option<S<&mut T>>`, `Option<(S<&mut T>,)>`) return
/// `None` and stay fail-closed under the Fix A guard: this milestone lowers
/// only what it can lower exactly.
fn mutref_option_payload_sort<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    payload_ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<ExprSort> {
    match payload_ty.kind() {
        TyKind::Ref(_, _, Mutability::Mut) => match ty_to_expr_sort_enriched(tcx, payload_ty) {
            Some(sort @ ExprSort::MutRef(_)) => Some(sort),
            _ => None,
        },
        TyKind::Tuple(fields) if !fields.is_empty() => {
            let elements = fields
                .iter()
                .map(|field_ty| match field_ty.kind() {
                    TyKind::Ref(_, _, Mutability::Mut) => {
                        match ty_to_expr_sort_enriched(tcx, field_ty) {
                            // An element whose referent sort the driver cannot
                            // resolve (e.g. `&mut [T]`, whose slice referent has
                            // no `ExprSort`) is recorded as `legacy`, NOT guessed
                            // at: it keeps today's inference and today's
                            // fail-closed treatment.
                            sort @ Some(ExprSort::MutRef(_)) => sort,
                            _ => None,
                        }
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            trust_wp_ay::mutref_carrier_tuple_sort_name(&elements)
                .map(|name| ExprSort::Datatype(intern_sort_name(&name)))
        }
        _ => None,
    }
}

/// Enriched MIR type to `ExprSort` conversion with `TyCtxt` for ADT name resolution.
///
/// Extends `ty_to_expr_sort` with `ExprSort::Datatype(id)` for algebraic data types.
/// Use this variant at call sites where `TyCtxt` is available for richer sort annotations.
pub(crate) fn ty_to_expr_sort_enriched<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<ExprSort> {
    if let Some(sort) = predcell_collection_sort(tcx, ty) {
        return Some(sort);
    }
    match ty.kind() {
        TyKind::Adt(adt_def, substs) => {
            if let Some(inner_sort) =
                transparent_wrapper_inner_sort(tcx, *adt_def, adt_def.did(), substs)
            {
                return Some(inner_sort);
            }
            let name = tcx.def_path_str(adt_def.did());
            // #prophecy-slots (Fix B M1, blueprint C2): instantiation-aware
            // annotation names for `Option<&mut T>`. `Option<&mut i32>` must
            // be a DIFFERENT `ExprSort` from `Option<i32>` — with the plain
            // path name, the `&mut`-ness is invisible above the ADT and the
            // encoder collapses the payload to the same sort as a plain
            // payload (the take_first_mut inversion class). The suffixed name
            // resolves ay-side to the specialized carrier Option family whose
            // `Some` field sits at the mutref record sort. Scoped to a
            // payload that IS a mutable reference at the top: deeper
            // embeddings (e.g. `Option<S<&mut T>>`) keep the legacy name and
            // stay fail-closed under the Fix A guard. ADTs embedding no
            // `&mut` keep byte-identical names — zero churn on the passing
            // corpus.
            if matches!(
                name.as_str(),
                "std::option::Option" | "core::option::Option"
            ) {
                if let Some(payload_ty) = substs.types().next() {
                    if let Some(payload_sort) = mutref_option_payload_sort(tcx, payload_ty) {
                        return Some(ExprSort::Datatype(intern_sort_name(
                            &trust_wp_ay::mutref_instantiated_option_name(&name, &payload_sort),
                        )));
                    }
                }
            }
            Some(ExprSort::Datatype(intern_sort_name(&name)))
        }
        TyKind::Ref(_, inner, mutability) => {
            // Use enriched version for inner type to capture ADTs through refs.
            ty_to_expr_sort_enriched(tcx, *inner).map(|s| match mutability {
                Mutability::Mut => ExprSort::MutRef(Box::new(s)),
                Mutability::Not => ExprSort::Ref(Box::new(s)),
            })
        }
        // `dyn Trait` types → opaque Datatype sort named after the principal trait.
        // With `TyCtxt` available we can resolve the trait name for a more
        // precise sort annotation (e.g., `Datatype(dyn std::fmt::Debug)` rather
        // than the generic `Datatype(dyn)` from the base function). (#2685)
        TyKind::Dynamic(predicates, _) => {
            let sort_name = predicates
                .principal_def_id()
                .map(|def_id| format!("dyn {}", tcx.def_path_str(def_id)))
                .unwrap_or_else(|| "dyn".to_string());
            Some(ExprSort::Datatype(intern_sort_name(&sort_name)))
        }
        // Normalize associated type projections (e.g., `<() as Tr>::A` → `()`)
        // before falling through to a generic type-parameter carrier. Without
        // an explicit annotation, generic associated types such as
        // `K::DeepModelTy` return `None` and later trigger
        // sort_fallback_to_int demotions in the encoder. (#2670)
        TyKind::Alias(_, alias_ty) => {
            if ty.has_non_region_param() {
                if alias_ty
                    .args
                    .iter()
                    .find_map(|arg| arg.as_type())
                    .is_some_and(|self_ty| matches!(self_ty.kind(), TyKind::Param(_)))
                {
                    return Some(ExprSort::TypeParam(intern_sort_name(&ty.to_string())));
                }
                return ty_to_expr_sort(ty);
            }
            match tcx.try_normalize_erasing_regions(
                TypingEnv::fully_monomorphized(),
                rustc_middle::ty::Unnormalized::new_wip(ty),
            ) {
                Ok(norm_ty) if norm_ty != ty => ty_to_expr_sort_enriched(tcx, norm_ty),
                _ => Some(ExprSort::TypeParam(intern_sort_name(&ty.to_string()))),
            }
        }
        // Fall through to base implementation for non-ADT types.
        _ => ty_to_expr_sort(ty),
    }
}
