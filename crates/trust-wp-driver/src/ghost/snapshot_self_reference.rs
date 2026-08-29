// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type-level rejection for recursive `Snapshot<&mut T>` shapes.
//!
//! `tests/should_fail/bug/436_2.rs` is a known false-accept because the driver
//! currently allows self-referential snapshot borrows to reach proof_assert
//! reasoning. Creusot rejects these shapes at type level. This module adds the
//! corresponding driver-side guard.

use std::collections::HashSet;

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LOCAL_CRATE},
};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::GhostValidationError;

pub(crate) fn check_snapshot_self_references(tcx: TyCtxt<'_>) -> Vec<GhostValidationError> {
    let local_crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
    if matches!(
        local_crate_name.as_str(),
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts" | "trust_wp_lib"
    ) {
        return Vec::new();
    }

    let mut errors = Vec::new();

    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        if !matches!(
            tcx.def_kind(def_id),
            DefKind::Struct | DefKind::Enum | DefKind::Union
        ) {
            continue;
        }

        let root_ty = tcx.type_of(def_id).instantiate_identity().skip_norm_wip();
        if !has_recursive_snapshot_mut_borrow(tcx, def_id, root_ty) {
            continue;
        }

        let def_path = tcx.def_path_str(def_id);
        errors.push(GhostValidationError {
            span: tcx.def_span(def_id),
            message: format!(
                "snapshot self-reference: type `{def_path}` contains `Snapshot<&mut T>` \
                 where `T` transitively contains `{def_path}`. Self-referential \
                 Snapshot mutable borrows are rejected because they permit \
                 circular snapshot reasoning."
            ),
        });
    }

    errors
}

fn has_recursive_snapshot_mut_borrow<'tcx>(
    tcx: TyCtxt<'tcx>,
    root_def_id: DefId,
    ty: Ty<'tcx>,
) -> bool {
    let mut visiting = HashSet::new();
    has_recursive_snapshot_mut_borrow_inner(tcx, root_def_id, ty, &mut visiting)
}

fn has_recursive_snapshot_mut_borrow_inner<'tcx>(
    tcx: TyCtxt<'tcx>,
    root_def_id: DefId,
    ty: Ty<'tcx>,
    visiting: &mut HashSet<String>,
) -> bool {
    let visit_key = ty.to_string();
    if !visiting.insert(visit_key.clone()) {
        return false;
    }

    let found = match ty.kind() {
        TyKind::Ref(_, inner, _) => {
            has_recursive_snapshot_mut_borrow_inner(tcx, root_def_id, *inner, visiting)
        }
        TyKind::Adt(adt_def, substs) => {
            let snapshot_hit = is_snapshot_adt(tcx, adt_def.did())
                && substs.types().next().is_some_and(|arg_ty| {
                    matches!(
                        arg_ty.kind(),
                        TyKind::Ref(_, referent, rustc_middle::ty::Mutability::Mut)
                            if type_contains_adt_def(tcx, *referent, root_def_id)
                    )
                });

            snapshot_hit
                || substs.types().any(|arg_ty| {
                    has_recursive_snapshot_mut_borrow_inner(tcx, root_def_id, arg_ty, visiting)
                })
                || adt_def.variants().iter().any(|variant| {
                    variant.fields.iter().any(|field| {
                        let field_ty = field.ty(tcx, substs).skip_norm_wip();
                        has_recursive_snapshot_mut_borrow_inner(
                            tcx,
                            root_def_id,
                            field_ty,
                            visiting,
                        )
                    })
                })
        }
        TyKind::Tuple(fields) => fields.iter().any(|field_ty| {
            has_recursive_snapshot_mut_borrow_inner(tcx, root_def_id, field_ty, visiting)
        }),
        TyKind::Array(elem, _) | TyKind::Slice(elem) => {
            has_recursive_snapshot_mut_borrow_inner(tcx, root_def_id, *elem, visiting)
        }
        _ => false,
    };

    visiting.remove(&visit_key);
    found
}

fn type_contains_adt_def<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, root_def_id: DefId) -> bool {
    let mut visiting = HashSet::new();
    type_contains_adt_def_inner(tcx, ty, root_def_id, &mut visiting)
}

fn type_contains_adt_def_inner<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    root_def_id: DefId,
    visiting: &mut HashSet<String>,
) -> bool {
    let visit_key = ty.to_string();
    if !visiting.insert(visit_key.clone()) {
        return false;
    }

    let contains = match ty.kind() {
        TyKind::Ref(_, inner, _) => type_contains_adt_def_inner(tcx, *inner, root_def_id, visiting),
        TyKind::Adt(adt_def, substs) => {
            adt_def.did() == root_def_id
                || substs
                    .types()
                    .any(|arg_ty| type_contains_adt_def_inner(tcx, arg_ty, root_def_id, visiting))
                || adt_def.variants().iter().any(|variant| {
                    variant.fields.iter().any(|field| {
                        let field_ty = field.ty(tcx, substs).skip_norm_wip();
                        type_contains_adt_def_inner(tcx, field_ty, root_def_id, visiting)
                    })
                })
        }
        TyKind::Tuple(fields) => fields
            .iter()
            .any(|field_ty| type_contains_adt_def_inner(tcx, field_ty, root_def_id, visiting)),
        TyKind::Array(elem, _) | TyKind::Slice(elem) => {
            type_contains_adt_def_inner(tcx, *elem, root_def_id, visiting)
        }
        _ => false,
    };

    visiting.remove(&visit_key);
    contains
}

fn is_snapshot_adt(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let crate_name = tcx.crate_name(def_id.krate).to_string();
    let def_path = tcx.def_path_str(def_id);

    matches!(
        (crate_name.as_str(), def_path.as_str()),
        (
            "trust_wp_std",
            "trust_wp_std::ghost::Snapshot"
                | "trust_wp_std::Snapshot"
                | "creusot_std::Snapshot"
                | "ghost::Snapshot"
        ) | ("trust-wp", "trust_wp::Snapshot" | "Snapshot")
            | (
                "creusot_std",
                "creusot_std::ghost::Snapshot" | "creusot_std::Snapshot" | "ghost::Snapshot"
            )
            | (
                "creusot_contracts",
                "creusot_contracts::Snapshot" | "creusot_contracts::ghost::Snapshot"
            )
    )
}
