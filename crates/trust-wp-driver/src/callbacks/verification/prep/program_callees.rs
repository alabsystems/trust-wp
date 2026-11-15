// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The crate's program functions a logic body must not call
//! (`logic_fn_verify::callee_preconditions`).

use std::collections::HashSet;

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{AssocContainer, TyCtxt, TyKind};

use super::super::{
    super::super::contracts::{FunctionContract, TraitMethodContract},
    logic_fn_verify::ProgramFnsWithRequires,
};

/// The crate's program functions that carry a `#[requires]`, their own or a
/// trait declaration's, by every name a logic body could call one by and by
/// `DefId` (`logic_body_callees`). A logic function is never one of them:
/// `logic_fn_paths` holds every logic function's paths.
pub(super) fn program_fns_with_requires(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
    trait_contracts: &[TraitMethodContract],
    logic_fn_paths: &HashSet<String>,
) -> (ProgramFnsWithRequires, HashSet<DefId>) {
    let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE);
    let mut fns = ProgramFnsWithRequires::default();
    let mut def_ids = HashSet::new();
    let with_requires = contracts
        .iter()
        .filter(|contract| !contract.requires.is_empty())
        .map(|contract| contract.def_id)
        .chain(
            trait_contracts
                .iter()
                .filter(|contract| !contract.requires.is_empty())
                .map(|contract| contract.method_def_id),
        );
    for def_id in with_requires {
        if tcx.def_kind(def_id) == DefKind::Closure {
            continue;
        }
        let relative = tcx.def_path_str(def_id);
        let full = format!("{crate_name}::{relative}");
        if logic_fn_paths.contains(&full) || logic_fn_paths.contains(&relative) {
            continue;
        }
        let name = tcx.item_name(def_id).to_string();
        match tcx.opt_associated_item(def_id) {
            Some(assoc) => {
                let container = tcx.parent(def_id);
                let mut owners = Vec::new();
                match assoc.container {
                    AssocContainer::Trait => owners.push(container),
                    AssocContainer::TraitImpl(_) => {
                        owners.extend(tcx.impl_opt_trait_id(container));
                        owners.extend(impl_self_adt(tcx, container));
                    }
                    AssocContainer::InherentImpl => {
                        owners.extend(impl_self_adt(tcx, container));
                    }
                }
                for owner in owners {
                    fns.insert_associated(tcx.item_name(owner).as_str(), &name);
                }
            }
            None => fns.insert_free(name),
        }
        fns.insert_path(full);
        fns.insert_path(relative);
        def_ids.insert(def_id);
    }
    (fns, def_ids)
}

/// The ADT an impl block is for, when it is one.
fn impl_self_adt(tcx: TyCtxt<'_>, impl_id: DefId) -> Option<DefId> {
    match tcx
        .type_of(impl_id)
        .instantiate_identity()
        .skip_norm_wip()
        .kind()
    {
        TyKind::Adt(adt, _) => Some(adt.did()),
        _ => None,
    }
}
