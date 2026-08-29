// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type invariant analysis and trait contract handling.
//!
//! Cluster C: invariant-bearing signature detection and recursive type analysis.
//! Cluster D: trait contract discovery, inheritance, and refinement overrides.

use std::collections::{HashMap, HashSet};

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{TyCtxt, TyKind};

use super::super::super::{
    attr_utils::get_contract_attrs_from_doc,
    contracts::{FunctionContract, TraitMethodContract},
};

/// Check if a function signature is invariant-bearing.
///
/// A type is invariant-bearing when either:
/// - it has an explicit `impl Invariant for T` body, or
/// - it structurally contains a type with an explicit invariant body.
///
/// This allows discovery of wrapper/container APIs whose safety depends on
/// inner invariant types (e.g. enums/tuples containing `&mut Sum10`).
pub(in crate::callbacks) fn has_invariant_bearing_signature(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    invariant_type_names: &HashSet<&str>,
) -> bool {
    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();

    for ty in sig.inputs() {
        if type_has_invariant(tcx, *ty, invariant_type_names) {
            return true;
        }
    }

    type_has_invariant(tcx, sig.output(), invariant_type_names)
}

/// Check if a type has (or transitively contains) an explicit type invariant.
fn type_has_invariant<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    invariant_type_names: &HashSet<&str>,
) -> bool {
    let mut visiting = HashSet::new();
    type_has_invariant_inner(tcx, ty, invariant_type_names, &mut visiting)
}

fn type_has_invariant_inner<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    invariant_type_names: &HashSet<&str>,
    visiting: &mut HashSet<String>,
) -> bool {
    let inner = match ty.kind() {
        TyKind::Ref(_, inner, _) => *inner,
        _ => ty,
    };

    match inner.kind() {
        TyKind::Adt(adt_def, substs) => {
            // Fast path: explicit invariant body for this ADT.
            // `def_path_str` returns unqualified names for local items (e.g.,
            // "NonZeroU32"), but `invariant_type_names` may contain crate-qualified
            // names (e.g., "creusot_test::NonZeroU32"). Check both forms. (#2341)
            let type_path = tcx.def_path_str(adt_def.did());
            let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE);
            let qualified_type_path = format!("{crate_name}::{type_path}");
            if invariant_type_names.contains(type_path.as_str())
                || invariant_type_names.contains(qualified_type_path.as_str())
            {
                return true;
            }

            // Guard against recursive ADTs.
            let visit_key = inner.to_string();
            if !visiting.insert(visit_key.clone()) {
                return false;
            }

            // Propagate through instantiated generic arguments.
            if substs
                .types()
                .any(|arg_ty| type_has_invariant_inner(tcx, arg_ty, invariant_type_names, visiting))
            {
                visiting.remove(&visit_key);
                return true;
            }

            // Propagate through concrete fields for local wrapper enums/structs.
            let contains_invariant = adt_def.variants().iter().any(|variant| {
                variant.fields.iter().any(|field| {
                    let field_ty = field.ty(tcx, substs).skip_norm_wip();
                    type_has_invariant_inner(tcx, field_ty, invariant_type_names, visiting)
                })
            });

            visiting.remove(&visit_key);
            contains_invariant
        }
        TyKind::Tuple(fields) => fields
            .iter()
            .any(|elem| type_has_invariant_inner(tcx, elem, invariant_type_names, visiting)),
        TyKind::Array(elem, _) | TyKind::Slice(elem) => {
            type_has_invariant_inner(tcx, *elem, invariant_type_names, visiting)
        }
        _ => false,
    }
}

/// Discover contracts declared on trait method signatures.
///
/// Iterates over all locally-defined traits and their associated methods.
/// For each method with `#[requires]`/`#[ensures]` doc markers, a
/// `TraitMethodContract` is returned. These are used later for contract
/// inheritance (impl methods without contracts inherit from their trait).
pub(in crate::callbacks) fn find_trait_contracts(tcx: TyCtxt<'_>) -> Vec<TraitMethodContract> {
    let mut contracts = Vec::new();

    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();

        if tcx.def_kind(def_id) != DefKind::Trait {
            continue;
        }

        let trait_path = tcx.def_path_str(def_id);

        // Iterate over associated items of the trait
        for assoc_item in tcx.associated_items(def_id).in_definition_order() {
            // Only consider methods (skip associated types and consts)
            if tcx.def_kind(assoc_item.def_id) != DefKind::AssocFn {
                continue;
            }

            let method_id = assoc_item.def_id;
            let attrs = tcx.get_all_attrs(method_id);
            let requires = get_contract_attrs_from_doc(attrs, "requires");
            let ensures = get_contract_attrs_from_doc(attrs, "ensures");

            if requires.is_empty() && ensures.is_empty() {
                continue;
            }

            contracts.push(TraitMethodContract {
                trait_def_id: def_id,
                method_def_id: method_id,
                method_name: assoc_item.name().to_string(),
                trait_path: trait_path.clone(),
                requires,
                ensures,
            });
        }
    }

    contracts
}

/// Apply contract inheritance: impl methods without contracts inherit from their trait.
///
/// For each function contract with a `trait_origin` but no requires/ensures of its own,
/// look up the trait's contracts and copy them. This enables trait-based specification
/// where the trait declares the contract and impls inherit it.
pub(in crate::callbacks) fn apply_trait_contract_inheritance(
    contracts: &mut [FunctionContract],
    trait_contracts: &[TraitMethodContract],
) {
    // Index trait contracts once so per-contract lookup is O(1) instead of
    // scanning every trait method contract for each impl method.
    let mut trait_contract_index: HashMap<DefId, HashMap<&str, &TraitMethodContract>> =
        HashMap::new();
    for trait_contract in trait_contracts {
        trait_contract_index
            .entry(trait_contract.trait_def_id)
            .or_default()
            .insert(trait_contract.method_name.as_str(), trait_contract);
    }

    for contract in contracts.iter_mut() {
        // Skip if already has contracts
        if !contract.requires.is_empty() || !contract.ensures.is_empty() {
            continue;
        }

        // Check if this is a trait impl method
        let Some(ref origin) = contract.trait_origin else {
            continue;
        };

        // Find matching trait contract in the pre-built index.
        if let Some(trait_contract) = trait_contract_index
            .get(&origin.trait_def_id)
            .and_then(|methods| methods.get(origin.trait_method_name.as_str()))
        {
            contract.requires = trait_contract.requires.clone();
            contract.ensures = trait_contract.ensures.clone();
        }
    }
}

/// Find impl methods that explicitly override trait contracts.
///
/// Refinement obligations are needed only when an impl provides its own
/// `#[requires]` or `#[ensures]`; inherited trait contracts are skipped.
pub(in crate::callbacks) fn find_trait_refinement_overrides(
    contracts: &[FunctionContract],
) -> HashSet<DefId> {
    contracts
        .iter()
        .filter(|contract| {
            contract.trait_origin.is_some()
                && (!contract.requires.is_empty() || !contract.ensures.is_empty())
        })
        .map(|contract| contract.def_id)
        .collect()
}
