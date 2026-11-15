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
pub(super) fn type_has_invariant<'tcx>(
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
                    let field_ty = field.ty(tcx, *substs).skip_norm_wip();
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
            let mut requires = get_contract_attrs_from_doc(attrs, "requires");
            let mut ensures = get_contract_attrs_from_doc(attrs, "ensures");

            if requires.is_empty() && ensures.is_empty() {
                continue;
            }
            // D-177: a default body's parameter patterns, as for any function;
            // D-179: a positional name the method has no parameter of; D-181: a
            // `&mut` a parameter holds, read in a postcondition.
            if let Some(local) = method_id.as_local() {
                crate::param_patterns::destructure_contract_clauses(
                    tcx,
                    local,
                    "requires",
                    &mut requires,
                );
                crate::param_patterns::destructure_contract_clauses(
                    tcx,
                    local,
                    "ensures",
                    &mut ensures,
                );
                crate::param_patterns::refuse_positional_alias_collisions(
                    tcx,
                    local,
                    "requires",
                    &mut requires,
                );
                crate::param_patterns::refuse_positional_alias_collisions(
                    tcx,
                    local,
                    "ensures",
                    &mut ensures,
                );
                crate::param_patterns::refuse_unplaced_held_mut_param_reads(
                    tcx,
                    local,
                    "ensures",
                    &mut ensures,
                );
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
        let Some(ref mut origin) = contract.trait_origin else {
            continue;
        };

        // Find matching trait contract in the pre-built index.
        if let Some(trait_contract) = trait_contract_index
            .get(&origin.trait_def_id)
            .and_then(|methods| methods.get(origin.trait_method_name.as_str()))
        {
            origin.inherits_clauses = true;
            contract.requires = trait_contract.requires.clone();
            contract.ensures = trait_contract.ensures.clone();
        }
    }
}

/// Restate every inherited contract as the trait method's call-site spec,
/// instantiated at the impl.
///
/// The text `apply_trait_contract_inheritance` copies is the trait's, but an
/// impl's body obligation resolves its clauses in the IMPL's scope, while
/// every caller is handed the trait method's spec resolved in the TRAIT's
/// scope (`resolve_spec_table_texts`). Where a name means different things in
/// the two modules (`k()` is `a::k` in the trait's and `b::k` in the impl's),
/// the body proved one contract and callers were granted another. Here the
/// impl's clauses become the granted text itself: resolved in the trait's
/// scope, with every generic marker instantiated at the impl's own view of
/// the trait method's generic arguments, exactly as a call pinned to this
/// impl instantiates it. Names the trait-scope resolution left for the
/// encoder to refuse stay refused on both sides.
///
/// Runs once the identity registry is installed and `trait_specs` is
/// resolved. The granted text names the trait's parameters and the body reads
/// its own, so each clause is renamed position by position
/// (`rename_inherited_params`); a clause that cannot be renamed faithfully is
/// replaced by one the encoder refuses, and the impl discharges nothing.
pub(in crate::callbacks) fn restate_inherited_clauses(
    tcx: TyCtxt<'_>,
    contracts: &mut [FunctionContract],
    trait_specs: &HashMap<DefId, trust_wp_driver::StdSpec>,
) {
    for contract in contracts.iter_mut() {
        if !contract
            .trait_origin
            .as_ref()
            .is_some_and(|origin| origin.inherits_clauses)
        {
            continue;
        }
        let Some(trait_method) = tcx
            .opt_associated_item(contract.def_id)
            .and_then(|assoc| assoc.trait_item_def_id())
        else {
            continue;
        };
        let Some(spec) = trait_specs.get(&trait_method) else {
            continue;
        };
        let Some(impl_id) = tcx
            .opt_parent(contract.def_id)
            .filter(|parent| matches!(tcx.def_kind(*parent), DefKind::Impl { of_trait: true }))
        else {
            continue;
        };
        let trait_ref_args = tcx.impl_trait_ref(impl_id).skip_binder().args;
        let args_at_impl = rustc_middle::ty::GenericArgs::identity_for_item(tcx, contract.def_id)
            .rebase_onto(tcx, impl_id, trait_ref_args);
        let restated = crate::logic::identity_typed::instantiate_generic_markers(
            tcx,
            contract.def_id,
            trait_method,
            args_at_impl,
            spec,
        );
        let spec = restated.as_ref().unwrap_or(spec);
        // The granted text names the TRAIT's parameters; the body reads names
        // by its own. Positional renaming, or a clause no body can discharge.
        let renames = inherited_param_renames(tcx, trait_method, contract.def_id);
        let restate = |clauses: &[String]| -> Option<Vec<String>> {
            clauses
                .iter()
                .map(|clause| rename_inherited_params(clause, &renames))
                .collect()
        };
        match (restate(&spec.requires), restate(&spec.ensures)) {
            (Some(requires), Some(ensures)) => {
                contract.requires = requires;
                contract.ensures = ensures;
            }
            _ => {
                eprintln!(
                    "trust-wp: {} error: the contract it inherits from `{}` names parameters \
                     this impl renames, and it cannot be restated in the impl's names",
                    tcx.def_path_str(contract.def_id),
                    tcx.def_path_str(trait_method)
                );
                // Refused by the encoder wherever it is read: the body owes a
                // contract nobody can state, so it discharges nothing.
                let refused = format!(
                    "{}()",
                    trust_wp_core::logic::identity::logic_fn_unresolved_marker("inherited_clause")
                );
                contract.requires = vec![refused.clone()];
                contract.ensures = vec![refused];
            }
        }
    }
}

/// Trait parameter name -> impl parameter name, for every position where
/// they differ. Empty when either side's names are unavailable or the
/// arities differ (nothing is renamed; the refinement check refuses such an
/// impl on its own).
pub(in crate::callbacks) fn inherited_param_renames(
    tcx: TyCtxt<'_>,
    trait_method: DefId,
    impl_item: DefId,
) -> Vec<(String, String)> {
    use super::super::parsing::get_arg_names_from_def_id;
    let (Some(trait_names), Some(impl_names)) = (
        get_arg_names_from_def_id(tcx, trait_method),
        get_arg_names_from_def_id(tcx, impl_item),
    ) else {
        return Vec::new();
    };
    if trait_names.len() != impl_names.len() {
        return Vec::new();
    }
    trait_names
        .into_iter()
        .zip(impl_names)
        .filter(|(from, to)| from != to)
        .collect()
}

/// `clause` with every parameter name in `renames` replaced, simultaneously,
/// by the impl's name at the same position. `None` unless the result parses
/// to exactly the capture-avoiding substitution of the original's parse: a
/// textual rename that hit a field, a path segment, or was captured by a
/// binder of the clause is refused, never guessed.
pub(in crate::callbacks) fn rename_inherited_params(
    clause: &str,
    renames: &[(String, String)],
) -> Option<String> {
    use trust_wp_core::{contract_parser::parse_contract, formula::CaptureAvoidingSubstOptions};
    if renames.is_empty() {
        return Some(clause.to_string());
    }
    let map: HashMap<&str, &str> = renames
        .iter()
        .map(|(from, to)| (from.as_str(), to.as_str()))
        .collect();
    let bytes = clause.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut out = String::with_capacity(clause.len());
    let mut index = 0;
    while index < bytes.len() {
        let starts_word = is_ident(bytes[index])
            && !bytes[index].is_ascii_digit()
            && (index == 0 || !is_ident(bytes[index - 1]));
        if !starts_word {
            let ch = clause[index..].chars().next()?;
            out.push(ch);
            index += ch.len_utf8();
            continue;
        }
        let mut end = index;
        while end < bytes.len() && is_ident(bytes[end]) {
            end += 1;
        }
        let word = &clause[index..end];
        let before = clause[..index].trim_end();
        let after = clause[end..].trim_start();
        let is_member_or_path = before.ends_with('.')
            || before.ends_with("::")
            || before.ends_with('\'')
            || after.starts_with("::")
            || after.starts_with('!');
        match map.get(word) {
            Some(to) if !is_member_or_path => out.push_str(to),
            _ => out.push_str(word),
        }
        index = end;
    }
    let substitutions: HashMap<String, trust_wp_core::formula::PureExpr> = renames
        .iter()
        .map(|(from, to)| {
            (
                from.clone(),
                trust_wp_core::formula::PureExpr::Var(to.clone(), None),
            )
        })
        .collect();
    let expected = parse_contract(clause)
        .ok()?
        .substitute_capture_avoiding(&substitutions, &CaptureAvoidingSubstOptions::default());
    (parse_contract(&out).ok()? == expected).then_some(out)
}

#[cfg(test)]
mod tests {
    use super::rename_inherited_params;

    fn renames(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
        pairs
            .iter()
            .map(|(from, to)| ((*from).to_string(), (*to).to_string()))
            .collect()
    }

    #[test]
    fn swapped_parameters_are_renamed_simultaneously() {
        assert_eq!(
            rename_inherited_params(
                "result@ == x@ + y@ * 2",
                &renames(&[("x", "y"), ("y", "x")])
            )
            .as_deref(),
            Some("result@ == y@ + x@ * 2")
        );
    }

    #[test]
    fn a_field_and_a_path_segment_keep_their_names() {
        assert_eq!(
            rename_inherited_params("x.x == a::x() && x@ > 0", &renames(&[("x", "p")])).as_deref(),
            Some("p.x == a::x() && p@ > 0")
        );
    }

    #[test]
    fn a_binder_that_would_capture_the_new_name_is_refused() {
        assert_eq!(
            rename_inherited_params("forall<p: Int> p < x@", &renames(&[("x", "p")])),
            None
        );
    }

    #[test]
    fn nothing_to_rename_leaves_the_clause_as_written() {
        assert_eq!(
            rename_inherited_params("result == k()", &[]).as_deref(),
            Some("result == k()")
        );
    }
}
