// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract detection and discovery.
//!
//! Finds functions with trust-wp contract attributes, discovers extern_spec!
//! entries, resolves trait contracts and inheritance.

pub(crate) mod erasure;
pub(crate) mod source_parsing;
mod trait_contracts;
pub(crate) mod trusted;

#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};

pub(super) use erasure::{collect_erasure_pairs, validate_erasure_pair};
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
    Node, TraitFn, TraitItemKind,
};
use rustc_middle::ty::TyCtxt;
use source_parsing::{
    collect_loop_contract_attrs, collect_loop_contract_attrs_from_source, extend_unique,
    get_contract_attrs,
};
pub(super) use trait_contracts::{
    apply_trait_contract_inheritance, find_trait_contracts, find_trait_refinement_overrides,
    has_invariant_bearing_signature,
};
use trust_wp_core::logic::TypeInvariantDef;
use trust_wp_driver::{normalize_extern_spec_path, parse_extern_spec_docs, StdSpec};
use trusted::has_trusted_marker;

use super::super::{
    attr_utils::{get_contract_attrs_from_doc, get_contract_attrs_from_proc_macro, has_check_mode},
    contracts::{FunctionContract, TraitOrigin},
};

/// Discover all extern_spec! entries in the crate.
///
/// Searches for functions with `trust-wp:extern_spec:target=...` doc markers
/// and extracts their contracts. Returns a map from normalized target path
/// to StdSpec, along with a count of duplicate declarations detected.
///
/// Duplicate local extern_specs (two `extern_spec!` blocks targeting the same
/// function) are reported as errors and skipped. (#2686)
pub(super) fn discover_extern_specs(tcx: TyCtxt<'_>) -> (HashMap<String, StdSpec>, usize) {
    let mut specs = HashMap::new();
    let mut duplicate_count = 0usize;

    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();

        // Only consider functions (extern_spec stubs are generated as functions)
        let def_kind = tcx.def_kind(def_id);
        if !matches!(def_kind, DefKind::Fn | DefKind::AssocFn) {
            continue;
        }

        // Get attributes and extract doc strings
        let attrs = tcx.get_all_attrs(def_id);
        let doc_values: Vec<String> = attrs
            .iter()
            .filter_map(|attr| crate::attr_utils::doc_marker_str(attr).map(|s| s.to_string()))
            .collect();

        // Try to parse as extern_spec entry
        match parse_extern_spec_docs(doc_values.iter().map(|s| s.as_str())) {
            Ok(Some(entry)) => {
                let normalized = normalize_extern_spec_path(&entry.target_path);
                let spec = StdSpec {
                    requires: entry.requires,
                    ensures: entry.ensures,
                    param_names: None,
                };
                if specs.contains_key(&normalized) {
                    let fn_name = tcx.def_path_str(def_id);
                    eprintln!(
                        "trust-wp: error: duplicate extern_spec for `{normalized}` \
                         (declared again in `{fn_name}`)"
                    );
                    duplicate_count += 1;
                } else {
                    specs.insert(normalized, spec);
                }
            }
            Ok(None) => {}
            Err(e) => {
                let fn_name = tcx.def_path_str(def_id);
                eprintln!("trust-wp: warning: malformed extern spec on `{fn_name}`: {e}");
            }
        }
    }

    (specs, duplicate_count)
}

/// Find all functions with trust-wp contract attributes.
pub(super) fn find_contract_functions(tcx: TyCtxt<'_>) -> Vec<FunctionContract> {
    let mut contracts = Vec::new();

    // Iterate over all local definitions
    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();

        // Only consider functions, methods, and closures.
        let def_kind = tcx.def_kind(def_id);
        if !matches!(def_kind, DefKind::Fn | DefKind::AssocFn | DefKind::Closure) {
            continue;
        }

        // Skip bodyless trait method declarations (e.g., `fn foo(&self);` without
        // a default body). These have contracts that should only be processed by
        // `find_trait_contracts` for call-site inheritance — including them here
        // causes ICEs when the verification pipeline tries to access their
        // non-existent MIR bodies. (#2205)
        if let Node::TraitItem(item) = tcx.hir_node_by_def_id(local_def_id) {
            if matches!(item.kind, TraitItemKind::Fn(_, TraitFn::Required(_))) {
                continue;
            }
        }

        // Check for contract attributes
        // Support multiple styles (checked in this order):
        // 1. Doc-embedded: #[doc = "trust-wp:requires:..."] (current proc-macro output)
        // 2. Tool attributes: #[trust_wp::spec::requires = "..."] (legacy)
        // 3. Proc macro style: #[requires(...)] (fallback)
        let attrs = tcx.get_all_attrs(def_id);

        // Check for trusted marker (postconditions assumed, body not verified)
        let trusted = has_trusted_marker(tcx, def_id, attrs);
        if trusted && trusted::trusted_code_is_denied_for_item(tcx, def_id, attrs) {
            tcx.dcx()
                .span_err(tcx.def_span(def_id), "used the `#[trusted]` attribute");
            continue;
        }
        // Check for explicit termination marker.
        let terminates = has_check_mode(attrs, "terminates");
        // Check for ghost function marker (#[check(ghost)]).
        let ghost = has_check_mode(attrs, "ghost");
        // Try doc-embedded attributes first (current proc-macro output)
        let mut requires = get_contract_attrs_from_doc(attrs, "requires");
        let mut ensures = get_contract_attrs_from_doc(attrs, "ensures");
        let mut invariants = get_contract_attrs_from_doc(attrs, "invariant");
        let mut variants = get_contract_attrs_from_doc(attrs, "variant");

        // Fall back to legacy tool attributes
        if requires.is_empty() && ensures.is_empty() && invariants.is_empty() && variants.is_empty()
        {
            requires = get_contract_attrs(attrs, &["trust-wp", "spec", "requires"]);
            ensures = get_contract_attrs(attrs, &["trust-wp", "spec", "ensures"]);
            invariants = get_contract_attrs(attrs, &["trust-wp", "spec", "invariant"]);
            variants = get_contract_attrs(attrs, &["trust-wp", "spec", "variant"]);
        }

        // Fall back to proc macro attributes if still not found
        if requires.is_empty() && ensures.is_empty() && invariants.is_empty() && variants.is_empty()
        {
            requires = get_contract_attrs_from_proc_macro(attrs, "requires");
            ensures = get_contract_attrs_from_proc_macro(attrs, "ensures");
            invariants = get_contract_attrs_from_proc_macro(attrs, "invariant");
            variants = get_contract_attrs_from_proc_macro(attrs, "variant");
        }

        // Loop-level `#[invariant(...)]` / `#[variant(...)]` attributes are attached
        // to HIR loop expressions, not function items. Collect them from the body so
        // Creusot-style statement attributes activate loop verification. (#873)
        let (
            loop_invariants,
            loop_variants,
            per_loop_invariants,
            per_loop_variants,
            all_loop_spans,
        ) = collect_loop_contract_attrs(tcx, local_def_id);
        extend_unique(&mut invariants, loop_invariants);
        extend_unique(&mut variants, loop_variants);
        let (source_invariants, source_variants) =
            collect_loop_contract_attrs_from_source(tcx, def_id);
        extend_unique(&mut invariants, source_invariants);
        extend_unique(&mut variants, source_variants);

        // Resolve trait origin for impl methods using opt_associated_item
        let trait_origin = tcx.opt_associated_item(def_id).and_then(|assoc| {
            // trait_item_def_id is set when this is an impl of a trait method
            assoc.trait_item_def_id().map(|trait_method_id| {
                // The trait DefId is the parent of the trait method
                let trait_def_id = tcx.parent(trait_method_id);
                let method_name = tcx.item_name(trait_method_id).to_string();
                TraitOrigin {
                    trait_def_id,
                    trait_method_name: method_name,
                }
            })
        });

        // Trait default methods with bodies need verification even without explicit
        // contracts so call-site obligations (e.g., invoking a contracted trait method)
        // are checked (#1203).
        let trait_default_with_body = is_bodyful_trait_method(tcx, local_def_id);

        // Include functions with any contract attribute, trusted marker, trait origin,
        // or bodyful trait default method.
        // (trait origin means we may inherit contracts later)
        if !requires.is_empty()
            || !ensures.is_empty()
            || !invariants.is_empty()
            || !variants.is_empty()
            || terminates
            || ghost
            || trusted
            || trait_origin.is_some()
            || trait_default_with_body
        {
            contracts.push(FunctionContract {
                local_def_id,
                def_id,
                requires,
                ensures,
                invariants,
                per_loop_invariants,
                per_loop_variants,
                all_loop_spans,
                variants,
                terminates,
                ghost,
                trusted,
                trait_origin,
            });
        }
    }

    contracts
}

pub(super) fn is_bodyful_trait_method(tcx: TyCtxt<'_>, local_def_id: LocalDefId) -> bool {
    let def_id = local_def_id.to_def_id();
    tcx.opt_associated_item(def_id).is_some_and(|assoc| {
        matches!(assoc.container, rustc_middle::ty::AssocContainer::Trait)
            && (tcx.defaultness(def_id).has_value()
                || matches!(
                    tcx.hir_node_by_def_id(local_def_id),
                    Node::TraitItem(item)
                        if matches!(item.kind, TraitItemKind::Fn(_, TraitFn::Provided(_)))
                )
                || tcx.is_mir_available(def_id))
    })
}

/// Discover functions that should be verified due to type invariant injection,
/// even without explicit `#[requires]`/`#[ensures]` annotations (#359).
///
/// In Creusot, functions with parameters or return types that have
/// `impl Invariant for T` automatically get invariant pre/postconditions.
/// This function finds unannotated functions whose types match defined
/// type invariants and adds them to the contracts list.
pub(super) fn discover_invariant_bearing_functions(
    tcx: TyCtxt<'_>,
    contracts: &mut Vec<FunctionContract>,
    type_invariant_defs: &[TypeInvariantDef],
) {
    if type_invariant_defs.is_empty() {
        return;
    }

    let invariant_type_names: HashSet<&str> =
        type_invariant_defs.iter().map(|d| d.type_name()).collect();

    // Build set of already-discovered functions so we don't add duplicates
    let existing: HashSet<DefId> = contracts.iter().map(|c| c.def_id).collect();

    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();

        // Only consider functions and methods (not closures — they get
        // invariant injection via their parent function's contract).
        let def_kind = tcx.def_kind(def_id);
        if !matches!(def_kind, DefKind::Fn | DefKind::AssocFn) {
            continue;
        }

        // Skip bodyless trait method declarations (#2205). These have no
        // HIR body or usable MIR; the verification pipeline would ICE in
        // `body_owned_by` when trying to access their non-existent bodies.
        if let Node::TraitItem(item) = tcx.hir_node_by_def_id(local_def_id) {
            if matches!(item.kind, TraitItemKind::Fn(_, TraitFn::Required(_))) {
                continue;
            }
        }

        // Skip functions already discovered via contract attributes
        if existing.contains(&def_id) {
            continue;
        }

        // Skip logic functions (they are specification-only)
        let attrs = tcx.get_all_attrs(def_id);
        if super::super::logic::has_logic_marker(attrs) {
            continue;
        }

        // Skip trusted functions without contracts (nothing to verify)
        if has_trusted_marker(tcx, def_id, attrs) {
            continue;
        }

        // Check if any parameter or the return type matches a type with a defined invariant
        if has_invariant_bearing_signature(tcx, def_id, &invariant_type_names) {
            contracts.push(FunctionContract {
                local_def_id,
                def_id,
                requires: vec![],
                ensures: vec![],
                invariants: vec![],
                per_loop_invariants: vec![],
                per_loop_variants: vec![],
                all_loop_spans: vec![],
                variants: vec![],
                terminates: false,
                ghost: false,
                trusted: false,
                trait_origin: None,
            });
        }
    }
}

/// Discover functions that contain `proof_assert!` but have no contract annotations.
///
/// When a function like `ghost_only()` uses `proof_assert!` inside a `ghost! { ... }` block
/// but has no `#[requires]`/`#[ensures]` attributes, it will not appear in the contracts
/// list. Without a contract entry, the verification loop in `verify_contracts` never
/// iterates over this function, so its proof_asserts are never checked. (#1581)
///
/// This function scans all MIR body owners for proof_assert closures (identified by the
/// `trust-wp:proof_assert:` doc marker attribute) and creates synthetic empty-contract entries
/// for their containing functions, enabling the per-function proof_assert verification
/// loop to pick them up.
pub(super) fn discover_proof_assert_functions(
    tcx: TyCtxt<'_>,
    contracts: &mut Vec<FunctionContract>,
) {
    use rustc_middle::mir::{Rvalue, StatementKind};

    let existing: HashSet<DefId> = contracts.iter().map(|c| c.def_id).collect();

    // Collect functions that contain proof_asserts. We scan MIR bodies
    // for closure aggregates with the proof_assert doc marker, matching
    // the same detection logic as `find_proof_asserts_in_mir`.
    let mut pa_fns: HashSet<LocalDefId> = HashSet::new();

    for local_def_id in tcx.hir_body_owners() {
        let def_id = local_def_id.to_def_id();

        // Only consider functions and methods
        let def_kind = tcx.def_kind(def_id);
        if !matches!(def_kind, DefKind::Fn | DefKind::AssocFn) {
            continue;
        }

        // Skip functions already in the contracts list
        if existing.contains(&def_id) {
            continue;
        }

        // Skip logic functions (specification-only)
        let attrs = tcx.get_all_attrs(def_id);
        if super::super::logic::has_logic_marker(attrs) {
            continue;
        }

        // Check MIR body for proof_assert closures
        if !tcx.is_mir_available(def_id) {
            continue;
        }

        // Skip bodyless trait method declarations (#2205). `is_mir_available`
        // returns true for these (rustc generates an unreachable shim), but
        // `mir_borrowck` panics in `body_owned_by` because no HIR body exists.
        if let Node::TraitItem(item) = tcx.hir_node_by_def_id(local_def_id) {
            if matches!(item.kind, TraitItemKind::Fn(_, TraitFn::Required(_))) {
                continue;
            }
        }

        // Trigger borrow checking to populate MIR cache.
        // Must use typeck_root_def_id, not the function itself — closures and
        // nested items share their root's borrowck result.
        let root = tcx.typeck_root_def_id(def_id).expect_local();
        let _ = tcx.mir_borrowck(root);

        let Some(body_with_facts) = super::try_get_body_with_context(local_def_id) else {
            continue;
        };

        // Walk MIR looking for proof_assert closure aggregates
        let body = &body_with_facts.body;

        let has_proof_assert = body.basic_blocks.iter().any(|bb_data| {
            bb_data.statements.iter().any(|stmt| {
                if let StatementKind::Assign(box (
                    _,
                    Rvalue::Aggregate(
                        box rustc_middle::mir::AggregateKind::Closure(closure_def_id, _),
                        _,
                    ),
                )) = &stmt.kind
                {
                    // Check if this closure has the proof_assert doc marker
                    if let Some(local) = closure_def_id.as_local() {
                        let hir_id = tcx.local_def_id_to_hir_id(local);
                        let attrs = tcx.hir_attrs(hir_id);
                        return attrs.iter().any(|attr| {
                            crate::attr_utils::doc_marker_str(attr).is_some_and(|v| {
                                let s = v.as_str();
                                s.starts_with("trust-wp:proof_assert:")
                                    || s.starts_with("trust-wp:trusted_proof_assert:")
                            })
                        });
                    }
                }
                false
            })
        });

        if has_proof_assert {
            pa_fns.insert(local_def_id);
        }
    }

    for local_def_id in pa_fns {
        let def_id = local_def_id.to_def_id();
        contracts.push(FunctionContract {
            local_def_id,
            def_id,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            per_loop_invariants: vec![],
            per_loop_variants: vec![],
            all_loop_spans: vec![],
            variants: vec![],
            terminates: false,
            ghost: false,
            trusted: false,
            trait_origin: None,
        });
    }
}
