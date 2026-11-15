// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type invariant infrastructure for verification.
//!
//! Handles building per-parameter type invariant method maps, rewriting
//! `invariant()` and `inv(x)` calls to type-qualified methods, injecting
//! invariant pre/postconditions, and building newtype parameter sets.

mod clauses;
mod lookup;
mod rewrite;
mod type_params;

use std::collections::{HashMap, HashSet};

// Re-export clause-building functions used by sibling modules.
pub(super) use clauses::{
    build_capture_invariants, build_closure_capture_invariant_requires,
    build_current_closure_self_invariant_requires, build_newtype_param_set,
    build_type_invariant_clauses, build_type_invariant_method_map,
    build_type_invariant_structural_expr_map, is_compound_native_single_field_struct,
    rewrite_synthesized_invariant_calls,
};
use lookup::{adt_type_path, find_element_invariant_method};
// Re-export lookup helpers used by sibling modules and tests.
pub(super) use lookup::{is_known_seq_container, type_path_short_name};
// Non-structural wrappers are test-only after structural expansion (#1296).
// `discharge_trivial_inv_calls_expr` is invoked in production directly from
// `clauses::rewrite_synthesized_invariant_calls` (via `super::rewrite::`); only
// the module's unit tests reach it through this re-export, so it is test-only.
#[cfg(test)]
pub(super) use rewrite::{
    discharge_trivial_inv_calls_expr, rewrite_parsed_contract_type_invariant_methods,
    rewrite_type_invariant_methods_expr,
};
// Re-export rewrite functions used by sibling modules (production).
pub(super) use rewrite::{
    rewrite_parsed_contract_type_invariant_methods_with_structural,
    rewrite_type_invariant_methods_expr_with_structural,
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{TyCtxt, TyKind};
use tracing::trace;
use trust_wp_core::formula::{internal::tuple_lowering::NAMED_FIELD_LOGIC_FN_PREFIX, PureExpr};
pub(super) use type_params::install_invariant_type_names;
pub(crate) use type_params::{
    clear_invariant_type_names, instantiate_type_param_invariants, is_trivially_invariant_free,
    mentions_type_param_invariant, type_param_invariant_at, type_param_invariant_of,
    TypeParamInvariantAt,
};

/// Build synthetic `TypeInvariantDef` entries for container types (#869).
///
/// Scans all function signatures in the contract list for known container types
/// (Vec, VecDeque) whose element types have explicit invariant definitions.
/// For each unique container type found, creates a synthetic `TypeInvariantDef`
/// with `body = true` and `element_invariant_method` set to the element type's
/// invariant method name.
///
/// This enables the encoder to assert quantified element invariants:
///   `forall i. 0 <= i < len(x@) => body[self/index(x@, i)]`
pub(super) fn build_container_invariant_defs(
    tcx: TyCtxt<'_>,
    contracts: &[super::super::contracts::FunctionContract],
    type_invariant_defs: &[trust_wp_core::logic::TypeInvariantDef],
) -> Vec<trust_wp_core::logic::TypeInvariantDef> {
    if type_invariant_defs.is_empty() {
        return Vec::new();
    }

    let invariant_type_names: HashSet<String> = type_invariant_defs
        .iter()
        .map(|d| d.type_name().to_string())
        .collect();
    // Track (container_type_path, element_method) to avoid duplicates
    let mut seen: HashSet<String> = HashSet::new();
    let mut container_defs = Vec::new();

    for contract in contracts {
        // Closures don't support fn_sig()
        if tcx.def_kind(contract.def_id) == rustc_hir::def::DefKind::Closure {
            continue;
        }

        let sig = tcx.fn_sig(contract.def_id).instantiate_identity();
        let sig = sig.skip_binder();

        for ty in sig.inputs().iter().chain(std::iter::once(&sig.output())) {
            let inner = match ty.kind() {
                TyKind::Ref(_, inner, _) => *inner,
                _ => *ty,
            };
            if let TyKind::Adt(adt_def, substs) = inner.kind() {
                let type_path = adt_type_path(tcx, *adt_def);
                if !is_known_seq_container(&type_path) {
                    continue;
                }
                if let Some(element_method) =
                    find_element_invariant_method(tcx, *substs, &invariant_type_names)
                {
                    // Use the short type name (last path segment) for the def,
                    // matching how build_type_invariant_method_map generates method names
                    let short_name = type_path_short_name(&type_path).to_string();
                    let key = format!("{short_name}::{element_method}");
                    if seen.contains(&key) {
                        continue;
                    }
                    seen.insert(key);

                    container_defs.push(trust_wp_core::type_invariant_def! {
                        type_name: short_name,
                        self_param: "self".to_string(),
                        param_sort: None,
                        body: PureExpr::Bool(true),
                        is_newtype: false,
                        element_invariant_method: Some(element_method),
                    });
                }
            }
        }
    }

    container_defs
}

/// Rewrite named field access in type invariant def bodies to positional access (#1370).
///
/// The contract parser lowers `self.a` in invariant bodies to
/// `LogicFnCall("__trust_wp_field_a", [Var("self")])`, while the proof_assert
/// assertion (from MIR extraction) uses positional access:
/// `LogicFnCall("__trust_wp_tuple_get_0", [x])`. These are unrelated uninterpreted
/// functions in SMT, so the solver cannot prove `a + b == 10` when one side
/// uses named access and the other uses positional.
///
/// This function rewrites invariant bodies by finding each invariant type's ADT
/// definition in the local crate and applying the same named→positional field
/// rewriting that contracts receive via `rewrite_named_field_access_expr`.
pub(super) fn rewrite_invariant_def_named_fields(
    tcx: TyCtxt<'_>,
    type_invariant_defs: &mut [trust_wp_core::logic::TypeInvariantDef],
) {
    use super::{
        contract_rewrite::{rewrite_named_field_access_expr, FieldOrderTables},
        struct_field_map::build_crate_ctor_field_order,
    };

    let ctor_field_order = build_crate_ctor_field_order(tcx);

    // Build a map from type name (both short and crate-qualified) to field map.
    // We iterate local ADTs once and cache the field maps.
    let mut adt_field_maps: HashMap<DefId, HashMap<String, usize>> = HashMap::new();
    // Map type_name → ADT DefId for quick lookup.
    let mut name_to_adt: HashMap<String, DefId> = HashMap::new();

    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        if tcx.def_kind(def_id) != rustc_hir::def::DefKind::Struct {
            continue;
        }
        let adt_def = tcx.adt_def(def_id);
        if !adt_def.is_struct() {
            continue;
        }
        // Register both the full def_path_str and crate-qualified forms.
        let def_path = tcx.def_path_str(def_id);
        name_to_adt.insert(def_path.clone(), def_id);

        // Also register with crate name prefix for matching against
        // crate-qualified invariant type names (e.g., "creusot_test::SumTo10").
        let crate_name = tcx.crate_name(def_id.krate).to_string();
        if !def_path.contains("::") {
            let qualified = format!("{crate_name}::{def_path}");
            name_to_adt.insert(qualified, def_id);
        }
    }

    for inv_def in type_invariant_defs.iter_mut() {
        // Skip if body doesn't contain named field access.
        // Note: do NOT skip based on `is_newtype` — multi-field structs can be
        // misclassified as newtypes when their invariant body uses named field
        // access (`__trust_wp_field_*`) instead of positional (`__trust_wp_tuple_get_*`),
        // because `has_higher_tuple_field_access` only checks positional access. (#1370)
        if !expr_contains_named_field_access(inv_def.body()) {
            continue;
        }

        let Some(&adt_def_id) = name_to_adt.get(inv_def.type_name()) else {
            continue;
        };

        let field_map = adt_field_maps.entry(adt_def_id).or_insert_with(|| {
            let adt_def = tcx.adt_def(adt_def_id);
            let mut map = HashMap::new();
            if let Some(variant) = adt_def.variants().iter().next() {
                for (idx, field) in variant.fields.iter().enumerate() {
                    map.insert(field.name.to_string(), idx);
                }
            }
            map
        });

        if field_map.is_empty() {
            continue;
        }

        // A body whose named-field pattern cannot be placed is left AS
        // WRITTEN, keeping its `{...}` field metadata. That is not a
        // source-order fallback: the contract-level pass this body is spliced
        // into sees the same metadata and refuses there (D-31), where a
        // refusal has a function to attach to.
        let tables = FieldOrderTables::new(field_map, &ctor_field_order);
        let Ok(rewritten) = rewrite_named_field_access_expr(inv_def.body(), tables) else {
            continue;
        };
        let field_count = field_map.len();
        trace!(
            type_name = %inv_def.type_name(),
            field_count,
            "type invariant body: named field(s) rewritten to positional access"
        );
        inv_def.set_body(rewritten);
    }
}

/// Check whether a `PureExpr` contains any `__trust_wp_field_*` logic function calls.
fn expr_contains_named_field_access(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| {
        matches!(node, PureExpr::LogicFnCall { name, .. } if name.starts_with(NAMED_FIELD_LOGIC_FN_PREFIX))
    })
}

#[cfg(test)]
mod tests;
