// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Struct field name → positional index mapping.
//!
//! The contract parser produces `__trust_wp_field_<name>` for named field access,
//! while MIR extraction produces `__trust_wp_tuple_get_<index>`. This module builds
//! the mapping between the two representations by inspecting struct ADT definitions
//! in the function signature.

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt};
use trust_wp_ay::type_constants_for_int;

/// Extract the integer type name from a def_path for type constant resolution.
///
/// For inherent integer methods like `i32::checked_add` or `u8::saturating_sub`,
/// this extracts the type prefix (`"i32"`, `"u8"`) so the driver can call
/// `type_constants_for_int` to populate `Self::MIN`/`Self::MAX` constants. (#688)
///
/// Supports both short-form paths (`i32::checked_add`) and fully-qualified
/// forms (`core::num::i32::checked_add`, `core::num::<impl i32>::checked_add`).
/// Returns `None` if no known integer type token is found.
pub(super) fn extract_int_type_from_path(def_path: &str) -> Option<&str> {
    // Fast path for short-form entries like "i32::checked_add".
    if let Some(prefix) = def_path.split("::").next() {
        if type_constants_for_int(prefix).is_some() {
            return Some(prefix);
        }
    }

    // Fallback for fully-qualified forms. We scan each path segment for an
    // integer token, handling shapes like "core::num::i32::checked_add" and
    // "core::num::<impl i32>::checked_add".
    for segment in def_path.rsplit("::") {
        if type_constants_for_int(segment).is_some() {
            return Some(segment);
        }

        for token in segment.split(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_')) {
            if !token.is_empty() && type_constants_for_int(token).is_some() {
                return Some(token);
            }
        }
    }

    None
}

/// Build a map from struct field names to positional indices for all struct
/// types that appear in the given function signature.
///
/// Used by the named field access rewrite pass to translate `__trust_wp_field_<name>`
/// (from the contract parser) into `__trust_wp_tuple_get_<index>` (matching MIR extraction).
pub(super) fn build_struct_field_map(tcx: TyCtxt<'_>, def_id: DefId) -> HashMap<String, usize> {
    let mut field_map = HashMap::new();
    let mut ambiguous_fields = HashSet::new();
    let mut visited = HashSet::new();
    // Closures don't have fn_sig(); their parameters are captures, not struct args.
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        return field_map;
    }
    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_norm_wip();
    let sig = tcx.liberate_late_bound_regions(def_id, sig);
    for ty in sig.inputs() {
        collect_struct_fields_from_ty(
            tcx,
            *ty,
            &mut field_map,
            &mut ambiguous_fields,
            &mut visited,
            0,
        );
    }
    collect_struct_fields_from_ty(
        tcx,
        sig.output(),
        &mut field_map,
        &mut ambiguous_fields,
        &mut visited,
        0,
    );
    field_map
}

fn record_struct_field_index(
    field_map: &mut HashMap<String, usize>,
    ambiguous_fields: &mut HashSet<String>,
    field_name: &str,
    index: usize,
) {
    if ambiguous_fields.contains(field_name) {
        return;
    }
    match field_map.get(field_name) {
        Some(existing) if *existing != index => {
            field_map.remove(field_name);
            ambiguous_fields.insert(field_name.to_string());
        }
        Some(_) => {}
        None => {
            field_map.insert(field_name.to_string(), index);
        }
    }
}

fn collect_struct_fields_from_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    field_map: &mut HashMap<String, usize>,
    ambiguous_fields: &mut HashSet<String>,
    visited: &mut HashSet<DefId>,
    depth: usize,
) {
    let inner_ty = ty.peel_refs();
    match inner_ty.kind() {
        rustc_middle::ty::TyKind::Adt(adt_def, substs) => {
            if !adt_def.is_struct() {
                // Still recurse into generic type arguments for non-struct ADTs
                // (e.g., Vec<&mut SumTo10> — Vec is a struct, but enums could
                // also carry user struct types in their generic parameters).
                for arg in *substs {
                    if let Some(arg_ty) = arg.as_type() {
                        collect_struct_fields_from_ty(
                            tcx,
                            arg_ty,
                            field_map,
                            ambiguous_fields,
                            visited,
                            depth + 1,
                        );
                    }
                }
                return;
            }
            let adt_id = adt_def.did();
            // Recurse through local nested structs only. Traversing non-local nested
            // structs (for example `Vec`) can pollute the map with implementation
            // detail field names and create false ambiguities for user fields.
            if depth > 0 && !adt_id.is_local() {
                // Still recurse into generic type arguments so that user-defined
                // structs buried in non-local containers (e.g., SumTo10 inside
                // Vec<&mut SumTo10>) are discovered. (#1572)
                for arg in *substs {
                    if let Some(arg_ty) = arg.as_type() {
                        collect_struct_fields_from_ty(
                            tcx,
                            arg_ty,
                            field_map,
                            ambiguous_fields,
                            visited,
                            depth + 1,
                        );
                    }
                }
                return;
            }
            if !visited.insert(adt_id) {
                return;
            }
            if let Some(variant) = adt_def.variants().iter().next() {
                for (idx, field) in variant.fields.iter().enumerate() {
                    let field_name = field.name.to_string();
                    record_struct_field_index(field_map, ambiguous_fields, &field_name, idx);
                    let field_ty = field.ty(tcx, substs).skip_norm_wip();
                    collect_struct_fields_from_ty(
                        tcx,
                        field_ty,
                        field_map,
                        ambiguous_fields,
                        visited,
                        depth + 1,
                    );
                }
            }
            // Also recurse into generic type arguments to discover user structs
            // in container types (e.g., Vec<&mut SumTo10>). (#1572)
            for arg in *substs {
                if let Some(arg_ty) = arg.as_type() {
                    collect_struct_fields_from_ty(
                        tcx,
                        arg_ty,
                        field_map,
                        ambiguous_fields,
                        visited,
                        depth + 1,
                    );
                }
            }
            visited.remove(&adt_id);
        }
        rustc_middle::ty::TyKind::Tuple(fields) => {
            for field_ty in *fields {
                collect_struct_fields_from_ty(
                    tcx,
                    field_ty,
                    field_map,
                    ambiguous_fields,
                    visited,
                    depth + 1,
                );
            }
        }
        rustc_middle::ty::TyKind::Array(elem_ty, _) | rustc_middle::ty::TyKind::Slice(elem_ty) => {
            collect_struct_fields_from_ty(
                tcx,
                *elem_ty,
                field_map,
                ambiguous_fields,
                visited,
                depth + 1,
            );
        }
        _ => {}
    }
}
