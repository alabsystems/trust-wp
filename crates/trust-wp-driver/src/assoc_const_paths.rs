// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Normalization helpers for local associated-const UFCS paths.

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LOCAL_CRATE},
};
use rustc_middle::ty::TyCtxt;
use trust_wp_core::formula::PureExpr;

/// Normalize local associated-const paths in a parsed expression.
///
/// Parsed contracts/proof_asserts preserve source-level trait qualifiers like
/// `crate::`, `self::`, `super::`, and `::{crate_name}::`, but the generic
/// associated-const substitution tables are keyed by rustc local def paths
/// (for example `Nat` or `outer::traits::Nat`). Normalize those local aliases
/// to the canonical form before substitution. (#2550)
pub(crate) fn normalize_local_assoc_const_paths(
    tcx: TyCtxt<'_>,
    scope_def_id: DefId,
    expr: &PureExpr,
) -> PureExpr {
    let current_module = enclosing_module_segments(tcx, scope_def_id);
    let local_crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
    normalize_local_assoc_const_paths_in_scope(expr, &current_module, &local_crate_name)
}

fn enclosing_module_segments(tcx: TyCtxt<'_>, scope_def_id: DefId) -> Vec<String> {
    let mut segments = Vec::new();
    let mut current = scope_def_id;

    while let Some(parent) = tcx.opt_parent(current) {
        current = parent;
        if tcx.def_kind(current) != DefKind::Mod {
            continue;
        }
        if tcx.opt_parent(current).is_none() {
            break;
        }
        segments.push(tcx.item_name(current).as_str().to_string());
    }

    segments.reverse();
    segments
}

fn normalize_local_assoc_const_paths_in_scope(
    expr: &PureExpr,
    current_module: &[String],
    local_crate_name: &str,
) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::Var(name, sort) => {
            if let Some(normalized) =
                normalize_local_qualified_assoc_const_name(&name, current_module, local_crate_name)
            {
                PureExpr::Var(normalized, sort)
            } else {
                PureExpr::Var(name, sort)
            }
        }
        other => other,
    })
}

fn normalize_local_qualified_assoc_const_name(
    name: &str,
    current_module: &[String],
    local_crate_name: &str,
) -> Option<String> {
    let (self_ty, trait_path, assoc_tail) = split_qualified_assoc_const_name(name)?;
    let normalized_trait_path =
        normalize_local_trait_path(trait_path, current_module, local_crate_name)?;
    (normalized_trait_path != trait_path)
        .then(|| format!("<{self_ty} as {normalized_trait_path}>::{assoc_tail}"))
}

fn split_qualified_assoc_const_name(name: &str) -> Option<(&str, &str, &str)> {
    if !name.starts_with('<') {
        return None;
    }

    let mut nested_angle_depth = 0usize;
    let mut as_idx = None;
    let mut outer_end_idx = None;

    for (idx, ch) in name.char_indices().skip(1) {
        match ch {
            '<' => nested_angle_depth += 1,
            '>' if nested_angle_depth == 0 => {
                outer_end_idx = Some(idx);
                break;
            }
            '>' => nested_angle_depth = nested_angle_depth.saturating_sub(1),
            ' ' if nested_angle_depth == 0 && name[idx..].starts_with(" as ") => {
                as_idx = Some(idx);
            }
            _ => {}
        }
    }

    let as_idx = as_idx?;
    let outer_end_idx = outer_end_idx?;
    if name.get(outer_end_idx + 1..outer_end_idx + 3)? != "::" {
        return None;
    }

    Some((
        &name[1..as_idx],
        &name[as_idx + 4..outer_end_idx],
        &name[outer_end_idx + 3..],
    ))
}

fn normalize_local_trait_path(
    trait_path: &str,
    current_module: &[String],
    local_crate_name: &str,
) -> Option<String> {
    if let Some(rest) = trait_path.strip_prefix("crate::") {
        return (!rest.is_empty()).then(|| rest.to_string());
    }

    let local_crate_prefix = format!("::{local_crate_name}::");
    if let Some(rest) = trait_path.strip_prefix(&local_crate_prefix) {
        return (!rest.is_empty()).then(|| rest.to_string());
    }

    let segments: Vec<&str> = trait_path.split("::").collect();
    let mut prefix_len = current_module.len();
    let mut idx = 0usize;
    let mut saw_relative_prefix = false;

    while idx < segments.len() {
        match segments[idx] {
            "self" => {
                saw_relative_prefix = true;
                idx += 1;
            }
            "super" => {
                saw_relative_prefix = true;
                if prefix_len == 0 {
                    return None;
                }
                prefix_len -= 1;
                idx += 1;
            }
            _ => break,
        }
    }

    if !saw_relative_prefix || idx >= segments.len() {
        return None;
    }

    let mut normalized = current_module[..prefix_len].to_vec();
    normalized.extend(segments[idx..].iter().map(|segment| (*segment).to_string()));
    Some(normalized.join("::"))
}

#[cfg(test)]
mod tests {
    use super::normalize_local_qualified_assoc_const_name;

    #[test]
    fn normalize_local_qualified_assoc_const_name_resolves_crate_root_alias() {
        let normalized = normalize_local_qualified_assoc_const_name(
            "<I3<T> as crate::Nat>::VALUE",
            &[],
            "trust_wp_assoc_const_path_test",
        );

        assert_eq!(normalized.as_deref(), Some("<I3<T> as Nat>::VALUE"));
    }

    #[test]
    fn normalize_local_qualified_assoc_const_name_resolves_absolute_local_crate_alias() {
        let normalized = normalize_local_qualified_assoc_const_name(
            "<I3<T> as ::trust_wp_assoc_const_path_test::Nat>::VALUE",
            &[],
            "trust_wp_assoc_const_path_test",
        );

        assert_eq!(normalized.as_deref(), Some("<I3<T> as Nat>::VALUE"));
    }

    #[test]
    fn normalize_local_qualified_assoc_const_name_resolves_super_relative_alias() {
        let normalized = normalize_local_qualified_assoc_const_name(
            "<I3<T> as super::traits::Nat>::VALUE",
            &["outer".to_string(), "nested".to_string()],
            "trust_wp_assoc_const_path_test",
        );

        assert_eq!(
            normalized.as_deref(),
            Some("<I3<T> as outer::traits::Nat>::VALUE")
        );
    }
}
