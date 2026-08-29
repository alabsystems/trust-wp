// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort context: sort mapping, inference, hint collection, and variable name resolution.

mod annotations;
mod collection_hint_helpers;
mod derived_names;
pub(in crate::encoder) mod hint_collection;
mod hint_registration;
pub(crate) mod plan;
pub(crate) mod preseed;
mod receiver;
pub(in crate::encoder) mod resolution;
pub(crate) use derived_names::DerivedKind;
#[cfg(test)]
pub(crate) use derived_names::{classify_var_name, is_derived_var_name};
pub(super) mod sort_coercion;
pub(in crate::encoder) mod sort_inference;
pub(crate) mod sort_mapping;
pub(crate) mod var_collection;

use std::{borrow::Cow, collections::HashSet};

use ay_dpll::api::Sort;
pub(crate) use hint_collection::collect_bool_hints;
pub(in crate::encoder) use hint_collection::collect_names_as_bool;
#[cfg(test)]
pub(crate) use hint_collection::{collect_all_sort_hints, SortHintAccumulator};
pub(crate) use plan::{SortPlan, SortPlanBuilder};
pub(super) use sort_coercion::{coerce_ite_sorts, coerce_to_numeric, NumericOperandMode};
pub(crate) use sort_coercion::{
    is_seq_family_sort, register_adt_family_alias, resolve_adt_family_alias,
    same_structural_family, select_structural_sort_target,
};
pub(crate) use sort_inference::{
    ay_sort_to_expr_sort, expr_sort_to_ay_sort, infer_expr_sort, is_definitely_non_bool,
};
pub(in crate::encoder) use sort_inference::{infer_expr_sort_cached, InferExprSortCache};
use sort_mapping::{expr_sort_to_ay_sort_for_carrier, SeqCarrier};
use trust_wp_core::formula::{ExprSort, PureExpr};

pub(crate) use super::closure_sorts::RegisteredClosureStructSort;
#[cfg(test)]
pub(crate) use super::closure_sorts::StructuredSortContext;
use crate::encoder::AYEncoder;

/// Helper: the `ExprSort` representation of the `Mapping` (total function) sort.
///
/// `Mapping` has no dedicated `ExprSort` variant; it is represented as
/// `ExprSort::Datatype(intern_sort_name("Mapping"))`. This helper centralizes
/// that convention for sort hint registration and receiver classification.
pub(crate) fn mapping_expr_sort() -> ExprSort {
    ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("Mapping"))
}

pub(crate) fn reference_like_inner_sort(sort: &ExprSort) -> Option<&ExprSort> {
    match sort {
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => Some(inner.as_ref()),
        _ => None,
    }
}

/// Returns `true` if the given `ExprSort` represents a collection type
/// (Seq, FMap, or Mapping). Collection sort hints take priority over Bool
/// in `record_sort_hint`. (#1517, #1778, #2316)
pub(crate) fn is_collection_expr_sort(sort: &ExprSort) -> bool {
    reference_like_inner_sort(sort).is_some_and(is_collection_expr_sort)
        || matches!(sort, ExprSort::Seq | ExprSort::FMap)
        || matches!(sort, ExprSort::Datatype(id) if trust_wp_core::formula::resolve_sort_name(*id) == "Mapping")
}

pub(crate) fn extract_base_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => extract_base_var_name(inner),
        _ => None,
    }
}

/// Extract the ExprSort annotation from the innermost Var in a
/// Deref/Final/Old/View chain. For `Deref(Var("x", Some(Seq)))` returns
/// `Some(&Seq)`. For `Deref(Deref(Var("x", Some(Datatype(42)))))` returns
/// `Some(&Datatype(42))`. Returns `None` if no Var with annotation is found.
/// (#2084)
pub(crate) fn extract_inner_var_annotation(expr: &PureExpr) -> Option<&ExprSort> {
    match expr {
        PureExpr::Var(_, ann) => ann.as_ref(),
        PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => extract_inner_var_annotation(inner),
        _ => None,
    }
}

/// Compute the effective `ExprSort` annotation for an expression, accounting
/// for `Deref`/`Final` wrappers that peel reference layers from the source
/// variable's annotation.
///
/// Unlike [`extract_inner_var_annotation`] which returns the raw annotation from
/// the innermost `Var`, this function peels one `Ref`/`MutRef` layer per
/// `Deref`/`Final` wrapper. For `Deref(Var("x", MutRef(MutRef(Int))))`, returns
/// `Some(&MutRef(Int))` (not `Some(&MutRef(MutRef(Int))))`). (#2583)
pub(crate) fn effective_expr_annotation(expr: &PureExpr) -> Option<&ExprSort> {
    match expr {
        PureExpr::Var(_, ann) => ann.as_ref(),
        PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            effective_expr_annotation(inner).and_then(reference_like_inner_sort)
        }
        PureExpr::Old(inner) | PureExpr::View(inner) => effective_expr_annotation(inner),
        _ => None,
    }
}

pub(crate) fn extract_constructor_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::LogicFnCall { name, .. } => Some(name.as_str()),
        PureExpr::Var(name, _) if is_nullary_constructor_name(name) => Some(name.as_str()),
        PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => extract_constructor_name(inner),
        PureExpr::Ite(_, then_branch, else_branch) => {
            extract_constructor_name(then_branch).or_else(|| extract_constructor_name(else_branch))
        }
        _ => None,
    }
}

fn is_nullary_constructor_name(name: &str) -> bool {
    name == "None"
}

pub(crate) fn apply_name_prefix(name: &str, prefix: Option<DerivedKind>) -> Cow<'_, str> {
    match prefix {
        Some(kind) => Cow::Owned(kind.format_name(name)),
        None => Cow::Borrowed(name),
    }
}

pub(crate) fn resolve_nameable_expr(
    expr: &PureExpr,
    prefix: Option<DerivedKind>,
) -> Option<String> {
    match expr {
        PureExpr::Var(name, _) => Some(apply_name_prefix(name, prefix).into_owned()),
        PureExpr::Old(inner) => {
            if matches!(inner.as_ref(), PureExpr::Deref(_)) {
                resolve_nameable_expr(inner, prefix)
            } else {
                resolve_nameable_expr(inner, Some(DerivedKind::Old))
            }
        }
        PureExpr::Deref(inner) => {
            resolve_nameable_expr(inner, prefix).map(|name| DerivedKind::Current.format_name(&name))
        }
        PureExpr::Final(inner) => {
            resolve_nameable_expr(inner, prefix).map(|name| DerivedKind::Final.format_name(&name))
        }
        _ => None,
    }
}

pub(crate) struct MutRefVarNames {
    pub current: String,
    pub final_val: String,
    pub id: String,
}

impl MutRefVarNames {
    pub(crate) fn new(base: &str) -> Self {
        Self {
            current: DerivedKind::Current.format_name(base),
            final_val: DerivedKind::Final.format_name(base),
            id: format!("{base}_id"),
        }
    }
}

pub(crate) fn resolve_view_var_name(
    expr: &PureExpr,
    prefix: Option<DerivedKind>,
) -> Option<String> {
    match expr {
        PureExpr::View(inner) => {
            if let PureExpr::Final(inner_final) = inner.as_ref() {
                resolve_nameable_expr(inner_final, prefix).map(|name| {
                    DerivedKind::format_chain(&name, &[DerivedKind::FinalPrefix, DerivedKind::View])
                })
            } else {
                resolve_nameable_expr(inner, prefix)
                    .map(|name| DerivedKind::View.format_name(&name))
            }
        }
        PureExpr::Old(inner) => {
            if let PureExpr::View(view_inner) = inner.as_ref() {
                if let PureExpr::Final(inner_final) = view_inner.as_ref() {
                    resolve_nameable_expr(inner_final, Some(DerivedKind::Old)).map(|name| {
                        DerivedKind::format_chain(
                            &name,
                            &[DerivedKind::FinalPrefix, DerivedKind::View],
                        )
                    })
                } else {
                    resolve_nameable_expr(view_inner, Some(DerivedKind::Old))
                        .map(|name| DerivedKind::View.format_name(&name))
                }
            } else {
                None
            }
        }
        _ => None,
    }
}

fn collect_derived_name_fallback_candidates(
    name: &str,
    seen: &mut HashSet<String>,
    out: &mut Vec<String>,
) {
    if !seen.insert(name.to_string()) {
        return;
    }
    out.push(name.to_string());

    if let Some(stripped) = DerivedKind::peel_final_view_prefix(name) {
        collect_derived_name_fallback_candidates(&stripped, seen, out);
    }

    if let Some((DerivedKind::View, base)) = DerivedKind::strip_from(name) {
        collect_derived_name_fallback_candidates(base, seen, out);
    }

    let mut suffix_base = name;
    while let Some((kind, stripped)) = DerivedKind::strip_from(suffix_base) {
        match kind {
            DerivedKind::Current | DerivedKind::Final | DerivedKind::Prime => {
                suffix_base = stripped;
                collect_derived_name_fallback_candidates(suffix_base, seen, out);
            }
            _ => break,
        }
    }

    for stripped in DerivedKind::peel_old_prefixes(name) {
        collect_derived_name_fallback_candidates(stripped, seen, out);
    }
}

fn derived_name_fallback_candidates(name: &str) -> Vec<String> {
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    collect_derived_name_fallback_candidates(name, &mut seen, &mut out);
    out
}

fn registered_non_int_hint(encoder: &AYEncoder, name: &str) -> Option<Sort> {
    let carrier = encoder.seq_carrier();
    encoder
        .sort_hint(name)
        // Every Seq-producing annotation is carrier-aware, not just the bare
        // `ExprSort::Seq` one: a `Datatype("Vec")` hint maps to Seq too, and
        // used to arrive here hard-coded to the native spelling.
        .map(|hint| expr_sort_to_ay_sort_for_carrier(hint, carrier))
        .filter(|sort| *sort != Sort::Int)
}

fn project_reference_like_sort_for_requested_name(
    name: &str,
    sort: &Sort,
    carrier: SeqCarrier,
) -> Option<Sort> {
    let mut current = name;
    let mut chain = Vec::new();
    while let Some((kind, base)) = DerivedKind::strip_from(current) {
        chain.push(kind);
        current = base;
    }
    if chain.is_empty() {
        return None;
    }

    let mut expr_sort = ay_sort_to_expr_sort(sort)?;
    let mut peeled = false;
    for kind in chain.into_iter().rev() {
        match kind {
            // These derived names consume one reference layer when one is
            // still present. This lets names like `self__final_current_view`
            // project `&mut &mut [T]` all the way down to Seq instead of
            // stopping after a single peel at `&mut [T]`. (#1805, #2673)
            DerivedKind::Current
            | DerivedKind::Final
            | DerivedKind::FinalPrefix
            | DerivedKind::View => {
                let Some(inner) = reference_like_inner_sort(&expr_sort).cloned() else {
                    continue;
                };
                expr_sort = inner;
                peeled = true;
            }
            DerivedKind::Old | DerivedKind::Prime => {}
        }
    }

    peeled.then(|| expr_sort_to_ay_sort_for_carrier(&expr_sort, carrier))
}

fn project_registered_sort_for_requested_name(
    name: &str,
    sort: &Sort,
    carrier: SeqCarrier,
) -> Sort {
    project_reference_like_sort_for_requested_name(name, sort, carrier)
        .unwrap_or_else(|| sort.clone())
}

fn is_logical_view_identity_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool)
        || is_seq_family_sort(sort)
        || matches!(sort, Sort::Uninterpreted(name) if matches!(name.as_str(), "FMap" | "Mapping"))
}

fn later_logical_view_identity_decl(
    encoder: &AYEncoder,
    candidates: &[String],
    start: usize,
) -> Option<Sort> {
    candidates[start..].iter().find_map(|candidate| {
        encoder
            .var_sort(candidate)
            .filter(|sort| **sort != Sort::Int && is_logical_view_identity_sort(sort))
            .cloned()
    })
}

pub(in crate::encoder) fn matches_registered_sort(
    encoder: &AYEncoder,
    name: &str,
    target: &Sort,
) -> bool {
    resolve_registered_non_int_sort(encoder, name).is_some_and(|sort| sort == *target)
}

pub(in crate::encoder) fn resolve_registered_non_int_sort(
    encoder: &AYEncoder,
    name: &str,
) -> Option<Sort> {
    let carrier = encoder.seq_carrier();
    let candidates = derived_name_fallback_candidates(name);
    for (idx, candidate) in candidates.iter().enumerate() {
        if let Some(sort) = encoder.var_sort(candidate) {
            let projected = project_registered_sort_for_requested_name(name, sort, carrier);
            if projected != Sort::Int {
                return Some(projected);
            }
        }
        if let Some(hint) = registered_non_int_hint(encoder, candidate) {
            let projected_hint = project_registered_sort_for_requested_name(name, &hint, carrier);
            if projected_hint == Sort::Int {
                continue;
            }
            // View-derived names can intentionally change carrier
            // (`PredCellTemp -> Mapping`, `Vec -> Seq`), so an earlier direct
            // hint still wins over later runtime carriers. But if a later name
            // in the fallback chain already has a declared logical carrier
            // (`Seq`/`FMap`/`Mapping`/`Bool`), that declaration is more
            // authoritative than a stale derived hint like `m_view: Seq` over
            // `m: FMap`. (#2116, #2316)
            if let Some(later_decl) =
                later_logical_view_identity_decl(encoder, &candidates, idx + 1)
            {
                if later_decl != projected_hint {
                    return Some(later_decl);
                }
            }
            return Some(projected_hint);
        }
    }
    None
}
