// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! ExprSort annotation helpers shared across sort-context passes.

use trust_wp_core::formula::{resolve_sort_name, ExprSort, PureExpr};

use super::{
    reference_like_inner_sort,
    sort_inference::{is_fmap_model_type, is_mapping_model_type, is_seq_model_type},
};

fn expr_sort_is_seq(sort: &ExprSort) -> bool {
    if let Some(inner) = reference_like_inner_sort(sort) {
        return expr_sort_is_seq(inner);
    }
    match sort {
        ExprSort::Seq => true,
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            let type_name = name.rsplit("::").next().unwrap_or(&name);
            is_seq_model_type(type_name)
        }
        _ => false,
    }
}

fn expr_sort_is_fmap(sort: &ExprSort) -> bool {
    if let Some(inner) = reference_like_inner_sort(sort) {
        return expr_sort_is_fmap(inner);
    }
    match sort {
        ExprSort::FMap => true,
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            let type_name = name.rsplit("::").next().unwrap_or(&name);
            is_fmap_model_type(type_name)
        }
        _ => false,
    }
}

fn expr_sort_is_mapping(sort: &ExprSort) -> bool {
    if let Some(inner) = reference_like_inner_sort(sort) {
        return expr_sort_is_mapping(inner);
    }
    match sort {
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            let type_name = name.rsplit("::").next().unwrap_or(&name);
            is_mapping_model_type(type_name)
        }
        _ => false,
    }
}

fn expr_sort_is_predcell(sort: &ExprSort) -> bool {
    if let Some(inner) = reference_like_inner_sort(sort) {
        return expr_sort_is_predcell(inner);
    }
    match sort {
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            let type_name = name.rsplit("::").next().unwrap_or(&name);
            type_name == "PredCell"
        }
        _ => false,
    }
}

fn receiver_annotation(expr: &PureExpr) -> Option<&ExprSort> {
    match expr {
        PureExpr::Var(_, ann) => ann.as_ref(),
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => receiver_annotation(inner),
        _ => None,
    }
}

pub(super) fn expr_annotation_is_seq(expr: &PureExpr) -> bool {
    receiver_annotation(expr).is_some_and(expr_sort_is_seq)
}

pub(super) fn expr_annotation_is_fmap(expr: &PureExpr) -> bool {
    receiver_annotation(expr).is_some_and(expr_sort_is_fmap)
}

/// Returns `true` when the receiver has an explicit sort annotation that is
/// NOT a collection type (Seq, FMap, Mapping, PredCell).
///
/// Used by the sort hint accumulator to suppress ambiguous-Seq classification
/// for variables with explicit non-collection annotations (e.g., `ExprSort::Int`
/// for FSet variables). Without this guard, `Final(Var("x", Some(Int))).contains(1)`
/// would incorrectly register `x` as a Seq variable. (#2671)
pub(super) fn expr_has_non_collection_annotation(expr: &PureExpr) -> bool {
    receiver_annotation(expr).is_some_and(|sort| {
        !expr_sort_is_seq(sort)
            && !expr_sort_is_fmap(sort)
            && !expr_sort_is_mapping(sort)
            && !expr_sort_is_predcell(sort)
    })
}

pub(super) fn expr_annotation_is_mapping(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::View(inner) => receiver_annotation(inner)
            .is_some_and(|sort| expr_sort_is_mapping(sort) || expr_sort_is_predcell(sort)),
        _ => receiver_annotation(expr).is_some_and(expr_sort_is_mapping),
    }
}
