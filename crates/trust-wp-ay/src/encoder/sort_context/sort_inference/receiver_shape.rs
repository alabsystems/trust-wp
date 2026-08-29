// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_core::formula::{
    internal::tuple_lowering::{NAMED_FIELD_LOGIC_FN_PREFIX, TUPLE_FIELD_LOGIC_FN_PREFIX},
    resolve_sort_name, ExprSort, PureExpr,
};

use super::{is_fmap_model_type, is_mapping_model_type, is_seq_model_type};
use crate::encoder::seq::expr_produces_seq;

fn type_name_is_predcell_slice(type_name: &str) -> bool {
    type_name == "PredCellSlice"
}

pub(super) fn receiver_is_seq_like(expr: &PureExpr) -> bool {
    // `set` returns `Self`, so `X.set(k, v)` has `X`'s collection kind. Recurse on
    // the inner receiver rather than letting the `expr_produces_seq` fallback treat
    // every `set` as Seq — a chained Mapping `m.set(..).set(..)` (mapping_indexing)
    // must stay Mapping-like for `Mapping::set` sort inference. (#newfrontier)
    if let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    {
        if method == "set" && args.len() == 2 {
            return receiver_is_seq_like(receiver);
        }
    }
    match expr {
        PureExpr::Var(_, Some(ExprSort::Seq)) => true,
        PureExpr::Var(_, Some(ExprSort::Datatype(id))) => {
            let name = resolve_sort_name(*id);
            let bare = name.rsplit("::").next().unwrap_or(&name);
            is_seq_model_type(bare)
        }
        PureExpr::Var(_, Some(sort)) => {
            super::super::reference_like_inner_sort(sort).is_some_and(|inner| match inner {
                ExprSort::Seq => true,
                ExprSort::Datatype(id) => {
                    let name = resolve_sort_name(*id);
                    let bare = name.rsplit("::").next().unwrap_or(&name);
                    is_seq_model_type(bare)
                }
                _ => false,
            })
        }
        PureExpr::View(_) => true,
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            receiver_is_seq_like(inner)
        }
        _ => super::super::resolve_view_var_name(expr, None).is_some() || expr_produces_seq(expr),
    }
}

/// Extract the `ExprSort` annotation from a receiver expression, peeling
/// through Old/Deref/Final/View wrappers to the inner Var.
pub(super) fn receiver_annotation(expr: &PureExpr) -> Option<&ExprSort> {
    match expr {
        PureExpr::Var(_, ann) => ann.as_ref(),
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => receiver_annotation(inner),
        _ => None,
    }
}

fn sort_matches(
    sort: &ExprSort,
    exact_match: &impl Fn(&ExprSort) -> bool,
    type_name_pred: &impl Fn(&str) -> bool,
) -> bool {
    if exact_match(sort) {
        return true;
    }
    match sort {
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            let bare = name.rsplit("::").next().unwrap_or(&name);
            type_name_pred(bare)
        }
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => {
            sort_matches(inner.as_ref(), exact_match, type_name_pred)
        }
        _ => false,
    }
}

fn receiver_annotation_matches(
    expr: &PureExpr,
    exact_match: impl Fn(&ExprSort) -> bool,
    type_name_pred: impl Fn(&str) -> bool,
) -> bool {
    receiver_annotation(expr).is_some_and(|sort| sort_matches(sort, &exact_match, &type_name_pred))
}

pub(super) fn receiver_is_fmap_like(expr: &PureExpr) -> bool {
    if let PureExpr::LogicFnCall { name, args } = expr {
        if let Some(field_name) = name.strip_prefix(NAMED_FIELD_LOGIC_FN_PREFIX) {
            if field_name == "frag" && args.len() == 1 && matches!(args[0], PureExpr::View(_)) {
                return true;
            }
        }
    }
    receiver_annotation_matches(
        expr,
        |sort| matches!(sort, ExprSort::FMap),
        is_fmap_model_type,
    )
}

pub(super) fn receiver_is_mapping_like(expr: &PureExpr) -> bool {
    // `set` returns `Self`: a chained `m.set(..).set(..)` keeps the Mapping kind
    // of its innermost receiver. (#newfrontier)
    if let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    {
        if method == "set" && args.len() == 2 {
            return receiver_is_mapping_like(receiver);
        }
    }
    receiver_annotation_matches(expr, |_| false, is_mapping_model_type)
}

pub(super) fn receiver_is_predcell_like(expr: &PureExpr) -> bool {
    receiver_annotation_matches(expr, |_| false, |name| name == "PredCell")
}

pub(super) fn receiver_is_predcell_slice_like(expr: &PureExpr) -> bool {
    receiver_annotation_matches(expr, |_| false, type_name_is_predcell_slice)
}

pub(super) fn receiver_is_structural_field_like(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::LogicFnCall { name, .. } => {
            name.starts_with(TUPLE_FIELD_LOGIC_FN_PREFIX)
                || name.starts_with(NAMED_FIELD_LOGIC_FN_PREFIX)
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => receiver_is_structural_field_like(inner),
        _ => false,
    }
}

pub(super) fn method_call_returns_predcell_like(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::MethodCall {
            receiver, method, ..
        } => {
            matches!(method.as_str(), "index" | "index_logic")
                && receiver_is_predcell_slice_like(receiver)
        }
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            method_call_returns_predcell_like(inner)
        }
        _ => false,
    }
}

/// Returns true when the receiver annotation indicates an Option type.
/// Recognizes `ExprSort::Datatype("Option")` and qualified forms like
/// `std::option::Option`, including through `Ref`/`MutRef` wrappers.
/// Used by `infer_expr_sort` to route `unwrap`/`get` on Option receivers
/// to the correct sort inference path instead of the HIGH-risk catch-all. (#2207)
pub(super) fn receiver_is_option_like(expr: &PureExpr) -> bool {
    receiver_annotation_matches(expr, |_| false, is_option_type_name)
}

/// Returns true when the receiver annotation indicates a Result type.
/// Recognizes `ExprSort::Datatype("Result")` and qualified forms like
/// `std::result::Result`, including through `Ref`/`MutRef` wrappers.
/// Used by `infer_expr_sort` to route `unwrap`/`unwrap_err` on Result
/// receivers to the correct sort inference path. (#2207)
pub(super) fn receiver_is_result_like(expr: &PureExpr) -> bool {
    receiver_annotation_matches(expr, |_| false, is_result_type_name)
}

fn is_option_type_name(name: &str) -> bool {
    matches!(name, "Option" | "OptionInt")
}

fn is_result_type_name(name: &str) -> bool {
    matches!(name, "Result" | "ResultIntInt")
}

/// Returns true when the `ExprSort` annotation itself indicates a Seq or
/// collection type, without any fallback heuristics. Used by View sort
/// inference where the broad `receiver_is_seq_like` fallback (which considers
/// all View expressions Seq-like) would be incorrect. (#1096)
pub(super) fn annotation_is_seq_like(sort: Option<&ExprSort>) -> bool {
    match sort {
        Some(ExprSort::Seq) => true,
        Some(ExprSort::Datatype(id)) => {
            let name = resolve_sort_name(*id);
            let bare = name.rsplit("::").next().unwrap_or(&name);
            is_seq_model_type(bare)
        }
        Some(ExprSort::Ref(inner) | ExprSort::MutRef(inner)) => {
            annotation_is_seq_like(Some(inner.as_ref()))
        }
        _ => false,
    }
}

pub(super) fn receiver_annotation_is_seq_like(expr: &PureExpr) -> bool {
    match receiver_annotation(expr) {
        ann @ Some(_) => annotation_is_seq_like(ann),
        None => receiver_is_seq_like(expr),
    }
}
