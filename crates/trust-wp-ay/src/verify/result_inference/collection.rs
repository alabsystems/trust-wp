// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Collection-sort inference from postconditions.

use ay_dpll::api::Sort;
use trust_wp_core::formula::{BinOp, PureExpr};

use super::shared::expr_contains_result_var;
use crate::encoder::{infer_expr_sort, sort_context::is_seq_family_sort, AYEncoder};

/// Infer a collection sort (Seq/FMap) for `result` from postconditions.
///
/// When postconditions contain `result == <expr>` where `<expr>` is a
/// Seq/FMap-returning expression (e.g., `result == s.reverse()`),
/// this returns the collection sort so `result` can be declared correctly.
/// Without this, `result` defaults to Int, causing ay sort mismatch panics
/// on `eq(Int, Seq)`. (#2116)
pub(crate) fn result_collection_sort_from_postcondition(ensures: &[PureExpr]) -> Option<Sort> {
    for ensure in ensures {
        if let Some(sort) = expr_collection_sort_for_result(ensure) {
            return Some(sort);
        }
    }
    None
}

/// Context-aware collection sort inference for `result` from postconditions.
///
/// Unlike [`result_collection_sort_from_postcondition`], this helper can use
/// encoder state to recover collection sorts from declared variables and sort
/// hints. This matters for proof_assert VCs that use receiver-style collection
/// methods like `result.ext_eq(m_snap)` instead of an explicit
/// `result == <collection_expr>` equality. (#2116)
pub(crate) fn result_collection_sort_from_postcondition_with_context(
    encoder: &mut AYEncoder,
    ensures: &[PureExpr],
) -> Option<Sort> {
    if let Some(sort) = result_collection_sort_from_postcondition(ensures) {
        return Some(sort);
    }
    for ensure in ensures {
        if let Some(sort) = expr_collection_sort_for_result_with_context(encoder, ensure) {
            return Some(sort);
        }
    }
    None
}

fn is_collection_sort(sort: &Sort) -> bool {
    is_seq_family_sort(sort) || matches!(sort, Sort::Uninterpreted(name) if name == "FMap")
}

/// Normalize a collection sort to the canonical form the encoder uses.
///
/// FMap is already canonical as `Uninterpreted("FMap")` - pass through
/// explicitly to document the handling and prevent accidental regression
/// if a parameterized FMap sort is introduced later. (#2624)
///
/// Seq uses native `Sort::Seq(Int)` throughout (#2080) - no legacy
/// `Uninterpreted("Seq")` normalization needed.
fn normalize_collection_sort(sort: Sort) -> Sort {
    match &sort {
        Sort::Uninterpreted(name) if name == "FMap" => sort,
        _ => sort,
    }
}

fn expr_collection_sort_for_result(expr: &PureExpr) -> Option<Sort> {
    let mut inferred = None;
    expr.for_each_recursive(|node| {
        if inferred.is_some() {
            return;
        }
        let PureExpr::BinOp(left, op, right) = node else {
            return;
        };
        if !matches!(op, BinOp::Eq | BinOp::Ne) {
            return;
        }
        if expr_contains_result_var(left) {
            let sort = infer_expr_sort(right);
            if is_collection_sort(&sort) {
                inferred = Some(normalize_collection_sort(sort));
                return;
            }
        }
        if expr_contains_result_var(right) {
            let sort = infer_expr_sort(left);
            if is_collection_sort(&sort) {
                inferred = Some(normalize_collection_sort(sort));
            }
        }
    });
    inferred
}

fn expr_collection_sort_for_result_with_context(
    encoder: &mut AYEncoder,
    expr: &PureExpr,
) -> Option<Sort> {
    let mut inferred = None;
    expr.for_each_recursive(|node| {
        if inferred.is_some() {
            return;
        }
        match node {
            PureExpr::BinOp(left, BinOp::Eq | BinOp::Ne, right) => {
                if expr_contains_result_var(left) {
                    let sort = encoder.infer_expr_sort_with_context(right, None);
                    if is_collection_sort(&sort) {
                        inferred = Some(normalize_collection_sort(sort));
                        return;
                    }
                }
                if expr_contains_result_var(right) {
                    let sort = encoder.infer_expr_sort_with_context(left, None);
                    if is_collection_sort(&sort) {
                        inferred = Some(normalize_collection_sort(sort));
                    }
                }
            }
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } if expr_contains_result_var(receiver) => {
                inferred = infer_collection_sort_from_result_receiver_method(encoder, method, args);
            }
            _ => {}
        }
    });
    inferred
}

fn infer_collection_sort_from_result_receiver_method(
    encoder: &mut AYEncoder,
    method: &str,
    args: &[PureExpr],
) -> Option<Sort> {
    match method {
        "ext_eq" if args.len() == 1 => {
            let sort = encoder.infer_expr_sort_with_context(&args[0], None);
            if is_collection_sort(&sort) {
                Some(normalize_collection_sort(sort))
            } else {
                None
            }
        }
        _ => None,
    }
}
