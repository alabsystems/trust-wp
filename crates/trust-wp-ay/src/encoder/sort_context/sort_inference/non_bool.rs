// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Non-Bool determination for pure expressions.
//!
//! Determines whether a `PureExpr` is *structurally* known to be non-Bool.
//! Used by `Not` sort inference (logical vs bitwise negation) and by the
//! verification pipeline to distinguish Bool formulas from Int terms.
//!
//! Extracted from the parent `sort_inference` module. Part of #1988.

use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_logic_fn_arity, BinOp, PureExpr, UnOp,
};

use super::{expr_sort_to_ay_sort, reference_like_inner_sort};
use crate::encoder::seq::method_produces_seq_unconditional;

/// Returns `true` when the expression is *structurally* known to produce a
/// non-Bool sort (Int, Seq, FMap, Datatype, etc.). Used by `UnOp::Not` to
/// distinguish logical negation (Bool -> Bool) from bitwise NOT (Int -> Int).
pub(crate) fn is_definitely_non_bool(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Int(_) | PureExpr::Float(_) => true,
        PureExpr::BinOp(_, op, _) => matches!(
            op,
            BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::Div
                | BinOp::Mod
                | BinOp::DivTrunc
                | BinOp::RemTrunc
                | BinOp::Shl
                | BinOp::Shr
                | BinOp::BitAnd
                | BinOp::BitXor
                | BinOp::BitOr
        ),
        PureExpr::UnOp(UnOp::Neg, _) | PureExpr::UnOp(UnOp::BitNot, _) => true,
        PureExpr::MethodCall { method, .. } if method == "into_seq" => true,
        PureExpr::MethodCall { method, .. } if method_produces_seq_unconditional(method) => true,
        PureExpr::MethodCall {
            receiver,
            method,
            args,
            ..
        } if method == "empty"
            && args.is_empty()
            && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "Seq" || name == "FMap") =>
        {
            true
        }
        PureExpr::MethodCall { method, .. }
            if matches!(
                method.as_str(),
                "len"
                    | "len_logic"
                    | "pow2"
                    | "sum"
                    | "discriminant"
                    | "namespace"
                    | "capacity"
                    | "abs"
                    | "min"
                    | "max"
                    | "clamp"
                    | "count"
                    | "position"
                    | "count_ones"
                    | "count_zeros"
                    | "leading_zeros"
                    | "trailing_zeros"
                    | "saturating_add"
                    | "saturating_sub"
                    | "saturating_mul"
                    | "wrapping_add"
                    | "wrapping_sub"
                    | "wrapping_mul"
            ) =>
        {
            true
        }
        // checked_* return Option (Datatype) — not Bool.
        PureExpr::MethodCall { method, .. }
            if matches!(
                method.as_str(),
                "checked_add"
                    | "checked_sub"
                    | "checked_mul"
                    | "checked_div"
                    | "checked_rem"
                    | "checked_neg"
                    | "checked_shl"
                    | "checked_shr"
                    | "checked_pow"
            ) =>
        {
            true
        }
        // overflowing_* return Tuple2 — not Bool.
        PureExpr::MethodCall { method, .. }
            if matches!(
                method.as_str(),
                "overflowing_add"
                    | "overflowing_sub"
                    | "overflowing_mul"
                    | "overflowing_neg"
                    | "overflowing_shl"
                    | "overflowing_shr"
                    | "overflowing_pow"
            ) =>
        {
            true
        }
        PureExpr::LogicFnCall { name, .. }
            if matches!(
                name.as_str(),
                "seq" | "Seq::singleton" | "seq_empty" | "Seq::empty"
            ) =>
        {
            true
        }
        // FMap-producing logic functions are not Bool. (#994 Phase 2c)
        PureExpr::LogicFnCall { name, .. }
            if matches!(
                name.as_str(),
                "fmap_insert" | "fmap_merge" | "fmap_empty" | "FMap::empty"
            ) =>
        {
            true
        }
        // Mapping-producing logic functions are not Bool. (#2663)
        PureExpr::LogicFnCall { name, .. }
            if matches!(
                name.as_str(),
                "mapping_cst" | "mapping_set" | "mapping_empty" | "Mapping::cst"
            ) =>
        {
            true
        }
        // Int-returning logic functions are not Bool. (#2663)
        PureExpr::LogicFnCall { name, .. }
            if matches!(name.as_str(), "fmap_len" | "fmap_lookup" | "mapping_get") =>
        {
            true
        }
        // Option/Result constructors produce Datatype sorts, not Bool. (#2207)
        PureExpr::LogicFnCall { name, .. }
            if crate::encoder::match_enc::stdlib_constructor_target(name).is_some() =>
        {
            true
        }
        PureExpr::LogicFnCall { name, .. } if tuple_logic_fn_arity(name).is_some() => true,
        PureExpr::Var(_, Some(sort)) => {
            !matches!(expr_sort_to_ay_sort(sort), ay_dpll::api::Sort::Bool)
        }
        // View and Old recurse like identity wrappers. (#2057)
        PureExpr::View(inner) | PureExpr::Old(inner) => is_definitely_non_bool(inner),
        PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            super::extract_inner_var_annotation(inner)
                .and_then(reference_like_inner_sort)
                .map_or_else(
                    || is_definitely_non_bool(inner),
                    |sort| !matches!(expr_sort_to_ay_sort(sort), ay_dpll::api::Sort::Bool),
                )
        }
        _ => false,
    }
}
