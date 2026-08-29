// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Direct unit tests for sort inference walker functions (#552 Finding 1).
//!
//! Tests `collect_seq_view_names`, `collect_bool_hints`, and
//! `infer_expr_sort` across all `PureExpr` variants, including the `Let`
//! variant that was previously silently ignored (fixed in this commit).

pub(super) use std::collections::HashSet;

pub(super) use ay_dpll::api::Sort;

pub(super) use super::{
    super::{
        encoder::{
            seq::collect_seq_view_names,
            sort_context::{
                classify_var_name, collect_bool_hints, infer_expr_sort, is_definitely_non_bool,
                is_derived_var_name, DerivedKind,
            },
        },
        AYEncoder, BinOp, ExprSort, Formula, Pattern, PureExpr,
    },
    helpers::*,
};

mod bool_hints;
mod constructor_preseed;
mod coverage_steps;
mod declare_var_conflicts;
mod expr_sort_calls;
mod expr_sort_method_bool;
mod expr_sort_variants;
mod fmap;
mod formula_hints;
mod let_and_match;
mod let_obligation;
mod name_resolution;
mod non_bool;
mod receiver_dispatch;
mod related_sorts;
mod related_sorts_boundary;
mod resolve_var_sort;
mod seq_theory_boundary;
mod seq_views;
mod sort_dispatch_fallback;

pub(super) use bool_hints::collect_bool_var_names;
