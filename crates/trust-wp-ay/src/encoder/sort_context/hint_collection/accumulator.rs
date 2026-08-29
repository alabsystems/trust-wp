// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use ay_dpll::api::Sort;
#[cfg(any(test, feature = "sep-logic"))]
use trust_wp_core::formula::Formula;
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr, UnOp};

#[cfg(any(test, feature = "sep-logic"))]
use super::bool_hints::collect_bool_hints;
use super::{
    super::{
        annotations::{
            expr_annotation_is_fmap, expr_annotation_is_mapping, expr_annotation_is_seq,
            expr_has_non_collection_annotation,
        },
        collection_hint_helpers::{collect_names_as_mapping, is_fmap_only_method},
        resolve_view_var_name,
        sort_inference::{infer_expr_sort_cached, mapping_sort, InferExprSortCache},
    },
    bool_hints::collect_names_as_bool,
};
use crate::encoder::{
    seq::{
        collect_view_names_as_seq, expr_produces_seq, is_seq_only_method,
        normalize_seq_receiver_for_scan,
    },
    unsoundness::{self, UnsoundnessCategory},
};

/// Whether an `ext_eq` operand has Seq evidence: explicit annotation,
/// view-shaped default (unless blocked by FMap/Mapping), or Seq-producing. (#2322)
fn ext_eq_operand_has_seq_evidence(expr: &PureExpr) -> bool {
    expr_annotation_is_seq(expr)
        || (!(expr_annotation_is_fmap(expr) || expr_annotation_is_mapping(expr))
            && (resolve_view_var_name(expr, None).is_some() || expr_produces_seq(expr)))
}

#[derive(Default)]
pub(crate) struct SortHintAccumulator {
    pub(crate) seqs: HashSet<String>,
    pub(crate) bool_vars: HashSet<String>,
    pub(crate) bool_fns: HashSet<String>,
    pub(crate) fmaps: HashSet<String>,
    pub(crate) mappings: HashSet<String>,
    /// Bare `Var` receivers of ambiguous methods (len, get, index, etc.).
    /// These are promoted to `seqs` during resolution if not also in `fmaps`.
    /// (#994: sort mismatch fix for Seq-typed variables on ambiguous methods)
    pub(crate) ambiguous_seqs: HashSet<String>,
    /// Variables appearing in Eq/Ne with an integer literal outside {0, 1}
    /// (e.g. `rc3@ == 2`). Such variables cannot be Bool under a faithful
    /// encoding; `collect_registered_sort_hints` strips them from `bool_vars`
    /// so a heuristic Bool hint minted elsewhere in the same batch (via the
    /// Eq-arm "one side infers Bool" rule) can never freeze the variable to
    /// Bool and force the literal equality premise to be fabricated away.
    /// Collected with the same name descent as `collect_names_as_bool`, so
    /// the veto set exactly covers the mint set. (arc_and_rc sort-plan flake)
    pub(crate) int_literal_eq_vars: HashSet<String>,
}

impl SortHintAccumulator {
    pub(crate) fn new() -> Self {
        Self::default()
    }
}

pub(crate) fn collect_all_sort_hints(expr: &PureExpr, acc: &mut SortHintAccumulator) {
    // Suppress SortFallbackToIntFromLogicFn: same rationale as collect_bool_hints. (#2062)
    let before = unsoundness::snapshot();
    collect_all_sort_hints_with_cache(expr, acc, &mut InferExprSortCache::default());
    unsoundness::restore_category(&before, UnsoundnessCategory::SortFallbackToIntFromLogicFn);
}

#[allow(clippy::too_many_lines)]
fn collect_all_sort_hints_with_cache(
    expr: &PureExpr,
    acc: &mut SortHintAccumulator,
    sort_cache: &mut InferExprSortCache,
) {
    match expr {
        PureExpr::UnOp(UnOp::Not, inner) => {
            collect_names_as_bool(inner, &mut acc.bool_vars, &mut acc.bool_fns);
            collect_all_sort_hints_with_cache(inner, acc, sort_cache);
        }
        PureExpr::BinOp(l, op, r) => {
            match op {
                BinOp::And | BinOp::Or | BinOp::Implies => {
                    collect_names_as_bool(l, &mut acc.bool_vars, &mut acc.bool_fns);
                    collect_names_as_bool(r, &mut acc.bool_vars, &mut acc.bool_fns);
                }
                BinOp::Eq | BinOp::Ne => {
                    if infer_expr_sort_cached(l, sort_cache) == Sort::Bool {
                        collect_names_as_bool(r, &mut acc.bool_vars, &mut acc.bool_fns);
                    }
                    if infer_expr_sort_cached(r, sort_cache) == Sort::Bool {
                        collect_names_as_bool(l, &mut acc.bool_vars, &mut acc.bool_fns);
                    }
                    // Anti-Bool evidence: `x == 2` / `x != 2` (literal outside
                    // {0,1}) proves x cannot be Bool. Collect the peer side's
                    // var names with the SAME descent used to mint Bool hints
                    // above so the veto set exactly covers the mint set; fn
                    // names are discarded (only var hints are vetoed).
                    // (arc_and_rc sort-plan flake)
                    let mut discard_fns = HashSet::new();
                    if super::super::var_collection::is_out_of_range_int_literal(l) {
                        collect_names_as_bool(r, &mut acc.int_literal_eq_vars, &mut discard_fns);
                    }
                    if super::super::var_collection::is_out_of_range_int_literal(r) {
                        collect_names_as_bool(l, &mut acc.int_literal_eq_vars, &mut discard_fns);
                    }
                    if expr_produces_seq(l) {
                        collect_view_names_as_seq(r, &mut acc.seqs);
                    }
                    if expr_produces_seq(r) {
                        collect_view_names_as_seq(l, &mut acc.seqs);
                    }
                    if infer_expr_sort_cached(l, sort_cache) == mapping_sort() {
                        collect_names_as_mapping(r, &mut acc.mappings);
                    }
                    if infer_expr_sort_cached(r, sort_cache) == mapping_sort() {
                        collect_names_as_mapping(l, &mut acc.mappings);
                    }
                }
                _ => {}
            }
            collect_all_sort_hints_with_cache(l, acc, sort_cache);
            collect_all_sort_hints_with_cache(r, acc, sort_cache);
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_names_as_bool(cond, &mut acc.bool_vars, &mut acc.bool_fns);
            if infer_expr_sort_cached(then_expr, sort_cache) == Sort::Bool {
                collect_names_as_bool(else_expr, &mut acc.bool_vars, &mut acc.bool_fns);
            }
            if infer_expr_sort_cached(else_expr, sort_cache) == Sort::Bool {
                collect_names_as_bool(then_expr, &mut acc.bool_vars, &mut acc.bool_fns);
            }
            collect_all_sort_hints_with_cache(cond, acc, sort_cache);
            collect_all_sort_hints_with_cache(then_expr, acc, sort_cache);
            collect_all_sort_hints_with_cache(else_expr, acc, sort_cache);
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let annotated_seq = expr_annotation_is_seq(receiver);
            let annotated_fmap = expr_annotation_is_fmap(receiver);
            let annotated_mapping = expr_annotation_is_mapping(receiver);
            let is_seq_only = is_seq_only_method(method);
            let is_ambiguous_method = matches!(
                method.as_str(),
                "len"
                    | "len_ghost"
                    | "index"
                    | "index_logic"
                    | "get"
                    | "get_ghost"
                    | "get_mut_ghost"
                    | "set"
                    | "sum"
                    | "contains"
                    | "contains_ghost"
            );
            let is_ambiguous_seq = is_ambiguous_method
                && !matches!(receiver.as_ref(), PureExpr::Var(_, _))
                && !annotated_fmap;
            let is_ambiguous_seq = is_ambiguous_seq && !annotated_mapping;
            // Suppress ambiguous-Seq when the receiver carries an explicit
            // non-collection annotation (e.g., ExprSort::Int for FSet variables).
            // Without this, `Final(Var("x", Some(Int))).contains(1)` would
            // register `x` as Seq, causing sort mismatches with FSet method
            // dispatch and ghost aliasing. (#2671)
            let is_ambiguous_seq =
                is_ambiguous_seq && !expr_has_non_collection_annotation(receiver);
            // When the receiver carries an authoritative Seq/FMap annotation
            // from MIR (including `Ref(Seq)` / `Ref(FMap)`), prefer it over the
            // non-Var ambiguous-method heuristic. (#2209)
            if is_seq_only || is_ambiguous_seq || annotated_seq {
                let normalized = normalize_seq_receiver_for_scan(receiver);
                if let Some(name) = resolve_view_var_name(normalized.as_ref(), None) {
                    acc.seqs.insert(name);
                }
            }
            if annotated_mapping {
                let normalized = normalize_seq_receiver_for_scan(receiver);
                if let Some(name) = resolve_view_var_name(normalized.as_ref(), None) {
                    acc.mappings.insert(name);
                }
                if let PureExpr::Var(name, _) = receiver.as_ref() {
                    acc.mappings.insert(name.clone());
                }
            }
            // Bare Var receivers of ambiguous methods: defer decision. (#994)
            // Promoted to Seq/FMap in register_sort_hints if view evidence exists.
            // Skip FMap-annotated vars: they're already added to fmaps via
            // is_annotated_fmap_ambiguous above, so adding them to ambiguous_seqs
            // is redundant. (#994)
            if is_ambiguous_method && !annotated_seq && !annotated_fmap && !annotated_mapping {
                if let PureExpr::Var(name, _) = receiver.as_ref() {
                    acc.ambiguous_seqs.insert(name.clone());
                    // Also add the view-normalized name so propagation reaches
                    // both `v` and `v_view` in the Seq hint chain.
                    let normalized = normalize_seq_receiver_for_scan(receiver);
                    if let Some(view_name) = resolve_view_var_name(normalized.as_ref(), None) {
                        acc.ambiguous_seqs.insert(view_name);
                    }
                }
            }
            // FMap-only methods tag the receiver as FMap. insert/insert_ghost
            // are arity-dependent: 2-arg → FMap, 1-arg → FSet (#2059).
            let is_fmap_insert =
                matches!(method.as_str(), "insert" | "insert_ghost") && args.len() == 2;
            let is_annotated_fmap_ambiguous = is_ambiguous_method && annotated_fmap;
            if is_fmap_only_method(method) || is_fmap_insert || is_annotated_fmap_ambiguous {
                let normalized = normalize_seq_receiver_for_scan(receiver);
                if let Some(name) = resolve_view_var_name(normalized.as_ref(), None) {
                    acc.fmaps.insert(name);
                }
                if let PureExpr::Var(name, _) = receiver.as_ref() {
                    acc.fmaps.insert(name.clone());
                }
                // merge(other_map, resolver): the first arg is also a map (#2059)
                if method == "merge" && !args.is_empty() {
                    if let Some(name) = resolve_view_var_name(&args[0], None) {
                        acc.fmaps.insert(name);
                    }
                    if let PureExpr::Var(name, _) = &args[0] {
                        acc.fmaps.insert(name.clone());
                    }
                }
            }
            if method == "concat" {
                for arg in args {
                    collect_view_names_as_seq(arg, &mut acc.seqs);
                }
            }
            if method == "ext_eq" {
                // ext_eq Seq evidence: annotation, view-shape, or Seq-producing.
                // Explicit FMap/Mapping blocks the view-shape default. (#2322)
                let receiver_seq_evidence = ext_eq_operand_has_seq_evidence(receiver);
                if receiver_seq_evidence {
                    if let Some(name) = resolve_view_var_name(receiver, None) {
                        acc.seqs.insert(name);
                    }
                }
                for arg in args {
                    if ext_eq_operand_has_seq_evidence(arg) {
                        if let Some(name) = resolve_view_var_name(arg, None) {
                            acc.seqs.insert(name);
                        }
                    }
                }
                if receiver_seq_evidence {
                    for arg in args {
                        collect_view_names_as_seq(arg, &mut acc.seqs);
                    }
                }
                for arg in args {
                    if ext_eq_operand_has_seq_evidence(arg) {
                        collect_view_names_as_seq(receiver, &mut acc.seqs);
                    }
                }
            }
            if method == "produces" && !args.is_empty() {
                if let Some(name) = resolve_view_var_name(&args[0], None) {
                    acc.seqs.insert(name);
                }
                if let PureExpr::Var(name, _) = &args[0] {
                    acc.seqs.insert(name.clone());
                }
                collect_view_names_as_seq(&args[0], &mut acc.seqs);
            }
            // `contains` is ambiguous (Seq/FMap/FSet) — handled via
            // is_ambiguous_method above, NOT unconditionally tagged as Seq.
            // The old unconditional tagging caused FSet receivers to get
            // ExprSort::Seq, misrouting FSet contains to seq_contains. (#2155)
            collect_all_sort_hints_with_cache(receiver, acc, sort_cache);
            for arg in args {
                collect_all_sort_hints_with_cache(arg, acc, sort_cache);
            }
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::UnOp(_, inner) => {
            collect_all_sort_hints_with_cache(inner, acc, sort_cache);
        }
        PureExpr::View(inner) => {
            if infer_expr_sort_cached(expr, sort_cache) == mapping_sort() {
                if let Some(name) = resolve_view_var_name(expr, None) {
                    acc.mappings.insert(name);
                }
            }
            collect_all_sort_hints_with_cache(inner, acc, sort_cache);
        }
        PureExpr::LogicFnCall { args, .. } => {
            for arg in args {
                collect_all_sort_hints_with_cache(arg, acc, sort_cache);
            }
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            ..
        }
        | PureExpr::Exists {
            var,
            var_sort,
            body,
            ..
        } => {
            // Register quantifier-bound variable sort hints from explicit
            // ExprSort annotations (#994 Step 2e, #2040).
            match var_sort {
                Some(ExprSort::Seq) => {
                    acc.seqs.insert(var.clone());
                }
                Some(ExprSort::Bool) => {
                    acc.bool_vars.insert(var.clone());
                }
                Some(ExprSort::FMap) => {
                    acc.fmaps.insert(var.clone());
                }
                // Datatype, Tuple, Unit, Ref, Int — no hint accumulator
                // needed; these are resolved via direct ExprSort annotation
                // in resolve_var_sort_or_int_with_annotation (#2039).
                _ => {}
            }
            collect_all_sort_hints_with_cache(body, acc, sort_cache);
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_all_sort_hints_with_cache(scrutinee, acc, sort_cache);
            for arm in arms {
                collect_all_sort_hints_with_cache(&arm.body, acc, sort_cache);
            }
        }
        PureExpr::Let { value, body, .. } => {
            collect_all_sort_hints_with_cache(value, acc, sort_cache);
            collect_all_sort_hints_with_cache(body, acc, sort_cache);
        }
        PureExpr::LetAssume { assumption, body } => {
            collect_all_sort_hints_with_cache(assumption, acc, sort_cache);
            collect_all_sort_hints_with_cache(body, acc, sort_cache);
        }
        PureExpr::LetObligation { obligation, body } => {
            collect_all_sort_hints_with_cache(obligation, acc, sort_cache);
            collect_all_sort_hints_with_cache(body, acc, sort_cache);
        }
        _ => {}
    }
}

#[cfg(any(test, feature = "sep-logic"))]
pub(in crate::encoder::sort_context) fn collect_formula_sort_hints(
    formula: &Formula,
    acc: &mut SortHintAccumulator,
) {
    match formula {
        Formula::Pure(expr) => {
            collect_names_as_bool(expr, &mut acc.bool_vars, &mut acc.bool_fns);
            collect_bool_hints(expr, &mut acc.bool_vars, &mut acc.bool_fns);
            collect_all_sort_hints(expr, acc);
        }
        Formula::And(l, r)
        | Formula::Or(l, r)
        | Formula::Implies(l, r)
        | Formula::SepConj(l, r)
        | Formula::MagicWand(l, r) => {
            collect_formula_sort_hints(l, acc);
            collect_formula_sort_hints(r, acc);
        }
        Formula::Forall { body, .. } | Formula::Exists { body, .. } => {
            collect_formula_sort_hints(body, acc);
        }
        Formula::True | Formula::False => {}
        Formula::PointsTo { .. } | Formula::MutBorrow { .. } => {}
        // Formula is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => {}
    }
}
