// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost closure MIR descent and capture variable resolution.
//!
//! Ghost blocks are closures in MIR. This module handles:
//! - Finding ghost closure `DefId`s by matching aggregate statements against ghost spans
//! - Descending into ghost closure MIR bodies for substitution/effect extraction
//! - Resolving and rewriting `self.N` capture variables to their source names

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::{def::DefKind, def_id::DefId, HirId};
use rustc_middle::{
    mir::{self, Body, Rvalue, StatementKind},
    ty::TyCtxt,
};
use rustc_span::Span;
use trust_wp_core::formula::PureExpr;
use trust_wp_driver::StdSpec;

use super::super::proof_assert_extract::extract_call_effects;
use crate::mir_analysis::{
    effects::CallEffects, extract_name_substitutions_until_span,
    extract_name_substitutions_until_span_in_region, extract_return_expr_with_cutoff_span,
    resolve_arg_names_or_warn, NameSubstitutions,
};

pub(super) fn closure_capture_roots(
    tcx: TyCtxt<'_>,
    closure_def_id: DefId,
) -> HashMap<String, HirId> {
    let Some(local_def_id) = closure_def_id.as_local() else {
        return HashMap::new();
    };

    let saved_names: Vec<String> = tcx
        .closure_saved_names_of_captured_variables(local_def_id.to_def_id())
        .iter()
        .map(|symbol| symbol.as_str().to_string())
        .collect();

    tcx.closure_captures(local_def_id)
        .iter()
        .enumerate()
        .map(|(idx, capture)| {
            let name = {
                let var_ident_name = capture.var_ident.as_str().to_string();
                if !var_ident_name.is_empty() && var_ident_name != "_" {
                    var_ident_name
                } else {
                    let symbol_name = capture.to_symbol().to_string();
                    if !symbol_name.is_empty() && symbol_name != "_" {
                        symbol_name
                    } else {
                        saved_names
                            .get(idx)
                            .filter(|name| !name.is_empty() && name.as_str() != "_")
                            .cloned()
                            .unwrap_or_else(|| format!("self.{idx}"))
                    }
                }
            };
            (name, capture.get_root_variable())
        })
        .collect()
}

pub(super) fn ghost_block_capture_roots(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    ghost_span: Span,
) -> HashMap<String, HirId> {
    let mut capture_roots = HashMap::new();
    for closure_def_id in find_ghost_closure_def_ids_in_mir(body, ghost_span) {
        capture_roots.extend(closure_capture_roots(tcx, closure_def_id));
    }
    capture_roots
}

pub(super) fn shared_capture_names(
    block_capture_roots: &HashMap<String, HirId>,
    current_capture_roots: &HashMap<String, HirId>,
) -> HashSet<String> {
    block_capture_roots
        .iter()
        .filter_map(|(name, root)| {
            current_capture_roots
                .get(name)
                .is_some_and(|current_root| current_root == root)
                .then_some(name.clone())
        })
        .collect()
}

pub(super) fn substitution_base_name(lhs: &str) -> &str {
    let trimmed = lhs.trim_start_matches('^');
    trimmed.strip_prefix('*').unwrap_or(trimmed)
}

pub(super) fn retain_substitutions_for_names(
    substitutions: &mut NameSubstitutions,
    allowed_names: &HashSet<String>,
) {
    substitutions
        .exprs
        .retain(|lhs, _| allowed_names.contains(substitution_base_name(lhs)));
    substitutions
        .name_sorts
        .retain(|name, _| allowed_names.contains(name));
}

/// Rewrite substitution map keys from closure-internal names (e.g., `self.0`,
/// `*self.0`) to source-level capture names (e.g., `g2`, `*g2`).
///
/// Ghost closures produce substitutions using closure-internal naming (the
/// captured variable is `self.N` inside the closure MIR). The downstream
/// `retain_substitutions_for_names` filter expects source names. Without this
/// rewriting, deref substitutions like `*self.0 -> Int(1)` from a ghost write
/// `**g2 = 1` would be filtered out because `"self.0"` is not in the allowed
/// source names set. (#2671)
///
/// Also rewrites `Var("self.N")` references in the substitution values so they
/// refer to the source name.
pub(in crate::callbacks) fn rewrite_closure_substitution_capture_names(
    substitutions: &mut NameSubstitutions,
    capture_names: &[String],
) {
    // Rewrite keys in the exprs map.
    //
    // Deterministic drain order (arc_and_rc sort-plan hygiene, part b):
    // when two ORIGINAL keys rewrite to the SAME key, last-in wins — with a
    // raw HashMap drain the winner was decided by hash-iteration order,
    // making the resulting ghost-fact shapes vary per process. Sorting by
    // the original key makes collision resolution reproducible. This is
    // safe only because the evidence-complete sort-plan veto (part a)
    // removed the order-sensitive Bool-hint mint downstream; it is pure
    // reproducibility hygiene, not the fix itself.
    let mut entries: Vec<(String, PureExpr)> = substitutions.exprs.drain().collect();
    entries.sort_by(|(left, _), (right, _)| left.cmp(right));
    for (key, value) in entries {
        let rewritten_key = rewrite_substitution_key(&key, capture_names);
        let rewritten_value = rewrite_ghost_closure_capture_vars(&value, capture_names);
        substitutions.exprs.insert(rewritten_key, rewritten_value);
    }

    // Rewrite keys in the name_sorts map (same deterministic drain order).
    let mut sort_entries: Vec<(String, Option<trust_wp_core::formula::ExprSort>)> =
        substitutions.name_sorts.drain().collect();
    sort_entries.sort_by(|(left, _), (right, _)| left.cmp(right));
    for (key, sort) in sort_entries {
        if let Some(rewritten) = rewrite_ghost_closure_capture_name(&key, capture_names) {
            substitutions.name_sorts.insert(rewritten, sort);
        } else {
            substitutions.name_sorts.insert(key, sort);
        }
    }
}

/// Rewrite a substitution key, preserving any `^` and `*` prefixes.
///
/// For example, `"*self.0"` becomes `"*g2"` and `"^*self.0"` becomes `"^*g2"`.
fn rewrite_substitution_key(key: &str, capture_names: &[String]) -> String {
    let (prefix, base) = if let Some(rest) = key.strip_prefix("^*") {
        ("^*", rest)
    } else if let Some(rest) = key.strip_prefix('*') {
        ("*", rest)
    } else if let Some(rest) = key.strip_prefix('^') {
        ("^", rest)
    } else {
        ("", key)
    };
    if let Some(rewritten) = rewrite_ghost_closure_capture_name(base, capture_names) {
        format!("{prefix}{rewritten}")
    } else {
        key.to_string()
    }
}

/// Find closure `DefId`s whose MIR aggregate statements fall within a ghost block span.
///
/// Ghost blocks are closures in MIR. The enclosing function's MIR contains
/// `Rvalue::Aggregate(AggregateKind::Closure(def_id, _), _)` statements for the
/// ghost block closure. By matching statement spans against the ghost block span,
/// we identify which closure bodies belong to a given ghost block. (#2209)
pub(in crate::callbacks) fn find_ghost_closure_def_ids_in_mir(
    body: &Body<'_>,
    ghost_span: Span,
) -> Vec<DefId> {
    let ghost = ghost_span.source_callsite();
    let mut closure_def_ids = Vec::new();
    for bb_data in body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            if let StatementKind::Assign(box (
                _,
                Rvalue::Aggregate(box mir::AggregateKind::Closure(def_id, _), _),
            )) = stmt.kind
            {
                let stmt_span = stmt.source_info.span.source_callsite();
                // The closure aggregate for the ghost block should have a span
                // that falls within (or overlaps with) the ghost block span.
                if ghost.lo() <= stmt_span.lo() && stmt_span.hi() <= ghost.hi() {
                    closure_def_ids.push(def_id);
                }
            }
        }
    }
    closure_def_ids
}

/// Extract substitutions from a ghost closure's MIR body.
///
/// Ghost blocks are closures in MIR — assignments inside the ghost block
/// (like `g_mut = snapshot!(...)`) live in the closure's MIR body, invisible
/// to the enclosing function's MIR walk. This function descends into the
/// ghost closure's MIR to extract those substitutions. (#2209)
///
/// When `cutoff_span` is `Some`, extraction stops at that span (used when a
/// proof_assert is inside the ghost block — we only want substitutions from
/// assignments that precede the assertion). When `None`, the full closure body
/// is walked.
///
/// The closure's capture variables are resolved to their source names so the
/// substitutions merge naturally with the enclosing function's variable namespace.
pub(in crate::callbacks) fn extract_ghost_closure_substitutions<'tcx>(
    tcx: TyCtxt<'tcx>,
    closure_def_id: DefId,
    cutoff_span: Option<Span>,
    region_span: Option<Span>,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> Option<NameSubstitutions> {
    if !tcx.is_mir_available(closure_def_id) {
        return None;
    }
    let Ok(closure_body) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tcx.optimized_mir(closure_def_id)
    })) else {
        return None;
    };
    let closure_arg_names = ghost_closure_arg_names(tcx, closure_def_id);

    let stop_span = match cutoff_span {
        // When a proof_assert is inside this ghost block, stop extraction at
        // the proof_assert position to capture only preceding assignments.
        Some(cutoff) => cutoff.source_callsite().shrink_to_lo(),
        // Walk the entire closure body.
        None => closure_body.span.shrink_to_hi(),
    };

    match region_span {
        Some(region_span) => extract_name_substitutions_until_span_in_region(
            tcx,
            closure_body,
            &closure_arg_names,
            user_specs,
            trait_specs,
            extern_specs,
            stop_span,
            region_span,
        ),
        None => extract_name_substitutions_until_span(
            tcx,
            closure_body,
            &closure_arg_names,
            user_specs,
            trait_specs,
            extern_specs,
            stop_span,
        ),
    }
}

pub(in crate::callbacks) fn closure_capture_names(
    tcx: TyCtxt<'_>,
    closure_def_id: DefId,
) -> Vec<String> {
    let Some(local_def_id) = closure_def_id.as_local() else {
        return Vec::new();
    };

    let saved_names: Vec<String> = tcx
        .closure_saved_names_of_captured_variables(local_def_id.to_def_id())
        .iter()
        .map(|symbol| symbol.as_str().to_string())
        .collect();

    tcx.closure_captures(local_def_id)
        .iter()
        .enumerate()
        .map(|(idx, capture)| {
            let var_ident_name = capture.var_ident.as_str().to_string();
            if !var_ident_name.is_empty() && var_ident_name != "_" {
                return var_ident_name;
            }

            let symbol_name = capture.to_symbol().to_string();
            if !symbol_name.is_empty() && symbol_name != "_" {
                return symbol_name;
            }

            saved_names
                .get(idx)
                .filter(|name| !name.is_empty() && name.as_str() != "_")
                .cloned()
                .unwrap_or_else(|| format!("self.{idx}"))
        })
        .collect()
}

fn ghost_closure_arg_names(tcx: TyCtxt<'_>, closure_def_id: DefId) -> Vec<String> {
    let mut names = resolve_arg_names_or_warn(tcx, closure_def_id, None);
    if tcx.def_kind(closure_def_id) == DefKind::Closure
        && names.first().is_none_or(|name| name != "self")
    {
        names.insert(0, "self".to_string());
    }
    names
}

fn rewrite_ghost_closure_capture_name(name: &str, capture_names: &[String]) -> Option<String> {
    // Standard closure capture pattern: `self.N` -> capture_names[N]
    if let Some(field_path) = name.strip_prefix("self.") {
        let field_idx_end = field_path.find('.').unwrap_or(field_path.len());
        let field_idx = field_path[..field_idx_end].parse::<usize>().ok()?;
        let capture_name = capture_names.get(field_idx)?;
        let suffix = &field_path[field_idx_end..];
        return Some(format!("{capture_name}{suffix}"));
    }

    // Projected reborrow carrier pattern (#2691): `__trust_wp_reborrow_<N>_deref_field<K>`
    // In closure MIR, `&mut ((*_1).K)` creates a synthetic carrier name because
    // the projected field access doesn't match the simple reborrow pattern.
    // Extract the field index K and map it to capture_names[K].
    if let Some(carrier_suffix) = name.strip_prefix("__trust_wp_reborrow_") {
        // Parse: <local_index>_deref_field<capture_index>
        if let Some(deref_pos) = carrier_suffix.find("_deref_field") {
            let field_idx_str = &carrier_suffix[deref_pos + "_deref_field".len()..];
            let field_idx = field_idx_str.parse::<usize>().ok()?;
            let capture_name = capture_names.get(field_idx)?;
            return Some(capture_name.clone());
        }
    }

    None
}

pub(in crate::callbacks) fn rewrite_ghost_closure_capture_vars(
    expr: &PureExpr,
    capture_names: &[String],
) -> PureExpr {
    match expr {
        PureExpr::Var(name, sort) => rewrite_ghost_closure_capture_name(name, capture_names)
            .map_or_else(|| expr.clone(), |name| PureExpr::Var(name, sort.clone())),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => expr.clone(),
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(rewrite_ghost_closure_capture_vars(left, capture_names)),
            *op,
            Arc::new(rewrite_ghost_closure_capture_vars(right, capture_names)),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            Arc::new(rewrite_ghost_closure_capture_vars(inner, capture_names)),
        ),
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(rewrite_ghost_closure_capture_vars(cond, capture_names)),
            Arc::new(rewrite_ghost_closure_capture_vars(then_expr, capture_names)),
            Arc::new(rewrite_ghost_closure_capture_vars(else_expr, capture_names)),
        ),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(rewrite_ghost_closure_capture_vars(
            inner,
            capture_names,
        ))),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(rewrite_ghost_closure_capture_vars(
            inner,
            capture_names,
        ))),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(rewrite_ghost_closure_capture_vars(
            inner,
            capture_names,
        ))),
        PureExpr::View(inner) => PureExpr::View(Arc::new(rewrite_ghost_closure_capture_vars(
            inner,
            capture_names,
        ))),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(rewrite_ghost_closure_capture_vars(receiver, capture_names)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| rewrite_ghost_closure_capture_vars(arg, capture_names))
                .collect(),
        },
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Forall {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: Arc::new(rewrite_ghost_closure_capture_vars(body, capture_names)),
            triggers: triggers
                .iter()
                .map(|trigger| {
                    trigger
                        .iter()
                        .map(|expr| rewrite_ghost_closure_capture_vars(expr, capture_names))
                        .collect()
                })
                .collect(),
        },
        PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => PureExpr::Exists {
            var: var.clone(),
            var_sort: var_sort.clone(),
            body: Arc::new(rewrite_ghost_closure_capture_vars(body, capture_names)),
            triggers: triggers
                .iter()
                .map(|trigger| {
                    trigger
                        .iter()
                        .map(|expr| rewrite_ghost_closure_capture_vars(expr, capture_names))
                        .collect()
                })
                .collect(),
        },
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee: Arc::new(rewrite_ghost_closure_capture_vars(scrutinee, capture_names)),
            arms: arms
                .iter()
                .map(|arm| trust_wp_core::formula::MatchArm {
                    pattern: arm.pattern.clone(),
                    body: rewrite_ghost_closure_capture_vars(&arm.body, capture_names),
                })
                .collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| rewrite_ghost_closure_capture_vars(arg, capture_names))
                .collect(),
        },
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::new(rewrite_ghost_closure_capture_vars(value, capture_names)),
            body: Arc::new(rewrite_ghost_closure_capture_vars(body, capture_names)),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(rewrite_ghost_closure_capture_vars(
                assumption,
                capture_names,
            )),
            body: Arc::new(rewrite_ghost_closure_capture_vars(body, capture_names)),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(rewrite_ghost_closure_capture_vars(
                obligation,
                capture_names,
            )),
            body: Arc::new(rewrite_ghost_closure_capture_vars(body, capture_names)),
        },
        PureExpr::Closure { params, body } => PureExpr::Closure {
            params: params.clone(),
            body: Arc::new(rewrite_ghost_closure_capture_vars(body, capture_names)),
        },
        _ => expr.clone(),
    }
}

/// Extract semantic effects from a ghost closure's MIR body.
///
/// Uses the return-expr extraction pipeline (which preserves `CallEffects`)
/// rather than the substitution pipeline (which discards them). Returns the
/// call effects — postcondition-derived assumptions from ghost helper calls
/// like `push_back_ghost`, `len_ghost`, etc., plus their matching obligations.
pub(in crate::callbacks) fn extract_ghost_closure_effects<'tcx>(
    tcx: TyCtxt<'tcx>,
    closure_def_id: DefId,
    cutoff_span: Option<Span>,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> CallEffects {
    if !tcx.is_mir_available(closure_def_id) {
        return CallEffects::new();
    }
    let Ok(closure_body) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tcx.optimized_mir(closure_def_id)
    })) else {
        return CallEffects::new();
    };
    let closure_arg_names = ghost_closure_arg_names(tcx, closure_def_id);

    let stop_span = cutoff_span.map(|cutoff| cutoff.source_callsite().shrink_to_lo());

    let (return_expr, effects) = extract_return_expr_with_cutoff_span(
        tcx,
        closure_body,
        &closure_arg_names,
        user_specs,
        trait_specs,
        extern_specs,
        stop_span,
    );
    let mut effects = effects;
    let (_, embedded_assumptions, embedded_obligations) =
        extract_call_effects(return_expr.as_ref());
    effects.assumptions.extend(embedded_assumptions);
    effects.obligations.extend(embedded_obligations);
    effects
}
