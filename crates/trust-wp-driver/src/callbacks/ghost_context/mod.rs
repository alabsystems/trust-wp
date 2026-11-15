// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost block context extraction and focus-variable analysis.
//!
//! Extracted from `verification.rs` as part of #1526 decomposition.
//! Split into submodules as part of #1669 decomposition.
//! Further split (#1851): span utilities → `span_utils`, substitution
//! derivation → `substitutions`.

mod closure_mir;
mod focus_vars;
mod span_utils;
mod substitutions;
mod trusted_assumptions;

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

// Re-export public API so all existing `ghost_context::foo` imports work.
pub(in crate::callbacks) use closure_mir::closure_capture_names;
pub(super) use closure_mir::{
    extract_ghost_closure_effects, extract_ghost_closure_substitutions,
    find_ghost_closure_def_ids_in_mir, rewrite_closure_substitution_capture_names,
    rewrite_ghost_closure_capture_vars,
};
use closure_mir::{
    ghost_block_capture_roots, retain_substitutions_for_names, shared_capture_names,
};
#[cfg(test)]
pub(super) use focus_vars::expr_references_focus_vars;
pub(super) use focus_vars::{
    assumption_targets_focus_vars, collect_focus_var_names, select_focus_connected_assumptions,
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
pub(super) use span_utils::{
    ghost_block_contains_cutoff, ghost_block_precedes_cutoff, rustc_span_to_source_span,
};
pub(super) use substitutions::derive_final_deref_ghost_substitutions;
use tracing::debug;
use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_index, tuple_logic_fn_arity},
    BinOp, ExprSort, PureExpr, UnOp,
};
use trust_wp_driver::StdSpec;
pub(super) use trusted_assumptions::collect_trusted_proof_assert_assumptions;
#[cfg(test)]
pub(super) use trusted_assumptions::collect_trusted_proof_assert_assumptions_for_assert;

use super::{
    proof_assert_extract::{
        collapse_idempotent_views, normalize_view_fn_calls, substitution_assumptions,
    },
    try_get_body_with_context,
};
use crate::{
    contracts::FunctionContract,
    ghost::GhostBlock,
    mir_analysis::{extract_name_substitutions_until_span_in_region, get_mir_body},
};

/// Result of ghost context extraction, separating alias facts from semantic facts.
///
/// Alias facts are equality assumptions derived from substitutions (e.g., `v == call_1`).
/// Semantic facts are postcondition-derived assumptions from ghost helper calls
/// (e.g., `len(v@) == old_len + 1` after `push_back_ghost`). (#2326)
pub(super) struct GhostContextFacts {
    pub(super) alias_facts: Vec<PureExpr>,
    pub(super) semantic_facts: Vec<PureExpr>,
}

/// Specification context for ghost block extraction (#2657).
///
/// Bundles the type context and specification maps that are constant across
/// all ghost blocks within a single function, keeping
/// `build_ghost_context_for_function` under clippy's `too_many_arguments`
/// threshold.
pub(super) struct GhostBuildContext<'a, 'tcx> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) user_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) trait_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) extern_specs: &'a HashMap<String, StdSpec>,
}

pub(super) fn build_ghost_context_for_function(
    ctx: &GhostBuildContext<'_, '_>,
    contract: &FunctionContract,
    arg_names: &[String],
    ghost_blocks: &[GhostBlock],
    focus_vars: &HashSet<String>,
    cutoff_span: Option<Span>,
    cutoff_location: Option<rustc_middle::mir::Location>,
) -> GhostContextFacts {
    let tcx = ctx.tcx;
    let user_specs = ctx.user_specs;
    let trait_specs = ctx.trait_specs;
    let extern_specs = ctx.extern_specs;
    if ghost_blocks.is_empty() || focus_vars.is_empty() {
        return GhostContextFacts {
            alias_facts: Vec::new(),
            semantic_facts: Vec::new(),
        };
    }

    let Some(body_with_facts) = try_get_body_with_context(tcx, contract.local_def_id) else {
        return GhostContextFacts {
            alias_facts: Vec::new(),
            semantic_facts: Vec::new(),
        };
    };
    let mir_body = get_mir_body(&body_with_facts);

    let selected_cutoff_block_lo = cutoff_span.and_then(|cutoff| {
        ghost_blocks
            .iter()
            .filter(|block| {
                block.containing_fn == contract.local_def_id
                    && ghost_block_contains_cutoff(block.span, cutoff)
            })
            .map(|block| block.span.source_callsite().lo())
            .max()
    });

    let mut matching_blocks: Vec<(&GhostBlock, bool)> = ghost_blocks
        .iter()
        .filter_map(|block| {
            if block.containing_fn != contract.local_def_id {
                return None;
            }
            match cutoff_span {
                None => Some((block, false)),
                Some(cutoff) => {
                    let block_callsite = block.span.source_callsite();
                    if selected_cutoff_block_lo
                        .is_some_and(|selected_lo| block_callsite.lo() == selected_lo)
                    {
                        Some((block, true))
                    } else if ghost_block_precedes_cutoff(block.span, cutoff)
                        || selected_cutoff_block_lo
                            .is_some_and(|selected_lo| block_callsite.lo() < selected_lo)
                    {
                        Some((block, false))
                    } else {
                        None
                    }
                }
            }
        })
        .collect();
    matching_blocks.sort_by_key(|(block, _)| block.span.source_callsite().lo());
    let has_matching_ghost_block = !matching_blocks.is_empty();
    let cutoff_block_capture_roots = matching_blocks.iter().find_map(|(block, contains_cutoff)| {
        (*contains_cutoff).then(|| ghost_block_capture_roots(tcx, mir_body, block.span))
    });

    let mut ghost_context = Vec::new();
    let mut semantic_facts_raw = Vec::new();
    let fact_scope = cutoff_location
        .is_some()
        .then(|| crate::mir_analysis::fact_scope::FactScope::new(mir_body));
    for (block, contains_cutoff) in matching_blocks {
        // A ghost block before the assertion speaks of the values its names
        // had when it finished: its facts hold at the assertion only where
        // the block's end dominates it, and never over a name written on a
        // path between (D-190, FactScope::stale_names_after_region). The
        // block holding the assertion is read by the walk up to it instead.
        let stale_since_block: HashSet<String> = if contains_cutoff || cutoff_span.is_none() {
            HashSet::new()
        } else {
            let stale = fact_scope
                .as_ref()
                .zip(cutoff_location)
                .and_then(|(scope, at)| scope.stale_names_after_region(block.span, at));
            let Some(stale) = stale else {
                debug!(
                    "ghost_context: block {:?} does not hold at the assertion; its facts are \
                     not stated",
                    block.span
                );
                continue;
            };
            stale
        };
        let holds_after_block = |fact: &PureExpr| {
            !fact
                .free_vars()
                .iter()
                .any(|name| stale_since_block.contains(name))
        };
        let exported_capture_names = if contains_cutoff {
            None
        } else {
            let block_capture_roots = ghost_block_capture_roots(tcx, mir_body, block.span);
            // Under cfg(trust_wp), ghost blocks expand to direct expressions
            // (Ghost::new({...})), not closures. When no closures are found in
            // the ghost block span, block_capture_roots is empty. Do NOT filter
            // by capture names in this case — the enclosing function's MIR walk
            // captures all relevant substitutions directly. Filtering with an
            // empty allowed set would discard all substitutions. (#2671)
            //
            // However, only apply this non-closure bypass for function-level
            // ghost context (cutoff_span is None). When cutoff_span is Some, we
            // are building context for a proof_assert, and non-cutoff preceding
            // blocks should remain filtered to avoid injecting irrelevant
            // substitutions that overwhelm the solver (ghost_vec regression).
            if block_capture_roots.is_empty() && cutoff_span.is_none() {
                None
            } else if block_capture_roots.is_empty() {
                // Non-closure block with a proof_assert cutoff: keep old
                // behavior — the empty capture set filters out everything,
                // relying on the cutoff block's unfiltered substitutions.
                Some(HashSet::new())
            } else {
                Some(cutoff_block_capture_roots.as_ref().map_or_else(
                    || block_capture_roots.keys().cloned().collect(),
                    |current_capture_roots| {
                        shared_capture_names(&block_capture_roots, current_capture_roots)
                    },
                ))
            }
        };
        let stop_span = if contains_cutoff {
            // For ghost blocks that contain the cutoff (proof_assert inside ghost),
            // extract only up to the proof_assert, not the entire block. (#1581)
            cutoff_span
                .expect("invariant: contains_cutoff implies cutoff_span is Some")
                .source_callsite()
                .shrink_to_lo()
        } else {
            block.span.source_callsite().shrink_to_hi()
        };
        let mut block_assumptions = Vec::new();
        debug!(
            "ghost_context: extracting enclosing-MIR substitutions for ghost block \
             (stop_span={:?}, region_span={:?}, focus_vars={:?})",
            stop_span, block.span, focus_vars,
        );
        if let Some(mut substitutions) = extract_name_substitutions_until_span_in_region(
            tcx,
            mir_body,
            arg_names,
            user_specs,
            trait_specs,
            extern_specs,
            stop_span,
            block.span,
        ) {
            debug!(
                "ghost_context: enclosing-MIR substitutions for ghost block: {:?}",
                substitutions.exprs.keys().collect::<Vec<_>>()
            );
            if let Some(allowed_names) = exported_capture_names.as_ref() {
                // fact-source: ghost_block_capture_filter
                retain_substitutions_for_names(&mut substitutions, allowed_names);
            }
            // fact-source: ghost_final_deref_derivation
            derive_final_deref_ghost_substitutions(&mut substitutions);
            debug!(
                "ghost_context: after final-deref derivation: {:?}",
                substitutions.exprs.keys().collect::<Vec<_>>()
            );
            for (k, v) in substitutions.iter() {
                debug!("  ghost_context: sub {:?} = {:?}", k, v);
            }
            let new_assumptions = substitution_assumptions(&substitutions);
            debug!(
                "ghost_context: enclosing-MIR assumptions ({}): {:?}",
                new_assumptions.len(),
                new_assumptions
                    .iter()
                    .map(|e| format!("{e}"))
                    .collect::<Vec<_>>()
            );
            // fact-source: ghost_block_facts
            block_assumptions.extend(filter_stale_mutation_alias_facts(new_assumptions));
        } else {
            debug!("ghost_context: extract_name_substitutions_until_span_in_region returned None");
        }

        // Ghost closure MIR descent: Ghost blocks are closures in MIR.
        // Assignments inside the ghost block (like `g_mut = snapshot!(...)`)
        // live in the closure's MIR body, invisible to the enclosing function's
        // MIR walk above. Descend into ghost closure MIR bodies to extract
        // additional substitutions. (#2209)
        //
        // When the proof_assert is inside this ghost block (contains_cutoff),
        // pass the cutoff span so extraction stops before the assertion — we
        // only need assignments that precede the proof_assert.
        let closure_cutoff = if contains_cutoff { cutoff_span } else { None };
        let ghost_closure_def_ids = find_ghost_closure_def_ids_in_mir(mir_body, block.span);
        debug!(
            "ghost_context: ghost_closure_def_ids count: {}",
            ghost_closure_def_ids.len()
        );
        for closure_def_id in &ghost_closure_def_ids {
            if let Some(mut closure_subs) = extract_ghost_closure_substitutions(
                tcx,
                *closure_def_id,
                closure_cutoff,
                Some(block.span),
                user_specs,
                trait_specs,
                extern_specs,
            ) {
                // Rewrite closure-internal names (e.g., `self.0`, `*self.0`)
                // to source-level capture names (e.g., `g2`, `*g2`) so that
                // downstream filtering and assumption generation use the
                // correct variable names. (#2671)
                let capture_names = closure_capture_names(tcx, *closure_def_id);
                rewrite_closure_substitution_capture_names(&mut closure_subs, &capture_names);
                if let Some(allowed_names) = exported_capture_names.as_ref() {
                    retain_substitutions_for_names(&mut closure_subs, allowed_names);
                }
                derive_final_deref_ghost_substitutions(&mut closure_subs);
                // fact-source: ghost_block_facts
                block_assumptions.extend(filter_stale_mutation_alias_facts(
                    substitution_assumptions(&closure_subs),
                ));
            }
        }

        // Extract semantic facts from ghost closure effects (#2326).
        // The substitution pipeline above only captures alias equalities (e.g.,
        // `v == call_1`). Ghost helper calls (push_back_ghost, len_ghost, etc.)
        // also produce postcondition-derived assumptions that the substitution
        // pipeline discards. Use the return-expr extraction pipeline to capture
        // those CallEffects.assumptions as semantic facts.
        for closure_def_id in &ghost_closure_def_ids {
            let capture_names = closure_capture_names(tcx, *closure_def_id);
            let closure_semantic_facts = extract_ghost_closure_effects(
                tcx,
                *closure_def_id,
                closure_cutoff,
                user_specs,
                trait_specs,
                extern_specs,
            )
            .assumptions;
            // fact-source: ghost_block_facts
            semantic_facts_raw.extend(
                closure_semantic_facts
                    .into_iter()
                    .map(|fact| rewrite_ghost_closure_capture_vars(&fact, &capture_names))
                    .map(normalize_ghost_context_fact)
                    .filter(|fact| assumption_targets_focus_vars(fact, focus_vars))
                    .filter(|fact| holds_after_block(fact)),
            );
        }

        debug!(
            "ghost_context: block_assumptions before focus filter ({}): {:?}",
            block_assumptions.len(),
            block_assumptions
                .iter()
                .map(|e| format!("{e}"))
                .collect::<Vec<_>>()
        );
        block_assumptions.retain(|fact| holds_after_block(fact));
        let focus_selected = select_focus_connected_assumptions(&block_assumptions, focus_vars);
        debug!(
            "ghost_context: focus_selected ({}): {:?}",
            focus_selected.len(),
            focus_selected
                .iter()
                .map(|e| format!("{e}"))
                .collect::<Vec<_>>()
        );
        // fact-source: ghost_context_handoff
        ghost_context.extend(focus_selected);
    }

    if cutoff_span.is_none() && has_matching_ghost_block {
        let return_tuple_facts = scalar_tuple_projection_return_facts(
            tcx,
            mir_body,
            arg_names,
            user_specs,
            trait_specs,
            extern_specs,
        );
        if !return_tuple_facts.is_empty() {
            debug!(
                "ghost_context: scalar tuple projection return facts ({}): {:?}",
                return_tuple_facts.len(),
                return_tuple_facts
                    .iter()
                    .map(|e| format!("{e}"))
                    .collect::<Vec<_>>()
            );
            // fact-source: function_level_return_tuple_facts
            ghost_context.extend(return_tuple_facts);
        }
    }

    // Keep the context deterministic and compact.
    let mut seen = HashSet::new();
    ghost_context.retain(|expr| seen.insert(format!("{expr}")));

    // Deduplicate semantic facts, excluding any that are already alias facts.
    let alias_set: HashSet<String> = ghost_context.iter().map(|e| format!("{e}")).collect();
    let mut semantic_seen = HashSet::new();
    semantic_facts_raw.retain(|expr| {
        let s = format!("{expr}");
        !alias_set.contains(&s) && semantic_seen.insert(s)
    });

    if !ghost_context.is_empty() {
        debug!(
            "ghost_context: final alias_facts ({}): {:?}",
            ghost_context.len(),
            ghost_context
                .iter()
                .map(|e| format!("{e}"))
                .collect::<Vec<_>>()
        );
    }

    GhostContextFacts {
        alias_facts: ghost_context,
        semantic_facts: semantic_facts_raw,
    }
}

fn normalize_ghost_context_fact(expr: PureExpr) -> PureExpr {
    collapse_idempotent_views(normalize_view_fn_calls(expr))
}

fn scalar_tuple_projection_return_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    mir_body: &rustc_middle::mir::Body<'tcx>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> Vec<PureExpr> {
    let outcome = crate::mir_analysis::extract_return_expr_with_context_detailed(
        tcx,
        mir_body,
        arg_names,
        user_specs,
        trait_specs,
        extern_specs,
    );
    outcome.value.map_or_else(Vec::new, |return_expr| {
        collect_scalar_tuple_projection_identity_facts(&return_expr)
    })
}

fn collect_scalar_tuple_projection_identity_facts(expr: &PureExpr) -> Vec<PureExpr> {
    let mut facts = Vec::new();
    expr.for_each_recursive(|node| {
        let PureExpr::LogicFnCall { name, args } = node else {
            return;
        };
        if tuple_field_logic_fn_index(name) != Some(0) || args.len() != 1 {
            return;
        }
        let arg = &args[0];
        if infer_scalar_tuple_projection_arg_sort(arg)
            .as_ref()
            .is_some_and(is_scalar_view_identity_sort)
        {
            facts.push(PureExpr::BinOp(
                Arc::new(node.clone()),
                BinOp::Eq,
                Arc::new(arg.clone()),
            ));
        }
    });
    facts
}

fn infer_scalar_tuple_projection_arg_sort(expr: &PureExpr) -> Option<ExprSort> {
    match expr {
        PureExpr::Bool(_) => Some(ExprSort::Bool),
        PureExpr::Int(_) => Some(ExprSort::Int),
        PureExpr::Float(bits) => bits.width().map(ExprSort::Float),
        PureExpr::Var(_, sort) => sort.clone(),
        PureExpr::BinOp(_, op, _) => match op {
            BinOp::Eq
            | BinOp::Ne
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::And
            | BinOp::Or
            | BinOp::Implies => Some(ExprSort::Bool),
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
            | BinOp::BitOr => Some(ExprSort::Int),
            #[allow(unreachable_patterns)]
            _ => None,
        },
        PureExpr::UnOp(UnOp::Not, _) => Some(ExprSort::Bool),
        PureExpr::UnOp(UnOp::Neg, _) => Some(ExprSort::Int),
        PureExpr::Ite(_, then_expr, else_expr) => infer_scalar_tuple_projection_arg_sort(then_expr)
            .or_else(|| infer_scalar_tuple_projection_arg_sort(else_expr)),
        PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner)
        | PureExpr::Deref(inner) => infer_scalar_tuple_projection_arg_sort(inner),
        // A machine bit operation at its type (D-242) is an integer, as the
        // bare operator it wraps is.
        PureExpr::LogicFnCall { name, .. }
            if trust_wp_core::formula::internal::machine_bitop::parse(name).is_some() =>
        {
            Some(ExprSort::Int)
        }
        PureExpr::LogicFnCall { name, .. } => tuple_logic_fn_arity(name)
            .and_then(|arity| u8::try_from(arity).ok().map(ExprSort::Tuple)),
        PureExpr::Forall { .. } | PureExpr::Exists { .. } => Some(ExprSort::Bool),
        PureExpr::Match { arms, .. } => arms
            .iter()
            .find_map(|arm| infer_scalar_tuple_projection_arg_sort(&arm.body)),
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. }
        | PureExpr::Closure { body, .. } => infer_scalar_tuple_projection_arg_sort(body),
        PureExpr::MethodCall { method, .. } => infer_scalar_method_call_sort(method),
        #[allow(unreachable_patterns)]
        _ => None,
    }
}

fn infer_scalar_method_call_sort(method: &str) -> Option<ExprSort> {
    match method {
        "is_some" | "is_none" | "is_ok" | "is_err" | "contains" | "precondition"
        | "postcondition" | "postcondition_mut" | "postcondition_once" => Some(ExprSort::Bool),
        "len" | "len_logic" | "sum" | "discriminant" => Some(ExprSort::Int),
        _ => None,
    }
}

fn is_scalar_view_identity_sort(sort: &ExprSort) -> bool {
    matches!(
        sort,
        ExprSort::Int | ExprSort::Bool | ExprSort::Float(_) | ExprSort::Unit
    )
}

fn filter_stale_mutation_alias_facts(facts: Vec<PureExpr>) -> Vec<PureExpr> {
    facts
        .into_iter()
        .filter(|fact| {
            !is_stale_mutation_alias_fact(fact) && !is_stale_closure_capture_env_fact(fact)
        })
        .collect()
}

fn is_stale_mutation_alias_fact(expr: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    is_self_final_alias(lhs, rhs) || is_self_final_alias(rhs, lhs)
}

fn is_stale_closure_capture_env_fact(expr: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    is_stale_double_final_capture_alias(lhs, rhs) || is_stale_double_final_capture_alias(rhs, lhs)
}

fn is_stale_double_final_capture_alias(capture_candidate: &PureExpr, rhs: &PureExpr) -> bool {
    let PureExpr::Var(_, _) = capture_candidate else {
        return false;
    };
    let PureExpr::LogicFnCall { name, args } = rhs else {
        return false;
    };
    if name != "__trust_wp_tuple1" {
        return false;
    }
    args.iter().any(contains_nested_final)
}

fn contains_nested_final(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Final(inner) => {
            matches!(inner.as_ref(), PureExpr::Final(_)) || contains_nested_final(inner)
        }
        PureExpr::BinOp(lhs, _, rhs) => contains_nested_final(lhs) || contains_nested_final(rhs),
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::View(inner) => contains_nested_final(inner),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            contains_nested_final(cond)
                || contains_nested_final(then_expr)
                || contains_nested_final(else_expr)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            triggers.iter().flatten().any(contains_nested_final) || contains_nested_final(body)
        }
        PureExpr::Match { scrutinee, arms } => {
            contains_nested_final(scrutinee)
                || arms.iter().any(|arm| contains_nested_final(&arm.body))
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            contains_nested_final(receiver) || args.iter().any(contains_nested_final)
        }
        PureExpr::Closure { body, .. } => contains_nested_final(body),
        PureExpr::Let { value, body, .. } => {
            contains_nested_final(value) || contains_nested_final(body)
        }
        PureExpr::LetAssume { assumption, body } => {
            contains_nested_final(assumption) || contains_nested_final(body)
        }
        PureExpr::LetObligation { obligation, body } => {
            contains_nested_final(obligation) || contains_nested_final(body)
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => false,
        #[allow(unreachable_patterns)]
        _ => false,
    }
}

fn is_self_final_alias(pre: &PureExpr, post: &PureExpr) -> bool {
    let PureExpr::Var(pre_name, _) = pre else {
        return false;
    };
    let PureExpr::Final(inner) = post else {
        return false;
    };
    matches!(inner.as_ref(), PureExpr::Var(post_name, _) if post_name == pre_name)
}

#[cfg(test)]
mod focus_vars_tests;
#[cfg(test)]
mod ghost_context_subst_tests;
