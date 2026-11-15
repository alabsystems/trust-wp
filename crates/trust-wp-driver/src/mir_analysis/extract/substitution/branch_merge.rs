// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SwitchInt branch merge for proof-assert substitution extraction.
//!
//! When a `proof_assert!` follows a multi-arm match, the substitution walker
//! must collect variable values from *all* reachable branches and merge them
//! into ITE (if-then-else) chains. Without this, variables like `y` in
//! `let y = match x { -1 => -1, _ => x }; proof_assert!(x == y)` get a
//! single-branch value (`y = -1`) instead of the correct
//! `y = ite(x == -1, -1, x)`. (#1965)

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_middle::mir::{BasicBlock, Body, Operand, SwitchTargets};
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use super::{
    super::{
        super::translate::{operand_int_ty, switch_value_to_expr, translate_operand},
        NameSubstitutions,
    },
    extract_substitution_outcome_from_block, extract_substitutions_from_block,
    name_bindings::{build_name_substitutions, current_name_exprs},
    state::block_can_reach_substitution_cutoff,
    SubstitutionCutoff, SubstitutionExtractionContext, SubstitutionState,
};

/// Merge substitutions from all reachable SwitchInt branches into ITE chains.
///
/// For a match like `match x { -1 => y = -1, 127 => y = 127, _ => y = x }`,
/// this produces `y = ite(x == -1, -1, ite(x == 127, 127, x))` instead of
/// following only one branch. (#1965)
///
/// Falls back to single-branch behavior when:
/// - The discriminant expression cannot be translated
/// - The discriminant integer type is unknown
/// - Only one branch reaches the cutoff
/// - No branch produces substitutions
pub(super) fn merge_switchint_substitutions<'tcx>(
    body: &Body<'tcx>,
    discr: &Operand<'tcx>,
    targets: &SwitchTargets,
    st: &SubstitutionState,
    cutoff: SubstitutionCutoff,
    arg_names: &[String],
    ctx: &SubstitutionExtractionContext<'_, 'tcx>,
) -> Option<NameSubstitutions> {
    let reachable: Vec<BasicBlock> = targets
        .all_targets()
        .iter()
        .copied()
        .filter(|target| block_can_reach_substitution_cutoff(body, *target, &cutoff))
        .collect();

    // Single branch or no reachable targets: fall back to first-match behavior.
    if reachable.len() <= 1 {
        let candidates = if reachable.is_empty() {
            targets.all_targets().to_vec()
        } else {
            reachable
        };
        return first_reachable_substitution(body, &candidates, st, cutoff, arg_names, ctx);
    }

    // Need discriminant expression and int type for building ITE conditions.
    // If the discriminant cannot be translated, fall back to first-match behavior.
    let Some(discr_expr) = translate_operand(discr, &st.local_exprs) else {
        return first_reachable_substitution(body, &reachable, st, cutoff, arg_names, ctx);
    };
    let discr_int_ty = operand_int_ty(discr, body);

    // Collect (arm guard, BasicBlock) for each non-otherwise target. An
    // arm's guard is `discr == K` with `K` value-exact however wide
    // (`switch_value_to_expr`: `1u128 << 100`, `i128::MIN`). An arm whose
    // value has no exact term is still merged, under a guard nothing
    // constrains: dropping it (as the old i64-only skip did) folded its
    // writes into the otherwise branch, and `*x = 0; match v { 1 << 100 =>
    // *x = 5, _ => {} }` then read `*x == 0` on every path (D-186).
    let otherwise_bb = targets.otherwise();
    let mut valued_arms: Vec<(PureExpr, BasicBlock)> = Vec::new();
    for (value, target) in targets.iter() {
        if !reachable.contains(&target) {
            continue;
        }
        let value_expr = match discr_int_ty {
            Some(ty) => switch_value_to_expr(value, ty),
            None => i64::try_from(value).ok().map(PureExpr::Int),
        };
        let guard = match value_expr {
            Some(value_expr) => PureExpr::BinOp(
                Arc::new(discr_expr.clone()),
                BinOp::Eq,
                Arc::new(value_expr),
            ),
            None => PureExpr::Var(
                format!("$unrepresented_switch_arm_{}", target.as_u32()),
                Some(ExprSort::Bool),
            ),
        };
        valued_arms.push((guard, target));
    }

    // Collect substitutions from all reachable branches.
    let mut branch_subs: Vec<(Option<PureExpr>, NameSubstitutions)> = Vec::new();
    let mut cycle_only_failure = false;
    for (guard, target) in valued_arms {
        let outcome = extract_substitution_outcome_from_block(
            body,
            target,
            st.clone(),
            cutoff,
            arg_names,
            ctx,
        );
        cycle_only_failure |= outcome.failed_only_due_to_cycle;
        if let Some(subs) = outcome.substitutions {
            branch_subs.push((Some(guard), subs));
        }
    }
    // Otherwise (default) branch.
    if reachable.contains(&otherwise_bb) {
        let outcome = extract_substitution_outcome_from_block(
            body,
            otherwise_bb,
            st.clone(),
            cutoff,
            arg_names,
            ctx,
        );
        cycle_only_failure |= outcome.failed_only_due_to_cycle;
        if let Some(subs) = outcome.substitutions {
            branch_subs.push((None, subs));
        }
    }

    if branch_subs.is_empty() {
        return None;
    }
    if branch_subs.len() == 1 {
        // Safe: len() == 1 guarantees next() is Some.
        return branch_subs.into_iter().next().map(|(_, subs)| {
            if cycle_only_failure {
                let fallback_exprs = current_branch_fallbacks(body, arg_names, st, ctx);
                symbolize_cycle_recovered_fallbacks(subs, &fallback_exprs)
            } else {
                subs
            }
        });
    }

    let fallback_exprs = current_branch_fallbacks(body, arg_names, st, ctx);

    // Merge: for each variable name across all branches, build an ITE chain.
    Some(build_ite_merged_substitutions(
        &branch_subs,
        &fallback_exprs,
    ))
}

/// Build ITE-merged substitutions from collected branch data.
///
/// For each variable name that appears in any branch, constructs a nested ITE
/// expression: `ite(guard1, arm1_expr, ite(guard2, ..., default))`, each
/// guard an arm's `discr == K` (or an unconstrained symbol for an arm whose
/// value has no exact term).
pub(super) fn build_ite_merged_substitutions(
    branch_subs: &[(Option<PureExpr>, NameSubstitutions)],
    fallback_exprs: &HashMap<String, PureExpr>,
) -> NameSubstitutions {
    // Collect all variable names that appear in any branch.
    let mut all_names: HashSet<String> = HashSet::new();
    for (_, subs) in branch_subs {
        all_names.extend(subs.keys().cloned());
    }

    // Separate the otherwise branch (default) from valued arms.
    let mut default_subs: Option<&NameSubstitutions> = None;
    let mut valued_subs: Vec<(&PureExpr, &NameSubstitutions)> = Vec::new();
    for (guard, subs) in branch_subs {
        match guard {
            Some(guard) => valued_subs.push((guard, subs)),
            None => default_subs = Some(subs),
        }
    }

    let mut merged: HashMap<String, PureExpr> = HashMap::new();
    for name in &all_names {
        // Find the default (otherwise) value for this variable.
        let default_expr = default_subs
            .and_then(|d| d.get(name))
            .cloned()
            .unwrap_or_else(|| fallback_expr_for_name(name, fallback_exprs));

        // Build nested ITE from the valued arms in order.
        let mut result = default_expr;
        for &(guard, subs) in valued_subs.iter().rev() {
            if let Some(arm_expr) = subs.get(name) {
                // Only add ITE if the arm value differs from the current result.
                if arm_expr != &result {
                    result = PureExpr::Ite(
                        Arc::new(guard.clone()),
                        Arc::new(arm_expr.clone()),
                        Arc::new(result),
                    );
                }
            }
        }
        merged.insert(name.clone(), result);
    }

    NameSubstitutions::new(merged, merge_name_sorts(branch_subs))
}

fn current_branch_fallbacks<'tcx>(
    body: &Body<'tcx>,
    arg_names: &[String],
    st: &SubstitutionState,
    ctx: &SubstitutionExtractionContext<'_, 'tcx>,
) -> HashMap<String, PureExpr> {
    let mut fallback_exprs = current_name_exprs(body, arg_names, &st.local_exprs);
    fallback_exprs.extend(build_name_substitutions(
        body,
        arg_names,
        ctx.closure_capture_names.as_deref(),
        &st.local_exprs,
        &st.deref_exprs,
        &st.borrow_of,
        &st.name_updates,
    ));
    fallback_exprs
}

fn fallback_expr_for_name(name: &str, fallback_exprs: &HashMap<String, PureExpr>) -> PureExpr {
    fallback_exprs
        .get(name)
        .cloned()
        .or_else(|| symbolic_expr_for_substitution_key(name, fallback_exprs))
        .unwrap_or_else(|| PureExpr::Var(name.to_string(), None))
}

fn symbolic_expr_for_substitution_key(
    name: &str,
    fallback_exprs: &HashMap<String, PureExpr>,
) -> Option<PureExpr> {
    if let Some(base) = name.strip_prefix("^*") {
        return Some(PureExpr::Final(Arc::new(PureExpr::Deref(Arc::new(
            symbolic_source_var(base, fallback_exprs),
        )))));
    }
    if let Some(base) = name.strip_prefix("^^") {
        return Some(PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(
            symbolic_source_var(base, fallback_exprs),
        )))));
    }
    if let Some(base) = name.strip_prefix('^') {
        return Some(PureExpr::Final(Arc::new(symbolic_source_var(
            base,
            fallback_exprs,
        ))));
    }
    if let Some(base) = name.strip_prefix('*') {
        return Some(PureExpr::Deref(Arc::new(symbolic_source_var(
            base,
            fallback_exprs,
        ))));
    }
    if is_simple_ident(name) {
        return Some(symbolic_source_var(name, fallback_exprs));
    }
    None
}

fn symbolic_source_var(name: &str, fallback_exprs: &HashMap<String, PureExpr>) -> PureExpr {
    let sort = fallback_exprs.get(name).and_then(base_var_sort);
    PureExpr::Var(name.to_string(), sort)
}

fn base_var_sort(expr: &PureExpr) -> Option<ExprSort> {
    match expr {
        PureExpr::Var(_, sort) => sort.clone(),
        _ => None,
    }
}

fn is_simple_ident(name: &str) -> bool {
    // A renamed shadowed binding names a source binding too (D-237).
    crate::mir_analysis::binding_identity::is_binding_ident(name)
}

/// Branch targets and reachability for a boolean SwitchInt.
///
/// Bundles the then/else basic blocks with their cutoff-reachability flags
/// to reduce parameter counts in [`merge_bool_switchint_substitutions`]. (#2657)
pub(super) struct BoolBranchTargets {
    pub(super) then_bb: BasicBlock,
    pub(super) else_bb: BasicBlock,
    pub(super) then_reaches: bool,
    pub(super) else_reaches: bool,
}

/// Merge substitutions from Bool SwitchInt (if/else) into ITE expressions.
///
/// When both then and else branches reach the cutoff, merges their substitutions
/// into `ite(condition, then_val, else_val)`. Falls back to first-match behavior
/// when only one branch reaches the cutoff or the condition cannot be translated.
/// (#1965)
pub(super) fn merge_bool_switchint_substitutions<'tcx>(
    body: &Body<'tcx>,
    discr: &Operand<'tcx>,
    branches: &BoolBranchTargets,
    st: &SubstitutionState,
    cutoff: SubstitutionCutoff,
    arg_names: &[String],
    ctx: &SubstitutionExtractionContext<'_, 'tcx>,
) -> Option<NameSubstitutions> {
    if branches.then_reaches && branches.else_reaches {
        let condition = translate_operand(discr, &st.local_exprs);
        let then_outcome = extract_substitution_outcome_from_block(
            body,
            branches.then_bb,
            st.clone(),
            cutoff,
            arg_names,
            ctx,
        );
        let else_outcome = extract_substitution_outcome_from_block(
            body,
            branches.else_bb,
            st.clone(),
            cutoff,
            arg_names,
            ctx,
        );
        let then_failed_only_due_to_cycle = then_outcome.failed_only_due_to_cycle;
        let else_failed_only_due_to_cycle = else_outcome.failed_only_due_to_cycle;
        let then_substitutions = then_outcome.substitutions;
        let else_substitutions = else_outcome.substitutions;
        match (condition, then_substitutions, else_substitutions) {
            (Some(cond), Some(then_map), Some(else_map)) => {
                let fallback_exprs = current_branch_fallbacks(body, arg_names, st, ctx);
                Some(build_bool_ite_merged_substitutions(
                    &cond,
                    &then_map,
                    &else_map,
                    &fallback_exprs,
                ))
            }
            (_, Some(subs), None) if else_failed_only_due_to_cycle => {
                let fallback_exprs = current_branch_fallbacks(body, arg_names, st, ctx);
                Some(symbolize_cycle_recovered_fallbacks(subs, &fallback_exprs))
            }
            (_, None, Some(subs)) if then_failed_only_due_to_cycle => {
                let fallback_exprs = current_branch_fallbacks(body, arg_names, st, ctx);
                Some(symbolize_cycle_recovered_fallbacks(subs, &fallback_exprs))
            }
            (_, Some(subs), None) | (_, None, Some(subs)) => Some(subs),
            _ => None,
        }
    } else {
        // Only one branch reachable — fall back to first-match.
        let candidates: Vec<BasicBlock> = match (branches.then_reaches, branches.else_reaches) {
            (true, false) => vec![branches.then_bb],
            (false, true) => vec![branches.else_bb],
            (false, false) => vec![branches.then_bb, branches.else_bb],
            (true, true) => {
                // Defensive: the outer `if both_reachable` should prevent this
                // arm, but return None gracefully rather than panicking. (#2687)
                debug_assert!(
                    false,
                    "both_reachable guard should prevent (true, true) here"
                );
                return None;
            }
        };
        first_reachable_substitution(body, &candidates, st, cutoff, arg_names, ctx)
    }
}

pub(super) fn build_bool_ite_merged_substitutions(
    condition: &PureExpr,
    then_map: &NameSubstitutions,
    else_map: &NameSubstitutions,
    fallback_exprs: &HashMap<String, PureExpr>,
) -> NameSubstitutions {
    let mut all_names: HashSet<String> = HashSet::new();
    all_names.extend(then_map.keys().cloned());
    all_names.extend(else_map.keys().cloned());
    let mut merged: HashMap<String, PureExpr> = HashMap::new();
    for name in &all_names {
        let then_expr = then_map
            .get(name)
            .cloned()
            .unwrap_or_else(|| fallback_expr_for_name(name, fallback_exprs));
        let else_expr = else_map
            .get(name)
            .cloned()
            .unwrap_or_else(|| fallback_expr_for_name(name, fallback_exprs));
        if then_expr == else_expr {
            merged.insert(name.clone(), then_expr);
        } else {
            merged.insert(
                name.clone(),
                PureExpr::Ite(
                    Arc::new(condition.clone()),
                    Arc::new(then_expr),
                    Arc::new(else_expr),
                ),
            );
        }
    }
    let mut name_sorts = then_map.name_sorts.clone();
    for (name, sort) in &else_map.name_sorts {
        name_sorts
            .entry(name.clone())
            .or_insert_with(|| sort.clone());
    }
    NameSubstitutions::new(merged, name_sorts)
}

fn symbolize_cycle_recovered_fallbacks(
    mut substitutions: NameSubstitutions,
    fallback_exprs: &HashMap<String, PureExpr>,
) -> NameSubstitutions {
    let name_sorts = substitutions.name_sorts.clone();
    for (name, expr) in substitutions.iter_mut() {
        let Some(fallback_expr) = fallback_exprs.get(name) else {
            continue;
        };
        if expr != fallback_expr {
            continue;
        }
        if let Some(symbolic) = symbolic_expr_for_substitution_key(name, fallback_exprs) {
            *expr = apply_symbolic_name_sort(name, symbolic, &name_sorts);
        }
    }
    substitutions
}

fn apply_symbolic_name_sort(
    name: &str,
    expr: PureExpr,
    name_sorts: &HashMap<String, Option<ExprSort>>,
) -> PureExpr {
    match expr {
        PureExpr::Var(var, None) if var == name => {
            PureExpr::Var(var, name_sorts.get(name).cloned().flatten())
        }
        other => other,
    }
}

/// Try each candidate target in order and return the first successful substitution.
///
/// This is the old (pre-ITE-merge) behavior, used as a fallback when merge
/// preconditions aren't met (single branch, untranslatable discriminant, etc.).
fn first_reachable_substitution<'tcx>(
    body: &Body<'tcx>,
    candidates: &[BasicBlock],
    st: &SubstitutionState,
    cutoff: SubstitutionCutoff,
    arg_names: &[String],
    ctx: &SubstitutionExtractionContext<'_, 'tcx>,
) -> Option<NameSubstitutions> {
    for &target in candidates {
        if let Some(subs) =
            extract_substitutions_from_block(body, target, st.clone(), cutoff, arg_names, ctx)
        {
            return Some(subs);
        }
    }
    None
}

fn merge_name_sorts(
    branch_subs: &[(Option<PureExpr>, NameSubstitutions)],
) -> HashMap<String, Option<ExprSort>> {
    let mut merged = HashMap::new();
    for (_, substitutions) in branch_subs {
        for (name, sort) in &substitutions.name_sorts {
            merged.entry(name.clone()).or_insert_with(|| sort.clone());
        }
    }
    merged
}
