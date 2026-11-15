// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Branch handling and ITE-based state merging for loop body effects.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_middle::mir::{BasicBlock, Body, Local, Operand, SwitchTargets};
use trust_wp_core::formula::{BinOp, PureExpr, UnOp};

use super::{
    super::super::translate::{
        operand_int_ty, operand_is_bool, switch_value_to_i64, translate_operand,
    },
    BodyExtractionCtx, BodyExtractionState,
};

#[derive(Clone)]
pub(super) struct SwitchBranch {
    pub(super) target: BasicBlock,
    pub(super) condition: Option<PureExpr>,
}

impl<'a, 'tcx> BodyExtractionCtx<'a, 'tcx> {
    pub(super) fn extract_switch(
        &self,
        bb: BasicBlock,
        entered_header: bool,
        state: BodyExtractionState,
        visited: HashSet<BasicBlock>,
        discr: &Operand<'tcx>,
        targets: &SwitchTargets,
    ) -> Option<BodyExtractionState> {
        if bb == self.header {
            // Loop header SwitchInt includes an exit branch. Follow only
            // the single successor that stays inside the loop body.
            let mut in_loop_targets: Vec<BasicBlock> = targets
                .all_targets()
                .iter()
                .copied()
                .filter(|target| self.body_blocks.contains(target))
                .collect();
            in_loop_targets.sort_by_key(|target| target.as_u32());
            in_loop_targets.dedup();
            if in_loop_targets.len() != 1 {
                return None;
            }
            return self.extract_from_block(in_loop_targets[0], entered_header, state, visited);
        }

        let branches = switch_branches_for_effects(self.body, discr, targets, &state.working_exprs);

        match branches {
            Some(branches) => {
                self.extract_switch_with_branches(entered_header, state, visited, branches)
            }
            None => {
                // Discriminant not translatable (e.g., opaque Call result like
                // Vec::len()). Fall back to walking all in-loop targets and
                // conservatively merging — keep only effects that agree across
                // all branches. (#1295)
                self.extract_switch_opaque(entered_header, state, visited, targets)
            }
        }
    }

    /// Walk branches with known conditions and merge via ITE expressions.
    fn extract_switch_with_branches(
        &self,
        entered_header: bool,
        state: BodyExtractionState,
        visited: HashSet<BasicBlock>,
        branches: Vec<SwitchBranch>,
    ) -> Option<BodyExtractionState> {
        // Filter out branches that exit the loop body. A non-header SwitchInt
        // can act as the loop condition when FalseUnwind separates the header
        // from the condition block (e.g., ghost-wrapped while loops). Exit
        // branches target blocks outside body_blocks and must be skipped,
        // just like the header's exit filtering above. (#352)
        let in_loop_branches: Vec<_> = branches
            .into_iter()
            .filter(|b| self.body_blocks.contains(&b.target) || b.target == self.header)
            .collect();

        if in_loop_branches.is_empty() {
            return None;
        }
        if in_loop_branches.len() == 1 {
            return self.extract_from_block(
                in_loop_branches[0].target,
                entered_header,
                state,
                visited,
            );
        }

        // Each branch's path carries its own condition and the negation of
        // every condition tested before it, the order `merge_branch_values`
        // resolves the arms in. An arm filtered out above as a loop exit adds
        // no conjunct: the path it leaves out does not continue the iteration.
        let mut branch_results: Vec<(Option<PureExpr>, BodyExtractionState)> =
            Vec::with_capacity(in_loop_branches.len());
        let mut earlier_conditions_false: Vec<PureExpr> = Vec::new();
        for branch in in_loop_branches {
            let mut branch_entry = state.clone();
            branch_entry
                .path_guard
                .extend(earlier_conditions_false.iter().cloned());
            if let Some(condition) = &branch.condition {
                branch_entry.path_guard.push(condition.clone());
                earlier_conditions_false
                    .push(PureExpr::UnOp(UnOp::Not, Arc::new(condition.clone())));
            }
            let branch_state = self.extract_from_block(
                branch.target,
                entered_header,
                branch_entry,
                visited.clone(),
            )?;
            branch_results.push((branch.condition, branch_state));
        }

        let mut merged = merge_branch_states(branch_results, self.local_to_name)?;
        merged.path_guard = state.path_guard;
        merged.path_guard_opaque = state.path_guard_opaque;
        Some(merged)
    }

    /// Walk all in-loop SwitchInt targets when the discriminant is opaque.
    /// Uses conservative merge: only effects that are identical across all
    /// branches are kept; disagreeing effects are dropped (havoced). (#1295)
    fn extract_switch_opaque(
        &self,
        entered_header: bool,
        state: BodyExtractionState,
        visited: HashSet<BasicBlock>,
        targets: &SwitchTargets,
    ) -> Option<BodyExtractionState> {
        let mut in_loop_targets: Vec<BasicBlock> = targets
            .all_targets()
            .iter()
            .copied()
            .filter(|t| self.body_blocks.contains(t) || *t == self.header)
            .collect();
        in_loop_targets.sort_by_key(|t| t.as_u32());
        in_loop_targets.dedup();

        if in_loop_targets.is_empty() {
            return None;
        }
        if in_loop_targets.len() == 1 {
            return self.extract_from_block(in_loop_targets[0], entered_header, state, visited);
        }

        // No condition names these arms, so nothing recorded inside one can
        // be guarded by it.
        let mut branch_entry = state.clone();
        branch_entry.path_guard_opaque = true;
        let mut branch_states: Vec<BodyExtractionState> = Vec::with_capacity(in_loop_targets.len());
        for target in in_loop_targets {
            if let Some(bs) = self.extract_from_block(
                target,
                entered_header,
                branch_entry.clone(),
                visited.clone(),
            ) {
                branch_states.push(bs);
            }
            // Branches that fail extraction are skipped — the conservative
            // merge of remaining branches still produces sound effects.
        }

        if branch_states.is_empty() {
            return None;
        }
        let mut merged = if branch_states.len() == 1 {
            branch_states.into_iter().next()?
        } else {
            merge_branch_states_conservative(&branch_states)
        };
        merged.path_guard = state.path_guard;
        merged.path_guard_opaque = state.path_guard_opaque;
        Some(merged)
    }
}

pub(super) fn switch_branches_for_effects(
    body: &Body<'_>,
    discr: &Operand<'_>,
    targets: &SwitchTargets,
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<Vec<SwitchBranch>> {
    let condition = translate_operand(discr, local_exprs)?;

    if operand_is_bool(discr, body) {
        let mut false_bb = None;
        let mut true_bb = None;
        for (value, target) in targets.iter() {
            if value == 0 {
                false_bb = Some(target);
            } else if value == 1 {
                true_bb = Some(target);
            }
        }

        let otherwise_bb = targets.otherwise();
        let else_bb = false_bb.unwrap_or(otherwise_bb);
        let then_bb = true_bb.unwrap_or(otherwise_bb);
        if then_bb == else_bb {
            return Some(vec![SwitchBranch {
                target: then_bb,
                condition: None,
            }]);
        }

        return Some(vec![
            SwitchBranch {
                target: then_bb,
                condition: Some(condition),
            },
            SwitchBranch {
                target: else_bb,
                condition: None,
            },
        ]);
    }

    let discr_int_ty = operand_int_ty(discr, body)?;
    let mut branches: Vec<SwitchBranch> = Vec::new();
    for (value, target) in targets.iter() {
        let value_i64 = switch_value_to_i64(value, discr_int_ty)?;
        let eq_cond = PureExpr::BinOp(
            Arc::new(condition.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::Int(value_i64)),
        );
        branches.push(SwitchBranch {
            target,
            condition: Some(eq_cond),
        });
    }
    branches.push(SwitchBranch {
        target: targets.otherwise(),
        condition: None,
    });
    Some(branches)
}

fn merge_branch_states(
    branches: Vec<(Option<PureExpr>, BodyExtractionState)>,
    local_to_name: &HashMap<Local, String>,
) -> Option<BodyExtractionState> {
    if branches.is_empty() {
        return None;
    }
    if branches.len() == 1 {
        return Some(branches.into_iter().next()?.1);
    }

    let mut common_locals: HashSet<Local> = branches[0].1.working_exprs.keys().copied().collect();
    for (_, state) in branches.iter().skip(1) {
        common_locals.retain(|local| state.working_exprs.contains_key(local));
    }

    let mut merged_working_exprs: HashMap<Local, PureExpr> = HashMap::new();
    for local in common_locals {
        let values: Vec<PureExpr> = branches
            .iter()
            .map(|(_, state)| state.working_exprs.get(&local).cloned())
            .collect::<Option<Vec<_>>>()?;
        let merged = merge_branch_values(&branches, &values)?;
        merged_working_exprs.insert(local, merged);
    }

    let mut effect_vars: HashSet<String> = HashSet::new();
    for (_, state) in &branches {
        effect_vars.extend(state.effects.keys().cloned());
    }
    let name_to_local: HashMap<String, Local> = local_to_name
        .iter()
        .map(|(local, name)| (name.clone(), *local))
        .collect();

    let mut merged_effects: HashMap<String, PureExpr> = HashMap::new();
    for var_name in effect_vars {
        let local = name_to_local.get(&var_name).copied();
        let mut values: Vec<PureExpr> = Vec::with_capacity(branches.len());
        for (_, state) in &branches {
            let value = state
                .effects
                .get(&var_name)
                .cloned()
                .or_else(|| local.and_then(|local| state.working_exprs.get(&local).cloned()));
            if let Some(value) = value {
                values.push(value);
            } else {
                values.clear();
                break;
            }
        }
        if values.len() != branches.len() {
            continue;
        }
        let merged = merge_branch_values(&branches, &values)?;
        merged_effects.insert(var_name, merged);
    }

    // Merge deref effects across branches (#1295)
    let mut deref_effect_vars: HashSet<String> = HashSet::new();
    for (_, state) in &branches {
        deref_effect_vars.extend(state.deref_effects.keys().cloned());
    }
    let mut merged_deref_effects: HashMap<String, PureExpr> = HashMap::new();
    for var_name in deref_effect_vars {
        // A branch that records a deref effect for `var_name` (e.g. the
        // then-branch of `if cond { v[i] = x }` writes `v@ := v@.set(i, x)`)
        // must be merged with branches that leave `*var_name` UNCHANGED. An
        // absent entry means the branch did not modify `*var_name`, so its
        // value is the identity `(*var_name)@`. Previously this branch bailed
        // out (the effect was dropped), which havoced `var_name` during
        // preservation and discarded the per-iteration frame (length, element
        // frame) the conditional indexed write actually establishes. Defaulting
        // the missing branch to the identity instead yields
        // `Ite(cond, v@.set(i, x), v@)` — length-preserving in BOTH arms — so
        // a `v[i] = x` write under a guard now preserves `v@.len()`. (#1295)
        let identity = PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            var_name.clone(),
            None,
        )))));
        let values: Vec<PureExpr> = branches
            .iter()
            .map(|(_, state)| {
                state
                    .deref_effects
                    .get(&var_name)
                    .cloned()
                    .unwrap_or_else(|| identity.clone())
            })
            .collect();
        if let Some(merged) = merge_branch_values(&branches, &values) {
            merged_deref_effects.insert(var_name, merged);
        }
    }

    // Merge double-deref effects across branches (#1295)
    let mut double_deref_effect_vars: HashSet<String> = HashSet::new();
    for (_, state) in &branches {
        double_deref_effect_vars.extend(state.double_deref_effects.keys().cloned());
    }
    let mut merged_double_deref_effects: HashMap<String, PureExpr> = HashMap::new();
    for var_name in double_deref_effect_vars {
        let mut values: Vec<PureExpr> = Vec::with_capacity(branches.len());
        for (_, state) in &branches {
            if let Some(value) = state.double_deref_effects.get(&var_name).cloned() {
                values.push(value);
            } else {
                values.clear();
                break;
            }
        }
        if values.len() != branches.len() {
            continue;
        }
        if let Some(merged) = merge_branch_values(&branches, &values) {
            merged_double_deref_effects.insert(var_name, merged);
        }
    }

    // All branches descend from the same walk state, so they share the
    // length-only-on-value-failure mode; preserve it across the merge.
    let length_only_mode = branches
        .iter()
        .any(|(_, state)| state.index_mut_length_only_on_value_failure);
    let branch_states: Vec<BodyExtractionState> =
        branches.iter().map(|(_, state)| state.clone()).collect();
    let (call_facts, dropped_premises) = union_branch_premises(&branch_states);
    Some(BodyExtractionState {
        working_exprs: merged_working_exprs,
        effects: merged_effects,
        deref_effects: merged_deref_effects,
        double_deref_effects: merged_double_deref_effects,
        pending_index_mut: merge_pending_index_mut_conservative(&branch_states),
        index_mut_length_only_on_value_failure: length_only_mode,
        // The caller restores the pre-switch path.
        path_guard: Vec::new(),
        path_guard_opaque: false,
        call_facts,
        dropped_premises,
    })
}

/// Every branch's facts and dropped premises, once each.
///
/// A fact is guarded by the path that recorded it, so it stays true on every
/// path of the merged state; a premise dropped on any path is dropped for the
/// iteration.
fn union_branch_premises(
    branches: &[BodyExtractionState],
) -> (Vec<PureExpr>, Vec<super::DroppedPremise>) {
    let mut call_facts: Vec<PureExpr> = Vec::new();
    let mut dropped: Vec<super::DroppedPremise> = Vec::new();
    for branch in branches {
        for fact in &branch.call_facts {
            if !call_facts.contains(fact) {
                call_facts.push(fact.clone());
            }
        }
        for premise in &branch.dropped_premises {
            if !dropped.contains(premise) {
                dropped.push(premise.clone());
            }
        }
    }
    (call_facts, dropped)
}

/// Conservative merge for opaque-condition branches: keep only effects that
/// are structurally identical across ALL branches. Effects present in some
/// branches but not others, or with different expressions, are dropped.
/// This is sound because dropped effects cause the variable to be havoced
/// during preservation, which is the conservative default. (#1295)
fn merge_branch_states_conservative(branches: &[BodyExtractionState]) -> BodyExtractionState {
    let first = &branches[0];

    // Working exprs: keep only locals present in ALL branches with identical values.
    let mut working_exprs: HashMap<Local, PureExpr> = HashMap::new();
    for (&local, expr) in &first.working_exprs {
        if branches[1..]
            .iter()
            .all(|b| b.working_exprs.get(&local) == Some(expr))
        {
            working_exprs.insert(local, expr.clone());
        }
    }

    // Direct effects: keep only vars present in ALL branches with identical values.
    let mut effects: HashMap<String, PureExpr> = HashMap::new();
    for (var, expr) in &first.effects {
        if branches[1..]
            .iter()
            .all(|b| b.effects.get(var) == Some(expr))
        {
            effects.insert(var.clone(), expr.clone());
        }
    }

    // Deref effects: keep only vars present in ALL branches with identical values.
    let mut deref_effects: HashMap<String, PureExpr> = HashMap::new();
    for (var, expr) in &first.deref_effects {
        if branches[1..]
            .iter()
            .all(|b| b.deref_effects.get(var) == Some(expr))
        {
            deref_effects.insert(var.clone(), expr.clone());
        }
    }

    // Double-deref effects: keep only vars present in ALL branches with identical values.
    let mut double_deref_effects: HashMap<String, PureExpr> = HashMap::new();
    for (var, expr) in &first.double_deref_effects {
        if branches[1..]
            .iter()
            .all(|b| b.double_deref_effects.get(var) == Some(expr))
        {
            double_deref_effects.insert(var.clone(), expr.clone());
        }
    }

    let (call_facts, dropped_premises) = union_branch_premises(branches);
    BodyExtractionState {
        working_exprs,
        effects,
        deref_effects,
        double_deref_effects,
        pending_index_mut: merge_pending_index_mut_conservative(branches),
        index_mut_length_only_on_value_failure: branches
            .iter()
            .any(|state| state.index_mut_length_only_on_value_failure),
        // The caller restores the pre-switch path.
        path_guard: Vec::new(),
        path_guard_opaque: false,
        call_facts,
        dropped_premises,
    }
}

fn merge_pending_index_mut_conservative(
    branches: &[BodyExtractionState],
) -> HashMap<Local, super::PendingIndexMutWrite> {
    let Some(first) = branches.first() else {
        return HashMap::new();
    };
    let mut pending = HashMap::new();
    for (local, write) in &first.pending_index_mut {
        if branches[1..]
            .iter()
            .all(|branch| branch.pending_index_mut.get(local) == Some(write))
        {
            pending.insert(*local, write.clone());
        }
    }
    pending
}

fn merge_branch_values(
    branches: &[(Option<PureExpr>, BodyExtractionState)],
    values: &[PureExpr],
) -> Option<PureExpr> {
    let (last, prefix) = values.split_last()?;
    let mut acc = last.clone();
    for (idx, value) in prefix.iter().enumerate().rev() {
        let cond = branches[idx].0.as_ref()?;
        acc = PureExpr::Ite(
            Arc::new(cond.clone()),
            Arc::new(value.clone()),
            Arc::new(acc),
        );
    }
    Some(acc)
}
