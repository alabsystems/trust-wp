// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Inner (nested) loop handling during body effect extraction.

use std::collections::{HashMap, HashSet};

use rustc_middle::mir::{BasicBlock, ProjectionElem, StatementKind, TerminatorKind};
use trust_wp_core::formula::PureExpr;

use super::{
    super::super::translate::{translate_rvalue, translate_rvalue_typed},
    BodyExtractionCtx, BodyExtractionState,
};

impl<'a, 'tcx> BodyExtractionCtx<'a, 'tcx> {
    /// If `target` is the header of an inner (nested) loop, find the inner loop's
    /// exit block (the successor of the inner header's condition block that is NOT
    /// inside the inner loop body). Mark all inner loop blocks as visited.
    ///
    /// For variables modified inside the inner loop:
    /// - Direct effects (`var = expr`) are havoced (removed from state.effects)
    /// - Deref effects (`*var = expr`) are preserved when the inner loop contains
    ///   a constant dereference assignment (e.g., `*x = 0`), since the inner loop
    ///   establishes this value on every iteration
    /// - IndexMut writes (`v[i] = x`, lowered as `index_mut` Call + `*result = value`,
    ///   or as a direct `(*v)[i] = rvalue` projection) are summarized by their LENGTH
    ///   frame: a `set`-shaped deref effect `v@.set(i, x)` is propagated for the outer
    ///   collection so the outer loop can carry `v@.len() == K` across the inner loop.
    ///   (gap nested-loop-outer-element-and-indexed-write-frame; 100doors)
    ///
    /// Returns `Some(exit_bb)` if `target` is an inner loop header; `None` otherwise.
    /// (#1295)
    pub(super) fn find_inner_loop_exit(
        &self,
        target: BasicBlock,
        state: &mut BodyExtractionState,
        visited: &mut HashSet<BasicBlock>,
    ) -> Option<BasicBlock> {
        let (_, inner_body) = self
            .inner_loops
            .iter()
            .find(|(header, _)| *header == target)?;

        // Mark all inner loop blocks as visited so the walk doesn't re-enter them.
        for &bb in inner_body {
            visited.insert(bb);
        }

        // Scan inner loop for deref assignments (`*var = expr`) and double-deref
        // assignments (`**var = expr` via temporaries). If the inner loop contains
        // a constant deref/double-deref assignment, propagate it as the outer
        // loop's effect — the inner loop establishes this value.
        let mut inner_deref_effects: HashMap<String, PureExpr> = HashMap::new();
        let mut inner_double_deref_effects: HashMap<String, PureExpr> = HashMap::new();
        let mut inner_direct_modified: HashSet<String> = HashSet::new();
        // Track temporaries for double-deref tracing within the inner loop.
        let mut inner_working: HashMap<rustc_middle::mir::Local, PureExpr> =
            state.working_exprs.clone();
        let translate_inner = |rvalue, inner_working: &HashMap<_, _>| {
            self.call_spec_ctx
                .map(|ctx| ctx.tcx)
                .and_then(|tcx| translate_rvalue_typed(tcx, rvalue, inner_working, Some(self.body)))
                .or_else(|| translate_rvalue(rvalue, inner_working, Some(self.body)))
        };
        for &bb in inner_body {
            for stmt in &self.body.basic_blocks[bb].statements {
                if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                    if place.projection.is_empty() {
                        // Direct assignment — update inner working exprs for temp tracing.
                        if let Some(expr) = translate_inner(rvalue, &inner_working) {
                            inner_working.insert(place.local, expr.clone());
                            if let Some(var_name) = self.local_to_name.get(&place.local) {
                                inner_direct_modified.insert(var_name.clone());
                            }
                        }
                    } else if place.projection.len() == 1
                        && matches!(place.projection.first(), Some(ProjectionElem::Deref))
                    {
                        if let Some(var_name) = self.local_to_name.get(&place.local) {
                            // Deref assignment in inner loop: `*var = expr`
                            if let Some(expr) = translate_inner(rvalue, &inner_working) {
                                inner_deref_effects.insert(var_name.clone(), expr);
                            }
                        } else if let Some(PureExpr::Deref(inner)) = inner_working.get(&place.local)
                        {
                            // Double-deref via temporary in inner loop (#1295)
                            if let PureExpr::Var(ref base_name, _) = **inner {
                                if let Some(expr) = translate_inner(rvalue, &inner_working) {
                                    inner_double_deref_effects.insert(base_name.clone(), expr);
                                }
                            }
                        }
                    }
                }
            }
        }

        // Havoc directly-modified variables (their values are not predictable
        // after the inner loop). Keep deref effects from the inner loop.
        for var_name in &inner_direct_modified {
            state.effects.remove(var_name);
        }
        // Nested IndexMut length-frame (gap nested-loop-outer-element-and-indexed-write-frame).
        // The direct-deref scan above does NOT see `v[i] = x` writes, which lower to an
        // `index_mut` Call followed by `*result = value` (or to a direct `(*v)[i] = rvalue`
        // projection). Run an execution-ordered symbolic walk of the inner-loop blocks that
        // reuses the main effect machinery (apply_assignments) on a SCRATCH state, then
        // propagate ONLY length-preserving `set` deref effects for collections the inner
        // loop does NOT also reassign wholesale. The length of `Seq::set` is invariant, so
        // `len(v@_after) == len(v@_before)` is a sound summary of the entire inner loop for
        // ANY number of iterations. Element content is intentionally NOT propagated.
        self.propagate_inner_indexmut_length_frames(
            inner_body,
            &inner_working,
            &inner_direct_modified,
            state,
        );
        // Propagate inner loop deref effects to the outer loop.
        for (var_name, expr) in inner_deref_effects {
            state.deref_effects.insert(var_name, expr);
        }
        // Propagate inner loop double-deref effects to the outer loop.
        for (var_name, expr) in inner_double_deref_effects {
            state.double_deref_effects.insert(var_name, expr);
        }

        // Find the inner loop's condition block and its exit target.
        // The inner header is typically FalseUnwind -> cond_block,
        // and the cond_block's SwitchInt has an exit branch outside
        // the inner loop body.
        let inner_header_data = &self.body.basic_blocks[target];
        let cond_block = match &inner_header_data.terminator().kind {
            TerminatorKind::SwitchInt { .. } => target,
            TerminatorKind::FalseUnwind { real_target, .. } => *real_target,
            // For-loop pattern: header is Call(Iterator::next) -> switch_bb.
            // Follow one hop to find the SwitchInt condition block. (#2698)
            TerminatorKind::Call {
                target: Some(switch_bb),
                ..
            } => *switch_bb,
            TerminatorKind::Goto { target: next_bb } => *next_bb,
            _ => target,
        };
        let cond_data = &self.body.basic_blocks[cond_block];
        // If the condition block is itself another hop (e.g., Call -> Goto
        // -> SwitchInt for complex for-loop patterns), follow one more. (#2698)
        let cond_data = match &cond_data.terminator().kind {
            TerminatorKind::SwitchInt { .. } => cond_data,
            TerminatorKind::Call {
                target: Some(next_bb),
                ..
            } => &self.body.basic_blocks[*next_bb],
            TerminatorKind::Goto { target: next_bb } => &self.body.basic_blocks[*next_bb],
            _ => cond_data,
        };
        match &cond_data.terminator().kind {
            TerminatorKind::SwitchInt { targets, .. } => {
                // The exit target is the one NOT in the inner loop body.
                for exit_bb in targets.all_targets() {
                    if !inner_body.contains(exit_bb) {
                        return Some(*exit_bb);
                    }
                }
                // All targets are inside the inner loop — can't find exit.
                None
            }
            _ => None,
        }
    }
}

impl<'a, 'tcx> BodyExtractionCtx<'a, 'tcx> {
    /// Summarize an inner loop's IndexMut writes (`v[i] = x`) as LENGTH-preserving
    /// `set` deref effects on the outer collection, so the outer loop can carry a
    /// `v@.len() == K` invariant across the inner loop. (gap
    /// nested-loop-outer-element-and-indexed-write-frame; 100doors)
    ///
    /// Strategy: run an execution-ordered symbolic walk of the inner-loop blocks,
    /// reusing `apply_assignments` (which already handles BOTH IndexMut lowerings via
    /// `record_pending_index_mut`/`apply_indexed_place_assignment`/`apply_deref_assignment`)
    /// on a SCRATCH `BodyExtractionState` seeded from the inner working exprs. From the
    /// scratch state, propagate ONLY deref effects whose value is a `set` MethodCall and
    /// whose base name is NOT directly clobbered by the inner loop. Soundness: the sole
    /// consequence consumed downstream (preservation `set_effect_preserves_len_equality`)
    /// is `len(set(s,i,x)) == len(s)`, a Seq theorem.
    fn propagate_inner_indexmut_length_frames(
        &self,
        inner_body: &HashSet<BasicBlock>,
        inner_working: &HashMap<rustc_middle::mir::Local, PureExpr>,
        inner_direct_modified: &HashSet<String>,
        state: &mut BodyExtractionState,
    ) {
        // IndexMut detection requires a spec context (is_index_mut_call returns false
        // without one); the positional/test path has none, so skip cleanly there.
        if self.call_spec_ctx.is_none() {
            return;
        }
        let mut scratch = BodyExtractionState {
            working_exprs: inner_working.clone(),
            effects: HashMap::new(),
            deref_effects: HashMap::new(),
            double_deref_effects: HashMap::new(),
            pending_index_mut: HashMap::new(),
            // Capture the LENGTH frame even when an inner `v[i] = <expr>` write's
            // value is itself un-modeled (e.g. `door_open[i] = !door_open[i]`): the
            // length of `Seq::set` is value-invariant, so an opaque-value `set` is a
            // sound length summary. Element content is suppressed at preservation.
            index_mut_length_only_on_value_failure: true,
        };
        // Execution-ordered, inner-body-bounded walk. Following MIR successors (rather
        // than iterating the HashSet) keeps the `index_mut` Call's PendingIndexMutWrite
        // live until its `*result = value` successor block applies the `set` effect.
        let Some(&entry) = inner_body.iter().min_by_key(|bb| bb.as_u32()) else {
            return;
        };
        let mut walk_visited: HashSet<BasicBlock> = HashSet::new();
        self.walk_inner_blocks_for_effects(entry, inner_body, &mut scratch, &mut walk_visited);
        // Propagate ONLY length-preserving `set` deref effects for collections the inner
        // loop does not reassign wholesale.
        for (var_name, effect) in scratch.deref_effects {
            if inner_direct_modified.contains(&var_name) {
                continue; // wholesale-reassigned -> leave havoced (conservative)
            }
            if !is_set_method_call(&effect) {
                continue; // only the length-invariant `set` shape is a sound frame
            }
            // Strict precision floor: never DOWNGRADE an effect the legacy direct-deref
            // scan already established for this name; only fill a missing entry.
            state.deref_effects.entry(var_name).or_insert(effect);
        }
    }

    /// Execution-ordered symbolic walk of inner-loop blocks, bounded to `inner_body`,
    /// applying the main effect machinery to `scratch`. Successor-following ensures the
    /// `index_mut` Call's pending entry is live when the `*result = value` write applies.
    fn walk_inner_blocks_for_effects(
        &self,
        bb: BasicBlock,
        inner_body: &HashSet<BasicBlock>,
        scratch: &mut BodyExtractionState,
        walk_visited: &mut HashSet<BasicBlock>,
    ) {
        if !inner_body.contains(&bb) || !walk_visited.insert(bb) {
            return;
        }
        self.apply_assignments(bb, scratch);
        match &self.body.basic_blocks[bb].terminator().kind {
            TerminatorKind::Goto { target }
            | TerminatorKind::Assert { target, .. }
            | TerminatorKind::Drop { target, .. }
            | TerminatorKind::Call {
                target: Some(target),
                ..
            } => self.walk_inner_blocks_for_effects(*target, inner_body, scratch, walk_visited),
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => {
                self.walk_inner_blocks_for_effects(*real_target, inner_body, scratch, walk_visited);
            }
            TerminatorKind::SwitchInt { targets, .. } => {
                for t in targets.all_targets() {
                    self.walk_inner_blocks_for_effects(*t, inner_body, scratch, walk_visited);
                }
            }
            _ => {}
        }
    }
}

/// True iff `expr` is a `<receiver>.set(index, value)` MethodCall — the length-invariant
/// indexed-write shape produced by `apply_indexed_write_effect`.
fn is_set_method_call(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::MethodCall { method, args, .. } if method == "set" && args.len() == 2
    )
}
