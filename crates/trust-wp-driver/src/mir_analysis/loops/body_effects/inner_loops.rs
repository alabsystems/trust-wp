// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Inner (nested) loop handling during body effect extraction.

use std::collections::HashSet;

use rustc_middle::{
    mir::{BasicBlock, Local, StatementKind, TerminatorKind},
    ty::TyKind,
};
use trust_wp_core::formula::PureExpr;

use super::{
    super::{
        super::{extract::machine_int_range_fact, translate::ty_to_expr_sort_enriched},
        changed_places::extract_modified_vars,
        LoopInfo, WriteSites,
    },
    BodyExtractionCtx, BodyExtractionState,
};

impl<'a, 'tcx> BodyExtractionCtx<'a, 'tcx> {
    /// If `target` is the header of an inner (nested) loop, find the inner loop's
    /// exit block (the successor of the inner header's condition block that is NOT
    /// inside the inner loop body). Mark all inner loop blocks as visited.
    ///
    /// Everything the inner loop may write is havoced: it may run any number of
    /// times, zero included, so neither a value one of its iterations writes nor
    /// the value before it is the value after it. That covers a call result or
    /// an untranslatable value moved into a variable, and a store through a
    /// reference (loop_inner_call_write_outer_effect_kept,
    /// loop_inner_opaque_write_outer_effect_kept,
    /// loop_inner_deref_write_assumed_executed). What the inner loop does
    /// establish is its invariant at its exit, which this walk does not state:
    /// each such value is a bare value of its type, recorded as a premise the
    /// outer VC leaves out.
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
        self.havoc_inner_loop_writes(target, inner_body, state);

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
            TerminatorKind::Goto {
                target: next_bb, ..
            } => *next_bb,
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
            TerminatorKind::Goto {
                target: next_bb, ..
            } => &self.body.basic_blocks[*next_bb],
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
    /// Forget every value the inner loop headed by `header` may change.
    ///
    /// The locals are the ones any statement, call destination or write
    /// through a reference in the inner blocks may change, and the names are
    /// the ones the loop-level modified-variable scan attributes to those
    /// blocks, which follows reborrows to the variable they alias.
    fn havoc_inner_loop_writes(
        &self,
        header: BasicBlock,
        inner_body: &HashSet<BasicBlock>,
        state: &mut BodyExtractionState,
    ) {
        let mut written: HashSet<Local> = HashSet::new();
        for &bb in inner_body {
            let data = &self.body.basic_blocks[bb];
            for stmt in &data.statements {
                match &stmt.kind {
                    StatementKind::Assign((place, _))
                    | StatementKind::SetDiscriminant {
                        place: deref!(place),
                        ..
                    } => {
                        written.insert(place.local);
                    }
                    _ => {}
                }
            }
            if let TerminatorKind::Call { destination, .. } = &data.terminator().kind {
                written.insert(destination.local);
            }
        }
        written.extend(
            WriteSites::new(self.body)
                .writes_in_blocks(inner_body.iter().copied())
                .into_keys(),
        );
        let inner = LoopInfo {
            header,
            body_blocks: inner_body.clone(),
        };
        let mut names: HashSet<String> =
            extract_modified_vars(self.body, &inner, self.local_to_name)
                .into_iter()
                .collect();
        names.extend(
            written
                .iter()
                .filter_map(|local| self.local_to_name.get(local).cloned()),
        );
        for local in &written {
            state.working_exprs.remove(local);
            state.pending_index_mut.remove(local);
        }
        for name in &names {
            state.effects.remove(name);
            state.deref_effects.remove(name);
            state.double_deref_effects.remove(name);
        }
        let mut named_locals: Vec<(Local, &String)> = self
            .local_to_name
            .iter()
            .filter(|(_, name)| names.contains(*name))
            .map(|(local, name)| (*local, name))
            .collect();
        named_locals.sort();
        for (local, name) in named_locals {
            state.working_exprs.remove(&local);
            state.pending_index_mut.remove(&local);
            // A value of the local's type, and nothing more: what the inner
            // invariant says of it at the exit is the premise left out below.
            if let Some((symbol, range)) = self.inner_loop_exit_symbol(header, local) {
                state.working_exprs.insert(local, symbol.clone());
                state.effects.insert(name.clone(), symbol);
                state.call_facts.extend(range);
            }
            let premise = super::DroppedPremise {
                block: header,
                what: format!(
                    "the value of `{name}` after an inner loop, which its invariant states"
                ),
                iterator_step: false,
                only_about: Some(name.clone()),
            };
            if !state.dropped_premises.contains(&premise) {
                state.dropped_premises.push(premise);
            }
        }
    }

    /// The symbol naming a local's value at an inner loop's exit, with its
    /// machine-integer range, for a local whose type holds no reference.
    fn inner_loop_exit_symbol(
        &self,
        header: BasicBlock,
        local: Local,
    ) -> Option<(PureExpr, Option<PureExpr>)> {
        let spec_ctx = self.call_spec_ctx?;
        let ty = self.body.local_decls[local].ty;
        if ty
            .walk()
            .filter_map(|arg| arg.as_type())
            .any(|t| matches!(t.kind(), TyKind::Ref(..) | TyKind::RawPtr(..)))
        {
            return None;
        }
        let symbol = PureExpr::Var(
            format!(
                "__trust_wp_inner_loop_exit_{}_{}",
                header.as_u32(),
                local.as_u32()
            ),
            ty_to_expr_sort_enriched(spec_ctx.tcx, ty),
        );
        let range = machine_int_range_fact(spec_ctx.tcx, ty, symbol.clone());
        Some((symbol, range))
    }
}
