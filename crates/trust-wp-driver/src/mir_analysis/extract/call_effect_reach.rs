// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The condition under which a block of the block-slice walker
//! (`collect_call_effects_for_blocks`) runs, for scoping what it records
//! there (D-243).
//!
//! The walker is flat: an effect it records for one block is stated in the
//! function VC for every path. A callee postcondition recorded on the
//! `if flag { below(x) }` arm discharged a goal owed on the path that skips
//! the call, and a goal owed on one arm was owed on every path. [`BlockReach`]
//! gives each block a formula built as `true` at the entry,
//! `reach(P) && edge(P -> B)` along each edge and a disjunction at a join, in
//! one of two directions ([`Bound`]):
//! - a SUFFICIENT formula holds only where the block runs, or where the
//!   execution stops for good on the way in blocks that all still lead to it.
//!   A premise is stated under it. An execution that stops on the way meets
//!   only goals of blocks that reach the premise's block, and those goals
//!   guard the premise (`guard_assumptions_by_reaching_obligations`).
//! - a NECESSARY formula holds wherever the block runs. A goal is owed under
//!   it.
//!
//! What this module cannot describe is `false` for the first and `true` for
//! the second: an edge whose switch reads a value the walk may not see
//! unchanged, or whose condition does not translate exactly; a terminator
//! other than a switch with more than one normal successor; a block on a
//! cycle or one entered from another loop; a formula larger than
//! [`MAX_REACH_NODES`]. A premise is then lost, and a goal is owed on every
//! path, which is strictly stronger.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand, SwitchTargets, TerminatorKind},
    ty::TyCtxt,
};
use trust_wp_core::formula::{BinOp, PureExpr};

use super::{
    super::effects::CallEffects,
    helpers::{
        block_must_diverge, switch_discr_is_path_stable, switch_discr_is_single_call_result,
        switch_discr_is_value_stable,
    },
    loop_body::switch_branch_conditions,
    loop_merges::normal_successors,
    past_loop_names::PastLoopNames,
};

/// A reach formula larger than this many nodes is not built.
const MAX_REACH_NODES: usize = 256;

/// Which side of the true reach condition a formula approximates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Bound {
    /// Holds only where the block runs: the guard of a premise.
    Sufficient,
    /// Holds wherever the block runs: the guard of a goal.
    Necessary,
}

impl Bound {
    /// What a step this module cannot describe contributes.
    fn unknown(self) -> Reach {
        match self {
            Bound::Sufficient => Reach::Never,
            Bound::Necessary => Reach::Always,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub(super) enum Reach {
    /// `false`.
    Never,
    /// `true`.
    Always,
    /// This formula.
    When(PureExpr),
}

impl Reach {
    fn and(self, edge: Reach, bound: Bound) -> Reach {
        match (self, edge) {
            (Reach::Never, _) | (_, Reach::Never) => Reach::Never,
            (Reach::Always, other) | (other, Reach::Always) => other,
            (Reach::When(lhs), Reach::When(rhs)) => {
                Reach::When(PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs))).capped(bound)
            }
        }
    }

    fn or(self, other: Reach, bound: Bound) -> Reach {
        match (self, other) {
            (Reach::Always, _) | (_, Reach::Always) => Reach::Always,
            (Reach::Never, other) | (other, Reach::Never) => other,
            (Reach::When(lhs), Reach::When(rhs)) => {
                if lhs == rhs {
                    return Reach::When(lhs);
                }
                Reach::When(PureExpr::BinOp(Arc::new(lhs), BinOp::Or, Arc::new(rhs))).capped(bound)
            }
        }
    }

    fn capped(self, bound: Bound) -> Reach {
        match &self {
            Reach::When(expr) if node_count(expr, MAX_REACH_NODES) > MAX_REACH_NODES => {
                bound.unknown()
            }
            _ => self,
        }
    }
}

fn node_count(expr: &PureExpr, limit: usize) -> usize {
    let mut count = 0usize;
    expr.any_recursive(|_| {
        count += 1;
        count > limit
    });
    count
}

/// The condition of each normal successor of a `SwitchInt`, when every one is
/// exact: the formula holds exactly where the switch takes that target.
///
/// `switch_branch_conditions` keys its conditions by block, and gives the
/// `otherwise` block only its own conjunction of `!=` even when an explicit
/// value also jumps there; such a switch has no exact condition here.
///
/// `flow_insensitive` is for `exprs` that do not follow control flow (the
/// names after a loop): the discriminant must then also be free of direct
/// reassignments (`switch_discr_is_value_stable`'s strict rule). The path
/// walk's bindings at the switch follow every whole assignment on the way to
/// it, so there the discriminant needs stability only against writes the walk
/// does not see and against a reassigned parameter, whose name is its entry
/// value (`switch_discr_is_path_stable`): a switch on a local one arm then
/// reassigns (`if lim > 100 { lim = 100 }`) reads its value at the switch
/// (D-244).
pub(super) fn exact_branch_conditions<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    switch_bb: BasicBlock,
    discr: &Operand<'tcx>,
    targets: &SwitchTargets,
    exprs: &HashMap<Local, PureExpr>,
    flow_insensitive: bool,
) -> Option<HashMap<BasicBlock, PureExpr>> {
    let stable = if flow_insensitive {
        switch_discr_is_value_stable(tcx, body, discr, true)
    } else {
        switch_discr_is_path_stable(tcx, body, discr)
    } || switch_discr_is_single_call_result(body, discr, switch_bb).is_some();
    if !stable
        || targets
            .iter()
            .any(|(_, target)| target == targets.otherwise())
    {
        return None;
    }
    switch_branch_conditions(discr, targets, exprs, body, None)
}

/// The reach formula of every block, in one [`Bound`], computed on demand.
pub(super) struct BlockReach<'a, 'tcx, F>
where
    F: Fn(BasicBlock) -> Option<&'a HashMap<Local, PureExpr>>,
{
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    past_loop: &'a PastLoopNames<'a, 'tcx>,
    bound: Bound,
    /// The bindings a switch ending each block is translated with.
    exprs_at: F,
    predecessors: HashMap<BasicBlock, Vec<BasicBlock>>,
    memo: HashMap<BasicBlock, Reach>,
    scc_memo: HashMap<BasicBlock, Reach>,
    in_progress: HashSet<BasicBlock>,
    reachable_from: HashMap<BasicBlock, HashSet<BasicBlock>>,
}

impl<'a, 'tcx, F> BlockReach<'a, 'tcx, F>
where
    F: Fn(BasicBlock) -> Option<&'a HashMap<Local, PureExpr>>,
{
    pub(super) fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        past_loop: &'a PastLoopNames<'a, 'tcx>,
        bound: Bound,
        exprs_at: F,
    ) -> Self {
        Self {
            tcx,
            body,
            past_loop,
            bound,
            exprs_at,
            predecessors: normal_predecessors(body),
            memo: HashMap::new(),
            scc_memo: HashMap::new(),
            in_progress: HashSet::new(),
            reachable_from: HashMap::new(),
        }
    }

    /// The reach formula of `bb`.
    pub(super) fn of(&mut self, bb: BasicBlock) -> Reach {
        if let Some(reach) = self.memo.get(&bb) {
            return reach.clone();
        }
        if !self.in_progress.insert(bb) {
            // Only a loop's blocks lie on a cycle, and a loop is entered as one
            // step; a cycle met here is no path this formula can describe.
            return self.bound.unknown();
        }
        let reach = self.compute(bb);
        self.in_progress.remove(&bb);
        self.memo.insert(bb, reach.clone());
        reach
    }

    fn compute(&mut self, bb: BasicBlock) -> Reach {
        if self.body.basic_blocks[bb].is_cleanup || self.past_loop.is_in_loop(bb) {
            // An unwind, or some pass of a loop: not one formula.
            return self.bound.unknown();
        }
        if bb == rustc_middle::mir::START_BLOCK {
            return Reach::Always;
        }
        let preds = self.predecessors.get(&bb).cloned().unwrap_or_default();
        if preds.is_empty() {
            return self.bound.unknown();
        }
        let dominator = if preds.len() > 1 {
            self.body
                .basic_blocks
                .dominators()
                .immediate_dominator(bb)
                .filter(|&dom| !self.past_loop.is_in_loop(dom))
        } else {
            None
        };
        // A join every path from its immediate dominator reaches, through
        // blocks that all still lead to it, runs whenever its dominator does
        // and the execution goes on.
        if let Some(dom) = dominator {
            if self.inevitable(dom, bb) {
                return self.of(dom);
            }
        }
        let mut reach = Reach::Never;
        for pred in preds {
            let contribution = if self.past_loop.is_in_loop(pred) {
                self.loop_exit_reach(pred, bb)
            } else {
                let edge = self.edge(pred, bb);
                if edge == Reach::Never {
                    Reach::Never
                } else {
                    self.of(pred).and(edge, self.bound)
                }
            };
            reach = reach.or(contribution, self.bound);
            if reach == Reach::Always {
                break;
            }
        }
        // Every path to a join passes its dominator: the dominator's
        // necessary formula holds wherever the join runs.
        if self.bound == Bound::Necessary && reach == Reach::Always {
            if let Some(dom) = dominator {
                return self.of(dom);
            }
        }
        reach
    }

    /// Whether every path from `from` that goes on reaches `to`: no block
    /// met on the way ends the execution (a return, a diverging call), and
    /// each one can still reach `to`. A path that cycles forever on the way
    /// meets only goals of blocks that lead to `to`.
    fn inevitable(&mut self, from: BasicBlock, to: BasicBlock) -> bool {
        let leads_to = self.blocks_reaching(to);
        let mut seen: HashSet<BasicBlock> = HashSet::new();
        let mut stack = normal_successors(self.body, from);
        if stack.is_empty() {
            return false;
        }
        while let Some(next) = stack.pop() {
            if next == to || !seen.insert(next) {
                continue;
            }
            if !leads_to.contains(&next) {
                return false;
            }
            let successors = normal_successors(self.body, next);
            if successors.is_empty() {
                return false;
            }
            stack.extend(successors);
        }
        true
    }

    /// The condition of the edge `from -> to` given `from` runs.
    fn edge(&self, from: BasicBlock, to: BasicBlock) -> Reach {
        let successors = normal_successors(self.body, from);
        if successors.iter().all(|&succ| succ == to) {
            return Reach::Always;
        }
        let TerminatorKind::SwitchInt { discr, targets } =
            &self.body.basic_blocks[from].terminator().kind
        else {
            // Every other terminator with more than one normal successor
            // (inline assembly, a yield) leaves which one runs unsaid.
            return self.bound.unknown();
        };
        let Some(exprs) = (self.exprs_at)(from) else {
            return self.bound.unknown();
        };
        let flow_insensitive = self.past_loop.is_past_a_loop(from);
        exact_branch_conditions(
            self.tcx,
            self.body,
            from,
            discr,
            targets,
            exprs,
            flow_insensitive,
        )
        .and_then(|conditions| conditions.get(&to).cloned())
        .map_or(self.bound.unknown(), Reach::When)
    }

    /// The contribution of the exit edge `pred -> exit`, `pred` in a loop:
    /// the loop's reach. The loop leaves no condition telling its exits
    /// apart, so for a sufficient formula every exit of the loop that does
    /// not diverge must be `exit`.
    fn loop_exit_reach(&mut self, pred: BasicBlock, exit: BasicBlock) -> Reach {
        let component = self.component(pred);
        if self.bound == Bound::Sufficient {
            let mut exits: HashSet<BasicBlock> = HashSet::new();
            for &member in &component {
                for succ in normal_successors(self.body, member) {
                    if !component.contains(&succ)
                        && !block_must_diverge(self.body, succ, &mut HashSet::new())
                    {
                        exits.insert(succ);
                    }
                }
            }
            if exits.len() != 1 || !exits.contains(&exit) {
                return Reach::Never;
            }
        }
        let key = component.iter().copied().min().unwrap_or(pred);
        if let Some(reach) = self.scc_memo.get(&key) {
            return reach.clone();
        }
        let mut reach = Reach::Never;
        'entries: for &member in &component {
            for entry in self.predecessors.get(&member).cloned().unwrap_or_default() {
                if component.contains(&entry) {
                    continue;
                }
                if self.past_loop.is_in_loop(entry) {
                    // Entered from another loop (a nested exit): not one step.
                    reach = self.bound.unknown();
                    break 'entries;
                }
                let edge = self.edge(entry, member);
                let contribution = if edge == Reach::Never {
                    Reach::Never
                } else {
                    self.of(entry).and(edge, self.bound)
                };
                reach = reach.or(contribution, self.bound);
            }
        }
        if reach == Reach::Never && self.bound == Bound::Necessary {
            reach = Reach::Always;
        }
        self.scc_memo.insert(key, reach.clone());
        reach
    }

    /// The strongly connected component of loop block `bb`.
    fn component(&mut self, bb: BasicBlock) -> HashSet<BasicBlock> {
        let from_bb = self.reachable(bb);
        let candidates: Vec<BasicBlock> = from_bb
            .iter()
            .copied()
            .filter(|&other| self.past_loop.is_in_loop(other))
            .collect();
        let mut component = HashSet::from([bb]);
        for other in candidates {
            if self.reachable(other).contains(&bb) {
                component.insert(other);
            }
        }
        component
    }

    fn reachable(&mut self, bb: BasicBlock) -> HashSet<BasicBlock> {
        if let Some(seen) = self.reachable_from.get(&bb) {
            return seen.clone();
        }
        let mut seen = HashSet::new();
        let mut stack = normal_successors(self.body, bb);
        while let Some(next) = stack.pop() {
            if seen.insert(next) {
                stack.extend(normal_successors(self.body, next));
            }
        }
        self.reachable_from.insert(bb, seen.clone());
        seen
    }

    /// `to` and every block from which it can be reached.
    fn blocks_reaching(&self, to: BasicBlock) -> HashSet<BasicBlock> {
        let mut seen = HashSet::from([to]);
        let mut stack = vec![to];
        while let Some(next) = stack.pop() {
            for &pred in self.predecessors.get(&next).into_iter().flatten() {
                if seen.insert(pred) {
                    stack.push(pred);
                }
            }
        }
        seen
    }
}

/// Each block's predecessors along the edges an execution that does not
/// unwind can take.
pub(super) fn normal_predecessors(body: &Body<'_>) -> HashMap<BasicBlock, Vec<BasicBlock>> {
    let mut predecessors: HashMap<BasicBlock, Vec<BasicBlock>> = HashMap::new();
    for bb in body.basic_blocks.indices() {
        for succ in normal_successors(body, bb) {
            let preds = predecessors.entry(succ).or_default();
            if !preds.contains(&bb) {
                preds.push(bb);
            }
        }
    }
    predecessors
}

/// Scope the block-slice walker's effects to the path that reaches their
/// block (D-243):
/// - every assumption recorded for block `B` becomes `reach(B) ==> assumption`
///   with the SUFFICIENT formula, and is dropped where that is `false` or its
///   block is not known. Without this a callee postcondition recorded on one
///   arm of a switch was a premise of the goals owed on the arm that skips
///   the call.
/// - every obligation recorded for `B` is owed as `reach(B) ==> obligation`
///   with the NECESSARY formula, as the weakest precondition owes it. A
///   literal `false` (a fail-closed marker or a written `requires(false)`,
///   which the verdict tells apart by the bare literal, D-27) stays
///   unconditional, which is stronger; so does one whose block is not known.
///
/// SOUND: a premise is weakened or dropped, which only removes derivations;
/// an obligation is weakened only by a condition every execution reaching its
/// block satisfies.
#[allow(clippy::too_many_arguments)]
pub(super) fn scope_effects_to_block_reach<'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    past_loop: &'a PastLoopNames<'a, 'tcx>,
    block_exprs: &'a HashMap<BasicBlock, HashMap<Local, PureExpr>>,
    past_exprs: &'a HashMap<Local, PureExpr>,
    effects: &mut CallEffects,
    obligation_blocks: &[BasicBlock],
    assumption_blocks: &mut Vec<BasicBlock>,
) {
    let exprs_at = |bb: BasicBlock| {
        if past_loop.is_past_a_loop(bb) {
            Some(past_exprs)
        } else {
            block_exprs.get(&bb)
        }
    };
    if obligation_blocks.len() == effects.obligations.len() {
        let mut necessary = BlockReach::new(tcx, body, past_loop, Bound::Necessary, exprs_at);
        for (obligation, &block) in effects.obligations.iter_mut().zip(obligation_blocks) {
            if matches!(obligation, PureExpr::Bool(true)) || owes_literal_false(obligation) {
                continue;
            }
            if let Reach::When(condition) = necessary.of(block) {
                let owed = std::mem::replace(obligation, PureExpr::Bool(true));
                *obligation = PureExpr::BinOp(Arc::new(condition), BinOp::Implies, Arc::new(owed));
            }
        }
    }
    if effects.assumptions.is_empty() {
        return;
    }
    if assumption_blocks.len() != effects.assumptions.len() {
        effects.assumptions.clear();
        assumption_blocks.clear();
        return;
    }
    let mut sufficient = BlockReach::new(tcx, body, past_loop, Bound::Sufficient, exprs_at);
    let mut kept_assumptions = Vec::with_capacity(effects.assumptions.len());
    let mut kept_blocks = Vec::with_capacity(assumption_blocks.len());
    for (assumption, block) in effects
        .assumptions
        .drain(..)
        .zip(assumption_blocks.drain(..))
    {
        match sufficient.of(block) {
            Reach::Never => {}
            Reach::Always => {
                kept_assumptions.push(assumption);
                kept_blocks.push(block);
            }
            Reach::When(condition) => {
                let mut guarded = [assumption];
                crate::mir_analysis::effects::guard_assumptions(&mut guarded, Some(&condition));
                let [guarded] = guarded;
                kept_assumptions.push(guarded);
                kept_blocks.push(block);
            }
        }
    }
    effects.assumptions = kept_assumptions;
    *assumption_blocks = kept_blocks;
}

/// Each fact stated where its block runs, under the SUFFICIENT formula, and
/// dropped where that is `false`, with its block.
pub(super) fn facts_where_their_block_runs<'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    past_loop: &'a PastLoopNames<'a, 'tcx>,
    block_exprs: &'a HashMap<BasicBlock, HashMap<Local, PureExpr>>,
    past_exprs: &'a HashMap<Local, PureExpr>,
    facts: Vec<(BasicBlock, PureExpr)>,
) -> Vec<(BasicBlock, PureExpr)> {
    if facts.is_empty() {
        return Vec::new();
    }
    let exprs_at = |bb: BasicBlock| {
        if past_loop.is_past_a_loop(bb) {
            Some(past_exprs)
        } else {
            block_exprs.get(&bb)
        }
    };
    let mut sufficient = BlockReach::new(tcx, body, past_loop, Bound::Sufficient, exprs_at);
    facts
        .into_iter()
        .filter_map(|(block, fact)| match sufficient.of(block) {
            Reach::Never => None,
            Reach::Always => Some((block, fact)),
            Reach::When(condition) => Some((
                block,
                PureExpr::BinOp(Arc::new(condition), BinOp::Implies, Arc::new(fact)),
            )),
        })
        .collect()
}

/// Whether `obligation` is a literal `false`, bare or behind the guards a
/// lane already wrapped it in: the marker D-27 counts.
fn owes_literal_false(obligation: &PureExpr) -> bool {
    match obligation {
        PureExpr::Bool(false) => true,
        PureExpr::BinOp(_, BinOp::Implies, owed) => owes_literal_false(owed),
        _ => false,
    }
}
