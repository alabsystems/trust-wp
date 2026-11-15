// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! What a loop the primary extractor SKIPS may change, and where the paths
//! that leave it rejoin the walked continuation.
//!
//! `skip_loop_or_continue` jumps from a loop header straight to the exit arm of
//! the loop condition. Every OTHER way out of the loop is invisible to that
//! walk: a `break` whose block writes a local and jumps to the post-loop code
//! (`if i == 3 { x = 5; break }`), a `return` inside the body (`_0 = 7; goto
//! return_block`), and a `loop { if c { y = 3; break } if d { break } }` whose
//! resolved "exit" arm itself writes before the join. The walked continuation
//! then describes only the normal exit; a postcondition proved from it alone
//! (`ensures(result@ == 0)` over a body with `x = 5; break`) is a false accept.
//!
//! For each skipped loop with header `h` and resolved exit edge `cond -> exit`:
//!
//! * `post`   = blocks reachable from `exit` without passing through `h`;
//! * `region` = blocks reachable from `h` without entering `post` (the body,
//!   break paths and in-loop return paths up to where they join `post`);
//! * every edge `b -> s` with `b` in `region`, `s` in `post` other than the
//!   resolved exit edge is a MERGE: on entering `s` the walk re-binds every
//!   local the region writes, plus every local written by `post` blocks that
//!   are not reachable from `s` (the exit-side code the joining path skipped),
//!   to fresh variables — the join of the two states over-approximated by
//!   havoc (Creusot's implicit `invariant true` gives the same post-loop
//!   state);
//! * a `Return` terminator inside `region` (a return that never joins `post`)
//!   makes the walk's result unconstrained.
//!
//! Parameters are included when the region writes the parameter's own storage
//! (a whole or field-projected write, a call destination, a `&mut`/raw borrow
//! of the parameter place): the fresh name leaves the entry name, which
//! `requires` constrains, untouched. Writes THROUGH a `&mut` parameter are
//! owned by the mut-borrow lanes and do not re-bind the reference itself.
//!
//! Every choice replaces a value by a less-constrained one: accept paths are
//! only ever removed.

use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{
        BasicBlock, Body, BorrowKind, Local, Operand, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{Mutability, TyKind},
};

use super::super::loops::{LoopAnalysis, LoopInfo};

/// Merge havoc facts for every loop in a body.
#[derive(Debug, Default)]
pub(in crate::mir_analysis) struct SkippedLoopMerges {
    /// Block -> (locals to re-bind on entry, whether a joined path may write
    /// through a pointer).
    pub(in crate::mir_analysis) havoc_at: HashMap<BasicBlock, (Vec<Local>, bool)>,
    /// Some loop region reaches a `Return` without joining its post region.
    pub(in crate::mir_analysis) unmerged_return: bool,
}

/// The resolved exit edge of a loop as used by the primary extractor's skip:
/// `(condition block, exit block)`. `None` when no exit arm leaves the body.
pub(in crate::mir_analysis) fn loop_exit_edge(
    body: &Body<'_>,
    loop_info: &LoopInfo,
) -> Option<(BasicBlock, BasicBlock)> {
    let header = loop_info.header;
    let header_data = &body.basic_blocks[header];
    let mut cond_block = match &header_data.terminator().kind {
        TerminatorKind::SwitchInt { .. } => header,
        TerminatorKind::FalseUnwind { real_target, .. }
        | TerminatorKind::Goto {
            target: real_target,
            ..
        } => *real_target,
        TerminatorKind::Call {
            target: Some(switch_bb),
            ..
        } => *switch_bb,
        _ => header,
    };
    match &body.basic_blocks[cond_block].terminator().kind {
        TerminatorKind::SwitchInt { .. } => {}
        TerminatorKind::Call {
            target: Some(next_bb),
            ..
        }
        | TerminatorKind::Goto {
            target: next_bb, ..
        } => cond_block = *next_bb,
        _ => {}
    }
    switch_exit_edge(body, loop_info, cond_block)
}

/// The exit edge of the `SwitchInt` ending `switch`: the arm the loop
/// verifier's own exit recovery picks (the unique arm that reaches `Return`
/// without re-entering the loop), else an arm outside the body. `None` when
/// `switch` ends in no `SwitchInt` or no arm leaves.
fn switch_exit_edge(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    switch: BasicBlock,
) -> Option<(BasicBlock, BasicBlock)> {
    let TerminatorKind::SwitchInt { targets, .. } = &body.basic_blocks[switch].terminator().kind
    else {
        return None;
    };
    // The recovery first: a `for` loop's `None` arm is a `FalseEdge` whose
    // imaginary target is the body, so loop detection keeps it in
    // `body_blocks` and the only arm "outside" is the `Unreachable`
    // otherwise-arm. Resolving the exit there makes every `for` loop's real
    // exit look like an unmodeled join (100doors) and makes the primary skip
    // continue at `unreachable` instead of the post-loop code.
    if let Some(exit) = super::super::loops::find_post_loop_exit_block(body, switch, loop_info) {
        return Some((switch, exit));
    }
    let outside: Vec<BasicBlock> = targets
        .all_targets()
        .iter()
        .copied()
        .filter(|target| !loop_info.body_blocks.contains(target))
        .collect();
    // Prefer an arm that is not `Unreachable` (a `for` loop's `otherwise`
    // arm), as the loop verifier's exit recovery does.
    outside
        .iter()
        .copied()
        .find(|target| {
            !matches!(
                body.basic_blocks[*target].terminator().kind,
                TerminatorKind::Unreachable
            )
        })
        .or_else(|| outside.first().copied())
        .map(|exit| (switch, exit))
}

/// The exit the loop lane reads, for the checks that refuse what the lane's
/// VC does not state (`loop_has_unmodeled_exit`, `loop_condition_exit_write`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LaneExit {
    /// The edge `(switch, exit block)` the lane's condition is read at.
    Edge(BasicBlock, BasicBlock),
    /// No path leaves the loop to code that can run after it: nothing after
    /// the loop reads its state.
    Never,
    /// A path leaves the loop and no exit edge is the one the lane reads.
    Unresolved,
}

/// The exit edge of `loop_info` that its lane reads, given the switch the
/// lane takes its condition from (`LoopBodyExpr::condition_switch`).
///
/// `loop_exit_edge` starts at the first `SwitchInt` after the header; the
/// lane takes its condition from the real exit switch
/// (`find_body_break_condition`) when that first switch has no exit arm
/// (`{ if n == 3 { i = 0 } n < 3 }`). The checks that refuse what the lane
/// does not state must read the lane's exit, or the code that grants and the
/// code that owes read different exits (D-234). Two resolved edges that name
/// different switches, or a loop some path leaves while neither resolves, is
/// [`LaneExit::Unresolved`]: the caller refuses the loop.
pub(crate) fn loop_lane_exit(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    condition_switch: Option<BasicBlock>,
) -> LaneExit {
    let first = loop_exit_edge(body, loop_info);
    let lane = condition_switch.and_then(|switch| switch_exit_edge(body, loop_info, switch));
    match (first, lane) {
        (Some(first), Some(lane)) if first != lane => LaneExit::Unresolved,
        (Some((switch, exit)), _) | (None, Some((switch, exit))) => LaneExit::Edge(switch, exit),
        (None, None) if loop_leaves(body, loop_info) => LaneExit::Unresolved,
        (None, None) => LaneExit::Never,
    }
}

/// Whether some path leaves `loop_info`'s body to code that can return: an
/// edge from the body to a block outside it that does not only diverge, or a
/// `Return` inside it.
fn loop_leaves(body: &Body<'_>, loop_info: &LoopInfo) -> bool {
    let mut blocks: Vec<BasicBlock> = loop_info.body_blocks.iter().copied().collect();
    blocks.push(loop_info.header);
    blocks.into_iter().any(|bb| {
        matches!(
            body.basic_blocks[bb].terminator().kind,
            TerminatorKind::Return
        ) || normal_successors(body, bb).into_iter().any(|succ| {
            !loop_info.body_blocks.contains(&succ)
                && succ != loop_info.header
                && !super::helpers::block_must_diverge(body, succ, &mut HashSet::new())
        })
    })
}

/// Whether some path leaves the loop other than through the exit edge
/// `cond_block -> exit` — a `break` or in-loop `return` that joins the
/// post-loop code, or a return that never joins it. The loop-invariant path
/// models only that exit (`!cond` and the invariant at the exit, the
/// post-loop return walk from the exit block), so such a loop's continuation
/// cannot be stated soundly there.
pub(crate) fn loop_has_unmodeled_exit(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    (cond_block, exit): (BasicBlock, BasicBlock),
) -> bool {
    let header = loop_info.header;
    let post = reach(body, exit, |bb| bb == header);
    let region = reach(body, header, |bb| post.contains(&bb));
    region.iter().any(|&bb| {
        let terminator = body.basic_blocks[bb].terminator();
        matches!(terminator.kind, TerminatorKind::Return)
            || normal_successors(body, bb)
                .into_iter()
                .any(|succ| post.contains(&succ) && !(bb == cond_block && succ == exit))
    })
}

pub(super) fn reach(
    body: &Body<'_>,
    start: BasicBlock,
    stop: impl Fn(BasicBlock) -> bool,
) -> HashSet<BasicBlock> {
    let mut seen = HashSet::new();
    let mut worklist = vec![start];
    while let Some(bb) = worklist.pop() {
        if stop(bb) || !seen.insert(bb) {
            continue;
        }
        worklist.extend(normal_successors(body, bb));
    }
    seen
}

/// Successors along edges that can execute on a non-unwinding path: the
/// imaginary edges of `FalseEdge` / `FalseUnwind` are never taken, and
/// cleanup blocks only unwind (they cannot reach `Return` or rejoin normal
/// code), so neither is a loop exit that joins the post-loop code. Counting
/// them flags every loop with a panic site or a `while let` / `for` as an
/// unmodeled exit (100doors, lang/while_let).
pub(super) fn normal_successors(body: &Body<'_>, bb: BasicBlock) -> Vec<BasicBlock> {
    let terminator = body.basic_blocks[bb].terminator();
    let real: Vec<BasicBlock> = match &terminator.kind {
        TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } => vec![*real_target],
        _ => terminator.successors().collect(),
    };
    real.into_iter()
        .filter(|succ| !body.basic_blocks[*succ].is_cleanup)
        .collect()
}

pub(in crate::mir_analysis) fn compute_skipped_loop_merges(
    body: &Body<'_>,
    analysis: &LoopAnalysis,
    arg_count: usize,
) -> SkippedLoopMerges {
    let mut merges = SkippedLoopMerges::default();
    for loop_info in &analysis.loops {
        let Some((cond_block, exit)) = loop_exit_edge(body, loop_info) else {
            continue;
        };
        let header = loop_info.header;
        let post = reach(body, exit, |bb| bb == header);
        let region = reach(body, header, |bb| post.contains(&bb));
        if region.iter().any(|&bb| {
            matches!(
                body.basic_blocks[bb].terminator().kind,
                TerminatorKind::Return
            )
        }) {
            merges.unmerged_return = true;
        }
        let (region_writes, region_pointer_write) = region_effects(body, arg_count, &region);
        let mut targets: Vec<BasicBlock> = Vec::new();
        for &bb in &region {
            for succ in normal_successors(body, bb) {
                if post.contains(&succ) && !(bb == cond_block && succ == exit) {
                    targets.push(succ);
                }
            }
        }
        targets.sort();
        targets.dedup();
        for target in targets {
            let from_target = reach(body, target, |bb| bb == header);
            let skipped: HashSet<BasicBlock> = post.difference(&from_target).copied().collect();
            let (skipped_writes, skipped_pointer_write) = region_effects(body, arg_count, &skipped);
            let entry = merges.havoc_at.entry(target).or_default();
            entry.0.extend(region_writes.iter().copied());
            entry.0.extend(skipped_writes);
            entry.0.sort();
            entry.0.dedup();
            entry.1 |= region_pointer_write || skipped_pointer_write;
        }
    }
    merges
}

/// Blocks reachable from the loop header before joining the post region of
/// its resolved exit. `None` when the loop has no resolvable exit edge.
pub(super) fn loop_region(body: &Body<'_>, loop_info: &LoopInfo) -> Option<HashSet<BasicBlock>> {
    let (_, exit) = loop_exit_edge(body, loop_info)?;
    let header = loop_info.header;
    let post = reach(body, exit, |bb| bb == header);
    Some(reach(body, header, |bb| post.contains(&bb)))
}

fn is_param(arg_count: usize, local: Local) -> bool {
    let index = local.as_usize();
    index >= 1 && index <= arg_count
}

fn place_has_deref(place: &rustc_middle::mir::Place<'_>) -> bool {
    place
        .projection
        .iter()
        .any(|p| matches!(p, ProjectionElem::Deref))
}

fn ty_holds_mutable_pointer(ty: rustc_middle::ty::Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        TyKind::Ref(_, _, Mutability::Mut) | TyKind::RawPtr(_, Mutability::Mut)
    )
}

/// Locals whose value the given blocks may change, and whether they may write
/// through a pointer (then every local reachable through a mutable pointer is
/// included, except `&mut`/`*mut` parameters that are never borrowed: writes
/// through those are owned by the mut-borrow lanes).
pub(in crate::mir_analysis) fn region_effects(
    body: &Body<'_>,
    arg_count: usize,
    blocks: &HashSet<BasicBlock>,
) -> (HashSet<Local>, bool) {
    let mut written = HashSet::new();
    let mut pointer_write = false;
    let record_place_write = |written: &mut HashSet<Local>,
                              pointer_write: &mut bool,
                              place: &rustc_middle::mir::Place<'_>| {
        if place_has_deref(place) {
            *pointer_write = true;
            if !is_param(arg_count, place.local) {
                written.insert(place.local);
            }
        } else {
            written.insert(place.local);
        }
    };
    for &bb in blocks {
        let bb_data = &body.basic_blocks[bb];
        for stmt in &bb_data.statements {
            match &stmt.kind {
                StatementKind::Assign((place, rvalue)) => {
                    record_place_write(&mut written, &mut pointer_write, place);
                    if let Rvalue::Ref(_, BorrowKind::Mut { .. }, borrowed)
                    | Rvalue::RawPtr(_, borrowed) = rvalue
                    {
                        record_place_write(&mut written, &mut pointer_write, borrowed);
                        pointer_write = true;
                    }
                }
                StatementKind::SetDiscriminant {
                    place: deref!(place),
                    ..
                } => record_place_write(&mut written, &mut pointer_write, place),
                _ => {}
            }
        }
        if let TerminatorKind::Call {
            args, destination, ..
        } = &bb_data.terminator().kind
        {
            record_place_write(&mut written, &mut pointer_write, destination);
            if args
                .iter()
                .any(|arg| operand_may_carry_mutable_pointer(body, &arg.node))
            {
                pointer_write = true;
            }
        }
    }
    if pointer_write {
        let borrowed = mutably_borrowed_locals(body);
        for (local, decl) in body.local_decls.iter_enumerated() {
            let typed = ty_holds_mutable_pointer(decl.ty);
            if borrowed.contains(&local) || (typed && !is_param(arg_count, local)) {
                written.insert(local);
            }
        }
    }
    (written, pointer_write)
}

fn mutably_borrowed_locals(body: &Body<'_>) -> HashSet<Local> {
    let mut locals = HashSet::new();
    for bb_data in body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            if let StatementKind::Assign((_, rvalue)) = &stmt.kind {
                if let Rvalue::Ref(_, BorrowKind::Mut { .. }, place) | Rvalue::RawPtr(_, place) =
                    rvalue
                {
                    locals.insert(place.local);
                }
            }
        }
    }
    locals
}

fn operand_may_carry_mutable_pointer<'tcx>(body: &Body<'tcx>, operand: &Operand<'tcx>) -> bool {
    super::unannotated_loops::operand_may_carry_mutable_pointer(body, operand)
}

/// The prefix of the symbol a local carried round a loop is bound to at that
/// loop's head ([`loop_head_symbol`], D-187).
pub(crate) const LOOP_HEAD_SYMBOL_PREFIX: &str = "__trust_wp_loop_head_";

/// The symbol `local` is bound to at the head of the loop whose header is
/// `header` (D-187): its value at the start of an ARBITRARY iteration, which
/// only the loop's invariants and its condition constrain. One symbol per
/// (header, local), so the program-point walk and the lane that states the
/// loop's invariants about the loop head name the same value.
pub(crate) fn loop_head_symbol(header: BasicBlock, local: Local) -> String {
    format!(
        "{LOOP_HEAD_SYMBOL_PREFIX}bb{}_{}",
        header.as_usize(),
        local.as_usize()
    )
}

/// Per header of a loop that `cutoff_blocks` lie in, the locals the loop may
/// change (D-187): the walk that stops at a program point inside the loop
/// follows each acyclic path from the entry once, so it reaches that point
/// on the FIRST iteration and would read every local the loop writes (a
/// counter, a local written later in the body) at its first-iteration
/// value. A value carried round the back edge is not that value: at the
/// head of an arbitrary iteration each of these locals is re-bound to its
/// loop-head symbol ([`loop_head_symbol`]). The locals are the loop's
/// [`region_effects`] over its body blocks, the same set the skipped-loop
/// merge havocs.
pub(crate) fn loop_head_rebinds(
    body: &Body<'_>,
    arg_count: usize,
    analysis: &LoopAnalysis,
    cutoff_blocks: &HashSet<BasicBlock>,
) -> HashMap<BasicBlock, Vec<Local>> {
    let mut rebinds: HashMap<BasicBlock, Vec<Local>> = HashMap::new();
    for loop_info in &analysis.loops {
        if loop_info.body_blocks.is_disjoint(cutoff_blocks) {
            continue;
        }
        let mut blocks = loop_info.body_blocks.clone();
        blocks.insert(loop_info.header);
        let (written, _) = region_effects(body, arg_count, &blocks);
        let entry = rebinds.entry(loop_info.header).or_default();
        entry.extend(written);
        entry.sort();
        entry.dedup();
    }
    rebinds
}

/// The arm of the `SwitchInt` ending `switch` that every path from the
/// function entry to `block` takes in the current iteration of `loop_info`,
/// among the arms `arm` accepts — so a fact that arm establishes (the loop
/// condition on the in-body arm, its negation on the exit arm) holds on every
/// path reaching `block`. `None` when there is no such arm.
///
/// The arm's target must have `switch` as its ONLY predecessor (no other path
/// enters it, imaginary and unwind edges included) and must dominate `block`.
/// A `switch` inside a loop nested in `loop_info` is refused: it is decided
/// again on each inner iteration, so the arm a path took last is not the one
/// any single evaluation of the condition describes.
pub(crate) fn switch_arm_dominating(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    all_loops: &[LoopInfo],
    switch: BasicBlock,
    arm: impl Fn(BasicBlock) -> bool,
    block: BasicBlock,
) -> Option<BasicBlock> {
    let TerminatorKind::SwitchInt { targets, .. } = &body.basic_blocks[switch].terminator().kind
    else {
        return None;
    };
    if all_loops.iter().any(|inner| {
        inner.header != loop_info.header
            && loop_info.body_blocks.contains(&inner.header)
            && inner.body_blocks.contains(&switch)
    }) {
        return None;
    }
    let predecessors = body.basic_blocks.predecessors();
    let dominators = body.basic_blocks.dominators();
    if !dominators.is_reachable(block) {
        return None;
    }
    targets.all_targets().iter().copied().find(|&target| {
        target != switch
            && target != loop_info.header
            && arm(target)
            && predecessors[target].iter().all(|pred| *pred == switch)
            && dominators.dominates(target, block)
    })
}

/// The block whose `SwitchInt` decides `loop_info`'s condition as the loop
/// verifier resolves it ([`loop_exit_edge`]); `None` when it has none.
pub(crate) fn loop_condition_block(body: &Body<'_>, loop_info: &LoopInfo) -> Option<BasicBlock> {
    loop_exit_edge(body, loop_info).map(|(cond_block, _)| cond_block)
}

/// The exit arm of `loop_info`'s condition switch ([`switch_arm_dominating`])
/// when it dominates `block`: a switch target outside the loop's body, or
/// the exit the loop verifier resolves ([`loop_exit_edge`]), which for a
/// `for` loop is a `FalseEdge` block loop detection keeps in the body.
pub(crate) fn loop_exit_arm_dominating(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    all_loops: &[LoopInfo],
    block: BasicBlock,
) -> Option<BasicBlock> {
    let (switch, exit) = loop_exit_edge(body, loop_info)?;
    switch_arm_dominating(
        body,
        loop_info,
        all_loops,
        switch,
        |target| target == exit || !loop_info.body_blocks.contains(&target),
        block,
    )
}
