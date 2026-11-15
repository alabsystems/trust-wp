// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Generic block-walking infrastructure for MIR extraction.
//!
//! Provides the [`BlockVisitor`] trait and [`walk_block`] function that
//! unify the statement dispatch logic shared across the three extraction
//! pipelines (primary, spanned, substitution). Each pipeline implements
//! the trait's callbacks; the walker handles cycle detection, statement
//! iteration, and terminator routing.

use std::collections::HashSet;

use rustc_middle::mir::{
    AssertKind, BasicBlock, Body, Local, Location, Operand, Place, ProjectionElem, Rvalue,
    StatementKind, SwitchTargets, TerminatorKind,
};
use rustc_span::Span;

/// Result of processing a terminator: continue walking, produce a final
/// value, or bail out (unsupported construct).
pub(super) enum VisitorAction<R> {
    /// Continue walking to the specified basic block.
    Continue(BasicBlock),
    /// Produce a final result (e.g., at Return terminator or SwitchInt
    /// that internally handles branching).
    Done(Option<R>),
}

impl<R> VisitorAction<R> {
    /// Convenience for bail-out (unsupported construct).
    pub(super) fn bail() -> Self {
        VisitorAction::Done(None)
    }
}

/// Trait for MIR block-walking pipelines.
///
/// Each extraction pipeline (primary, spanned, substitution) implements
/// this trait. The [`walk_block`] function drives statement iteration and
/// delegates to these callbacks for pipeline-specific behavior.
///
/// The visitor owns the `visited` set for cycle detection. This allows
/// complex terminator handlers (SwitchInt, Call) to take ownership of
/// the visited set when cloning state for branch exploration.
///
/// # Lifetime `'tcx`
/// The MIR lifetime threading Rust compiler types.
pub(super) trait BlockVisitor<'tcx> {
    /// The type produced by this extraction pipeline.
    type Result;

    // ── Cycle detection ──────────────────────────────────────────────

    /// Access the visited set for cycle detection. The walker checks
    /// and inserts blocks via this method.
    fn visited_mut(&mut self) -> &mut HashSet<BasicBlock>;

    /// Record that the walker revisited an already-seen block.
    fn on_cycle(&mut self, _block: BasicBlock) {}

    /// Called once when the walker enters a not-yet-visited block, before its
    /// statements. Default: no-op.
    fn on_block_enter(&mut self, _block: BasicBlock) {}

    // ── Statement callbacks ──────────────────────────────────────────

    /// Handle a whole-local assignment: `_N = <rvalue>` (empty projection).
    fn on_assign_local(
        &mut self,
        local: Local,
        rvalue: &Rvalue<'tcx>,
        body: &Body<'tcx>,
        location: Location,
    );

    /// Handle a non-deref projected write: `_N.field[idx] = <rvalue>`.
    /// Default: no-op (spanned pipeline doesn't track projected writes).
    fn on_assign_projected(
        &mut self,
        _place: &Place<'tcx>,
        _rvalue: &Rvalue<'tcx>,
        _body: &Body<'tcx>,
        _location: Location,
    ) {
    }

    /// Handle a deref projected write: `*_N.field = <rvalue>`.
    /// Default: no-op (only primary and substitution pipelines track these).
    fn on_assign_deref_projected(
        &mut self,
        _place: &Place<'tcx>,
        _rvalue: &Rvalue<'tcx>,
        _body: &Body<'tcx>,
        _location: Location,
    ) {
    }

    /// Handle a `StorageDead(_N)` statement.
    /// Default: no-op (only the substitution pipeline currently needs this).
    fn on_storage_dead(&mut self, _local: Local, _body: &Body<'tcx>, _location: Location) {}

    /// Record that a statement kind is unsupported by this visitor.
    fn on_unsupported_statement(&mut self, _kind: &StatementKind<'tcx>, _location: Location) {}

    // ── Cutoff callbacks ─────────────────────────────────────────────

    /// Check whether the current location has reached the cutoff point.
    /// Return `Some(result)` to stop walking, `None` to continue.
    fn check_cutoff_at_statement(&self, _span: Span, _location: Location) -> Option<Self::Result> {
        None
    }

    /// Check cutoff at the terminator position.
    fn check_cutoff_at_terminator(
        &self,
        _span: Span,
        _block: BasicBlock,
        _statement_count: usize,
    ) -> Option<Self::Result> {
        None
    }

    // ── Terminator callbacks ─────────────────────────────────────────

    /// Handle Return terminator. Produce the pipeline's result from
    /// the accumulated state (typically `local_exprs[_0]`).
    fn on_return(&self, body: &Body<'tcx>) -> Option<Self::Result>;

    /// Handle Goto terminator. Default: continue to target.
    fn on_goto(&mut self, target: BasicBlock) -> VisitorAction<Self::Result> {
        VisitorAction::Continue(target)
    }

    /// Handle Assert terminator. The visitor may extract the assert
    /// fact and produce a result wrapping the continuation, or delegate
    /// to the walker for the target block. `msg` carries the panic kind so
    /// fact extraction can distinguish safety-side-condition asserts that
    /// are PROVED as side obligations (shift overflow, ledger
    /// int-shift-full) from ordinary control asserts that are assumed.
    fn on_assert(
        &mut self,
        cond: &Operand<'tcx>,
        expected: bool,
        msg: &AssertKind<Operand<'tcx>>,
        target: BasicBlock,
        body: &Body<'tcx>,
    ) -> VisitorAction<Self::Result>;

    /// Handle SwitchInt terminator. The visitor must handle branching
    /// internally (cloning state for each branch as needed) and produce
    /// the final result.
    fn on_switch_int(
        &mut self,
        discr: &Operand<'tcx>,
        targets: &SwitchTargets,
        body: &Body<'tcx>,
        bb: BasicBlock,
    ) -> VisitorAction<Self::Result>;

    /// Handle Call terminator. The visitor resolves the call spec and
    /// produces a result (which may involve recursing via `walk_block`
    /// for the continuation block).
    fn on_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
        destination: Place<'tcx>,
        target: Option<BasicBlock>,
        body: &Body<'tcx>,
        bb: BasicBlock,
    ) -> VisitorAction<Self::Result>;

    /// Observe the place a `Drop` terminator drops (before `on_drop`).
    /// Default: nothing.
    fn on_drop_place(&mut self, _place: &Place<'tcx>, _body: &Body<'tcx>) {}

    /// Handle Drop terminator. Default: continue to target.
    fn on_drop(&mut self, target: BasicBlock) -> VisitorAction<Self::Result> {
        VisitorAction::Continue(target)
    }

    /// Handle FalseEdge/FalseUnwind. Default: continue to real_target.
    fn on_false_edge(&mut self, real_target: BasicBlock) -> VisitorAction<Self::Result> {
        VisitorAction::Continue(real_target)
    }

    /// Record that a terminator kind is unsupported by this visitor.
    fn on_unsupported_terminator(&mut self, _kind: &TerminatorKind<'tcx>, _location: Location) {}

    // ── Post-block wrapping ──────────────────────────────────────────

    /// Wrap a successor block's result after crossing a block boundary.
    /// The primary pipeline uses this to inject projected write facts as
    /// LetAssume nodes. Default: pass through unchanged.
    fn wrap_successor_result(&mut self, result: Option<Self::Result>) -> Option<Self::Result> {
        result
    }
}

/// Walk MIR blocks starting from `start_bb`, dispatching to `visitor`
/// callbacks for each statement and terminator.
///
/// The visitor owns the `visited` set (accessed via [`BlockVisitor::visited_mut`])
/// for cycle detection. For simple terminators (Goto, Drop, FalseEdge/FalseUnwind),
/// the walker recurses automatically. Complex terminators (SwitchInt, Call,
/// Return, Assert) are fully handled by the visitor.
pub(super) fn walk_block<'tcx, V: BlockVisitor<'tcx>>(
    body: &Body<'tcx>,
    start_bb: BasicBlock,
    visitor: &mut V,
) -> Option<V::Result> {
    if visitor.visited_mut().contains(&start_bb) {
        visitor.on_cycle(start_bb);
        return None;
    }
    visitor.visited_mut().insert(start_bb);
    visitor.on_block_enter(start_bb);

    let bb_data = &body.basic_blocks[start_bb];

    // ── Process statements ───────────────────────────────────────────
    for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
        let location = Location {
            block: start_bb,
            statement_index: stmt_idx,
        };

        // Check cutoff before processing the statement.
        if let Some(result) = visitor.check_cutoff_at_statement(stmt.source_info.span, location) {
            return Some(result);
        }

        match &stmt.kind {
            StatementKind::Assign((place, rvalue)) => {
                if place.projection.is_empty() {
                    visitor.on_assign_local(place.local, rvalue, body, location);
                } else if !place
                    .projection
                    .iter()
                    .any(|p| matches!(p, ProjectionElem::Deref))
                {
                    visitor.on_assign_projected(place, rvalue, body, location);
                } else {
                    visitor.on_assign_deref_projected(place, rvalue, body, location);
                }
            }
            StatementKind::StorageDead(local) => visitor.on_storage_dead(*local, body, location),
            StatementKind::StorageLive(_)
            | StatementKind::Nop
            | StatementKind::FakeRead(_)
            | StatementKind::PlaceMention(_)
            | StatementKind::AscribeUserType(..) => {}
            _ => {
                visitor.on_unsupported_statement(&stmt.kind, location);
                return None;
            }
        }
    }

    // ── Process terminator ───────────────────────────────────────────
    let terminator = bb_data.terminator();

    // Check cutoff at terminator position.
    if let Some(result) = visitor.check_cutoff_at_terminator(
        terminator.source_info.span,
        start_bb,
        bb_data.statements.len(),
    ) {
        return Some(result);
    }

    let terminator_location = Location {
        block: start_bb,
        statement_index: bb_data.statements.len(),
    };
    let action = match &terminator.kind {
        TerminatorKind::Return => return visitor.on_return(body),
        TerminatorKind::Goto { target, .. } => visitor.on_goto(*target),
        TerminatorKind::Assert {
            cond,
            expected,
            msg,
            target,
            ..
        } => visitor.on_assert(cond, *expected, msg, *target, body),
        TerminatorKind::SwitchInt { discr, targets } => {
            visitor.on_switch_int(discr, targets, body, start_bb)
        }
        TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } => visitor.on_call(func, args, *destination, *target, body, start_bb),
        TerminatorKind::Drop { place, target, .. } => {
            visitor.on_drop_place(place, body);
            visitor.on_drop(*target)
        }
        TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } => visitor.on_false_edge(*real_target),
        // Dead-end terminators: these are CFG leaves with no successors.
        // They are NOT unsupported — they represent divergence or unwinding
        // paths that the extractor correctly treats as dead branches. (#2323)
        TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::Unreachable => {
            return None;
        }
        _ => {
            visitor.on_unsupported_terminator(&terminator.kind, terminator_location);
            return None;
        }
    };

    match action {
        VisitorAction::Continue(next_bb) => {
            let result = walk_block(body, next_bb, visitor);
            visitor.wrap_successor_result(result)
        }
        VisitorAction::Done(result) => result,
    }
}
