// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Simplified backward liveness analysis for `&mut` locals (#2150).
//!
//! Computes per-block live-in and live-out sets for a tracked set of `&mut`-typed
//! locals. This is a local-level (not move-path-level) analysis, sufficient for
//! determining where `&mut` parameter borrows can be resolved.

use std::collections::{HashMap, HashSet};

use rustc_middle::mir::{
    BasicBlock, Body, Local, Operand, Place, Rvalue, StatementKind, TerminatorKind,
};

/// Per-block liveness results for `&mut` locals.
pub(super) struct LocalLiveness {
    /// Live-in set for each block: locals that are live at block entry.
    pub(super) live_in: HashMap<BasicBlock, HashSet<Local>>,
    /// Live-out set for each block: locals that are live at block exit.
    pub(super) live_out: HashMap<BasicBlock, HashSet<Local>>,
}

/// Compute liveness for the given set of `&mut` locals via backward dataflow.
pub(super) fn compute_mut_local_liveness<'tcx>(
    body: &Body<'tcx>,
    mut_locals: &HashSet<Local>,
) -> LocalLiveness {
    let num_blocks = body.basic_blocks.len();
    let mut live_in: HashMap<BasicBlock, HashSet<Local>> = HashMap::with_capacity(num_blocks);
    let mut live_out: HashMap<BasicBlock, HashSet<Local>> = HashMap::with_capacity(num_blocks);

    for bb in body.basic_blocks.indices() {
        live_in.insert(bb, HashSet::new());
        live_out.insert(bb, HashSet::new());
    }

    // Iterate backward dataflow to fixpoint.
    let mut changed = true;
    while changed {
        changed = false;
        for bb in body.basic_blocks.indices().rev() {
            let bb_data = &body.basic_blocks[bb];

            // live_out = union of live_in of successors
            let mut new_live_out = HashSet::new();
            for succ in bb_data.terminator().successors() {
                new_live_out.extend(live_in[&succ].iter().copied());
            }

            // Walk statements backward to compute live_in from live_out.
            let mut live = new_live_out.clone();

            // Process terminator first (it's at the end of the block).
            apply_terminator_effects(&bb_data.terminator().kind, mut_locals, &mut live);

            // Process statements in reverse order.
            for stmt in bb_data.statements.iter().rev() {
                apply_statement_effects(&stmt.kind, mut_locals, &mut live);
            }

            if live != live_in[&bb] {
                live_in.insert(bb, live);
                changed = true;
            }
            if new_live_out != live_out[&bb] {
                live_out.insert(bb, new_live_out);
                changed = true;
            }
        }
    }

    LocalLiveness { live_in, live_out }
}

/// Apply the liveness effects of a statement (gen/kill on the live set).
fn apply_statement_effects(
    kind: &StatementKind<'_>,
    mut_locals: &HashSet<Local>,
    live: &mut HashSet<Local>,
) {
    match kind {
        StatementKind::Assign(box (dest, rvalue)) => {
            // Kill: assignment to a local kills it (if the dest is a plain local).
            if dest.projection.is_empty() && mut_locals.contains(&dest.local) {
                live.remove(&dest.local);
            } else if is_deref_of_mut_local(dest, mut_locals) {
                // *x = expr uses x (writing through the borrow).
                live.insert(dest.local);
            }
            // Gen: uses of mut locals in the rvalue.
            gen_rvalue_uses(rvalue, mut_locals, live);
        }
        StatementKind::StorageDead(local) => {
            if mut_locals.contains(local) {
                live.remove(local);
            }
        }
        _ => {}
    }
}

/// Apply the liveness effects of a terminator.
fn apply_terminator_effects(
    kind: &TerminatorKind<'_>,
    mut_locals: &HashSet<Local>,
    live: &mut HashSet<Local>,
) {
    match kind {
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => {
            if destination.projection.is_empty() && mut_locals.contains(&destination.local) {
                live.remove(&destination.local);
            }
            gen_operand_uses(func, mut_locals, live);
            for arg in args {
                gen_operand_uses(&arg.node, mut_locals, live);
            }
        }
        TerminatorKind::Return => {}
        TerminatorKind::SwitchInt { discr, .. } => {
            gen_operand_uses(discr, mut_locals, live);
        }
        // Drop does NOT kill liveness. Creusot's MaybeLiveExceptDrop treats
        // Drop as DefUse::None (line 213 of liveness_no_drop.rs). Killing here
        // would cause premature resolution when a local is still live. (#2183)
        TerminatorKind::Drop { .. } => {}
        _ => {}
    }
}

/// Add uses of `&mut` locals in an rvalue to the live set.
fn gen_rvalue_uses(rvalue: &Rvalue<'_>, mut_locals: &HashSet<Local>, live: &mut HashSet<Local>) {
    match rvalue {
        // WithRetag changes provenance only; both modes read the same operand.
        Rvalue::Use(op, _) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(_, op, _) => {
            gen_operand_uses(op, mut_locals, live);
        }
        Rvalue::BinaryOp(_, box (l, r)) => {
            gen_operand_uses(l, mut_locals, live);
            gen_operand_uses(r, mut_locals, live);
        }
        Rvalue::Ref(_, _, place) | Rvalue::Reborrow(_, _, place) => {
            if mut_locals.contains(&place.local) {
                live.insert(place.local);
            }
        }
        Rvalue::Aggregate(_, ops) => {
            for op in ops {
                gen_operand_uses(op, mut_locals, live);
            }
        }
        Rvalue::Repeat(op, _) => {
            gen_operand_uses(op, mut_locals, live);
        }
        _ => {}
    }
}

/// Add uses of `&mut` locals in an operand to the live set.
fn gen_operand_uses(op: &Operand<'_>, mut_locals: &HashSet<Local>, live: &mut HashSet<Local>) {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            if mut_locals.contains(&place.local) {
                live.insert(place.local);
            }
        }
        Operand::Constant(_) | Operand::RuntimeChecks(_) => {}
    }
}

/// Check if a place is a deref through a `&mut` local (e.g., `*v` where `v: &mut T`).
pub(super) fn is_deref_of_mut_local(place: &Place<'_>, mut_locals: &HashSet<Local>) -> bool {
    use rustc_middle::mir::ProjectionElem;
    mut_locals.contains(&place.local)
        && place
            .projection
            .first()
            .is_some_and(|p| matches!(p, ProjectionElem::Deref))
}

/// Call a function for each `&mut` local used in an rvalue.
pub(super) fn for_each_rvalue_local(
    rvalue: &Rvalue<'_>,
    mut_locals: &HashSet<Local>,
    mut f: impl FnMut(Local),
) {
    let mut check_op = |op: &Operand<'_>| match op {
        Operand::Copy(p) | Operand::Move(p) => {
            if mut_locals.contains(&p.local) {
                f(p.local);
            }
        }
        Operand::Constant(_) | Operand::RuntimeChecks(_) => {}
    };

    match rvalue {
        // WithRetag changes provenance only; both modes visit the same local.
        Rvalue::Use(op, _) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(_, op, _) => check_op(op),
        Rvalue::BinaryOp(_, box (l, r)) => {
            check_op(l);
            check_op(r);
        }
        Rvalue::Ref(_, _, place) | Rvalue::Reborrow(_, _, place) => {
            if mut_locals.contains(&place.local) {
                f(place.local);
            }
        }
        Rvalue::Aggregate(_, ops) => {
            for op in ops {
                check_op(op);
            }
        }
        Rvalue::Repeat(op, _) => check_op(op),
        _ => {}
    }
}
