// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Which `&mut`-carrying parameters have a call's prophecy credit invalidated
//! because something other than that call can still decide their referent.
//!
//! A call's ensures is instantiated at the call site with the callee's `^p`
//! collapsed onto the caller's `Final(<root param>)`, so `set(&mut *x)` with
//! `#[ensures(^r == 1)]` contributes the premise `x_final == 1`. `^x` is not
//! fixed there: Creusot gives the call a FRESH borrow, writes its final back
//! into `*x`, and fixes `^x` from `*x` when `x`'s OWN borrow resolves. The
//! premise is therefore the reference semantics only while the crediting call
//! is the last thing that decides the referent before that resolution.
//!
//! Two ways it is not, and the rule is one question — *can anything else
//! decide the referent?* — rather than a list of statement shapes:
//!
//! - the body decides it again AFTER the call: a deref store, a
//!   `copy_nonoverlapping`, a rebinding of the parameter slot, or a later CALL
//!   handed a borrow rooted at the parameter (writing the referent is what a
//!   `&mut` argument is for, whether or not the callee's postcondition mentions
//!   it);
//! - the borrow ESCAPES, so this body never resolves it: `^p` is fixed by
//!   whoever holds the borrow next, and their writes through it are free to
//!   contradict the call's premise. Nothing need be written here at all.
//!
//! This walks MIR directly rather than riding the mut-borrow traversal,
//! because the traversal bails on the shapes that most need the answer: it
//! returns nothing for a body with a loop, and a loop is exactly where a write
//! reaches a call's credit through a back edge.
//!
//! Over-approximate on purpose, in the safe direction: borrow provenance is a
//! union over every local an rvalue mentions, and "after" is CFG reachability,
//! not a path condition. An escape is not required to be reachable from the
//! call at all — a borrow that leaves on any path is one this body does not
//! resolve. A parameter named here only loses a premise.

use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{
        visit::{PlaceContext, Visitor},
        BasicBlock, Body, Local, Location, NonDivergingIntrinsic, Operand, Place, ProjectionElem,
        Rvalue, StatementKind, TerminatorKind, RETURN_PLACE,
    },
    ty::{TyCtxt, TyKind},
};

use super::type_analysis::{collect_mut_ref_pin_paths_with_tcx, type_contains_mut_ref_with_tcx};

/// Names of the parameters whose call-site prophecy credit is dead because
/// something other than the crediting call can still decide their referent.
pub(crate) fn params_with_stale_call_final_credit<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
) -> HashSet<String> {
    let roots = borrow_provenance(tcx, body, arg_names.len());
    if roots.is_empty() {
        return HashSet::new();
    }

    // Blocks that follow a call which may have credited each param, blocks
    // that write through it, and params whose borrow leaves the body.
    let mut credited: HashMap<Local, HashSet<BasicBlock>> = HashMap::new();
    let mut written: HashMap<Local, HashSet<BasicBlock>> = HashMap::new();
    let mut escaped: HashSet<Local> = HashSet::new();

    for (bb, block) in body.basic_blocks.iter_enumerated() {
        for stmt in &block.statements {
            let (place, sources) = match &stmt.kind {
                StatementKind::Assign((place, rvalue)) => (place, rvalue_source_locals(rvalue)),
                StatementKind::SetDiscriminant {
                    place: deref!(place),
                    ..
                } => (place, Vec::new()),
                // Writes through a raw pointer whose value can be a tracked
                // borrow. Not a place, so the operand's local is the closest
                // route back to the parameter; recording it can only widen.
                StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(copy)) => {
                    if let Some(local) = operand_local(&copy.dst) {
                        note_local_write(&roots, local, bb, &mut written);
                    }
                    continue;
                }
                _ => continue,
            };
            note_escape(tcx, body, &roots, place, &sources, &mut escaped);
            note_write(tcx, body, &roots, place, bb, &mut written);
        }
        let Some(terminator) = &block.terminator else {
            continue;
        };
        if let TerminatorKind::Call {
            args, destination, ..
        } = &terminator.kind
        {
            let arg_locals: Vec<Local> =
                args.iter().filter_map(|a| operand_local(&a.node)).collect();
            // A callee can hand a borrow it was given straight back out of the
            // body, so the destination is an escape route like any other.
            note_escape(tcx, body, &roots, destination, &arg_locals, &mut escaped);
            // Both happen AT this call, so neither is "after" it: the call's
            // own block is not among its successors.
            note_write(tcx, body, &roots, destination, bb, &mut written);
            for local in arg_locals {
                let Some(params) = roots.get(&local) else {
                    continue;
                };
                // A callee handed a borrow rooted at the parameter writes the
                // referent — that is what the borrow is for — whether or not
                // its ensures happens to mention `^p`, and whether the callee
                // is a named function or a closure the body just built. So the
                // call both takes a credit and, for every EARLIER call, is the
                // thing that decides the referent after it.
                note_local_write(&roots, local, bb, &mut written);
                for &param in params {
                    credited
                        .entry(param)
                        .or_default()
                        .extend(terminator.successors());
                }
            }
        }
    }

    let mut stale = HashSet::new();
    for (param, starts) in credited {
        if !escaped.contains(&param) {
            let Some(writes) = written.get(&param) else {
                continue;
            };
            let reachable = blocks_reachable_from(body, &starts);
            if !writes.iter().any(|bb| reachable.contains(bb)) {
                continue;
            }
        }
        if let Some(name) = param
            .as_usize()
            .checked_sub(1)
            .and_then(|idx| arg_names.get(idx))
        {
            stale.insert(name.clone());
        }
    }
    stale
}

/// Record a borrow rooted at a tracked parameter that LEAVES this body.
///
/// A value stored into the return place, or through a pointer into memory the
/// body does not own, outlives the body; the parameter's borrow is then
/// resolved by whoever holds it next, so `^p` is theirs to decide and no call
/// here can promise it. The destination's type is what says a BORROW left
/// rather than a value read through one — `*q = *x` stores a scalar and
/// carries nothing — and it is read with the enum-aware deep collector so a
/// borrow nested past the provenance walk's own depth still counts.
fn note_escape<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    roots: &HashMap<Local, HashSet<Local>>,
    dest: &Place<'tcx>,
    sources: &[Local],
    escaped: &mut HashSet<Local>,
) {
    let leaves_body = dest.local == RETURN_PLACE
        || dest
            .projection
            .iter()
            .any(|proj| matches!(proj, ProjectionElem::Deref));
    if !leaves_body || !place_can_carry_mut_ref(tcx, body, dest) {
        return;
    }
    for src in sources {
        if let Some(params) = roots.get(src) {
            escaped.extend(params.iter().copied());
        }
    }
}

/// Record a write that reaches a tracked parameter's referent.
///
/// A projection through a `Deref` writes the referent. A write to the
/// parameter slot itself rebinds what the entry borrow's prophecy resolves
/// against — but only where the written place can hold a borrow: a scalar
/// field of a by-value carrier decides no referent.
fn note_write<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    roots: &HashMap<Local, HashSet<Local>>,
    place: &Place<'tcx>,
    bb: BasicBlock,
    written: &mut HashMap<Local, HashSet<BasicBlock>>,
) {
    let through_deref = place
        .projection
        .iter()
        .any(|proj| matches!(proj, ProjectionElem::Deref));
    let Some(params) = roots.get(&place.local) else {
        return;
    };
    if !through_deref
        && !(params.contains(&place.local) && place_can_carry_mut_ref(tcx, body, place))
    {
        return;
    }
    note_local_write(roots, place.local, bb, written);
}

/// Record a write reaching every parameter `local` can be rooted at.
fn note_local_write(
    roots: &HashMap<Local, HashSet<Local>>,
    local: Local,
    bb: BasicBlock,
    written: &mut HashMap<Local, HashSet<BasicBlock>>,
) {
    let Some(params) = roots.get(&local) else {
        return;
    };
    for &param in params {
        written.entry(param).or_default().insert(bb);
    }
}

/// Whether a value stored at this place can BE a borrow rather than a value
/// read out of one. Deeper than the provenance walk's own carrier test on
/// purpose: both answers here only ever add a disqualification.
fn place_can_carry_mut_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: &Place<'tcx>,
) -> bool {
    let ty = place.ty(&body.local_decls, tcx).ty;
    !collect_mut_ref_pin_paths_with_tcx(tcx, ty).is_empty()
}

/// Map every local that can carry a borrow rooted at a parameter that carries
/// a `&mut` to the set of parameters it can be rooted at.
///
/// Seeded from `type_contains_mut_ref`, the same view `mut_ref_param_names`
/// takes, because a `&mut` one field deep is a prophecy the call site pins
/// exactly like a bare `&mut` parameter.
///
/// Propagation is a union over the locals an rvalue mentions, restricted to
/// destinations whose type can still carry a mutable reference — a scalar read
/// out of `*x` is a value, not a route back to `x`.
fn borrow_provenance<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_count: usize,
) -> HashMap<Local, HashSet<Local>> {
    let mut roots: HashMap<Local, HashSet<Local>> = HashMap::new();
    for idx in 0..arg_count {
        let local = Local::from_usize(idx + 1);
        if local.as_usize() >= body.local_decls.len() {
            break;
        }
        if type_contains_mut_ref_with_tcx(tcx, body.local_decls[local].ty) {
            roots.entry(local).or_default().insert(local);
        }
    }
    if roots.is_empty() {
        return roots;
    }

    // Fixed point: a back edge can carry a borrow to a local the forward pass
    // has already visited.
    let mut changed = true;
    while changed {
        changed = false;
        for block in body.basic_blocks.iter() {
            for stmt in &block.statements {
                let StatementKind::Assign((place, rvalue)) = &stmt.kind else {
                    continue;
                };
                let sources = rvalue_source_locals(rvalue);
                changed |= propagate(tcx, body, &mut roots, place.local, &sources);
            }
            let Some(terminator) = &block.terminator else {
                continue;
            };
            if let TerminatorKind::Call {
                args, destination, ..
            } = &terminator.kind
            {
                // A call can hand back a borrow derived from any argument.
                let sources: Vec<Local> =
                    args.iter().filter_map(|a| operand_local(&a.node)).collect();
                changed |= propagate(tcx, body, &mut roots, destination.local, &sources);
            }
        }
    }
    roots
}

/// Union the source locals' roots into `dest`'s. Returns whether anything grew.
fn propagate<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    roots: &mut HashMap<Local, HashSet<Local>>,
    dest: Local,
    sources: &[Local],
) -> bool {
    if sources.is_empty() {
        return false;
    }
    if !can_carry_mut_ref(tcx, body.local_decls[dest].ty) {
        return false;
    }
    let incoming: HashSet<Local> = sources
        .iter()
        .filter_map(|src| roots.get(src))
        .flatten()
        .copied()
        .collect();
    if incoming.is_empty() {
        return false;
    }
    let entry = roots.entry(dest).or_default();
    let before = entry.len();
    entry.extend(incoming);
    entry.len() != before
}

/// Whether a value of this type can still be a route to a `&mut` referent.
///
/// A scalar read out of `*x` is a value, not a route back to `x`, and pruning
/// those keeps the provenance union from tainting the whole body. A CLOSURE is
/// a route even though the shared collector does not walk upvars: its captured
/// `&mut` writes the referent when the closure runs, which is exactly how the
/// write in `let c = || *x = 3; c();` hides from a walk of this body.
fn can_carry_mut_ref<'tcx>(tcx: TyCtxt<'tcx>, ty: rustc_middle::ty::Ty<'tcx>) -> bool {
    let peeled = match ty.kind() {
        TyKind::Ref(_, inner, _) => *inner,
        _ => ty,
    };
    if matches!(
        peeled.kind(),
        TyKind::Closure(..) | TyKind::CoroutineClosure(..) | TyKind::Coroutine(..)
    ) {
        return true;
    }
    type_contains_mut_ref_with_tcx(tcx, ty)
}

/// Every local an rvalue reads, place bases included.
///
/// A MIR visitor rather than a match on `Rvalue`: this set must stay complete
/// as the compiler's rvalue list changes, and a variant silently missed here
/// would be a route a borrow travels without provenance.
fn rvalue_source_locals<'tcx>(rvalue: &Rvalue<'tcx>) -> Vec<Local> {
    struct Locals(Vec<Local>);
    impl<'tcx> Visitor<'tcx> for Locals {
        fn visit_local(&mut self, local: Local, _: PlaceContext, _: Location) {
            self.0.push(local);
        }
    }
    let mut locals = Locals(Vec::new());
    locals.visit_rvalue(rvalue, Location::START);
    locals.0
}

fn operand_local(op: &Operand<'_>) -> Option<Local> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => Some(place.local),
        Operand::Constant(_) | Operand::RuntimeChecks(_) => None,
    }
}

/// Blocks reachable from `starts`, the starts themselves included.
fn blocks_reachable_from(body: &Body<'_>, starts: &HashSet<BasicBlock>) -> HashSet<BasicBlock> {
    let mut seen: HashSet<BasicBlock> = starts.clone();
    let mut queue: Vec<BasicBlock> = starts.iter().copied().collect();
    while let Some(bb) = queue.pop() {
        let Some(terminator) = &body.basic_blocks[bb].terminator else {
            continue;
        };
        for succ in terminator.successors() {
            if seen.insert(succ) {
                queue.push(succ);
            }
        }
    }
    seen
}
