// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-borrow prophecy carriers + expiry resolution for locally-rooted
//! borrows (#124 — the root-cause repair behind the `^<constant>` false
//! accept closed by the Fix A constant-carrier refusal).
//!
//! ## The defect being repaired
//!
//! The extraction pipelines translate locally-rooted borrows TRANSPARENTLY:
//! for `let mut x = 1; let r = &mut x; let r1 = &mut *r;` every one of
//! `x`/`r`/`r1` tracks the same value expression `Int(1)`. When a mutating
//! call consumes `r1`, the old advancement wrapped each tracked value as
//! `Final(<its own value expression>)`:
//!
//! * `Final(Int(1))` is a prophecy over a CONSTANT — no carrier, no prophecy
//!   slot. The encoder used to fold it to the literal (the live false accept
//!   `evil() == 3`); it now refuses fail-closed, so these shapes became
//!   honest-but-fabricated vacuity demotions / encoding errors.
//! * Every base wrapped ITS OWN value, so the prophecies of DISTINCT borrows
//!   (`^r`, `^r1`) collapsed onto one shape — `bug/final_borrows::
//!   not_final_borrow_works` needs `^r1 == 7` and `^r == 2` simultaneously.
//!
//! ## The repair (RustHorn discipline, mirroring the `&mut`-parameter lane)
//!
//! Mint a per-BORROW prophecy carrier keyed on the borrow LOCAL:
//! a `MutRef`-sorted variable named after the borrow (`Var("r1",
//! MutRef(Int))`). Then:
//!
//! * the call argument translates to the carrier, so the callee's contract
//!   instantiates `^r1`/`*r1` against a REAL prophecy variable;
//! * `*carrier == <pointee value at the call>` is assumed (the callee-entry
//!   binding), guarded fail-closed against stale tracking;
//! * each base local in the borrow chain advances to `Final(<carrier of the
//!   local that borrows it>)` — `r ↦ ^r1`, `x ↦ ^r` — de-conflating the
//!   prophecies;
//! * for each NON-consumed borrow in the chain (the ancestors, e.g. `r`),
//!   the expiry-resolution fact `^r == <pointee value at r's death>` is
//!   emitted when the extraction walk completes. The consumed borrow itself
//!   gets NO caller-side expiry fact: it was moved into the callee, whose
//!   contract is the sole authority on its prophecy (RustHorn).
//!
//! ## Fail-closed discipline
//!
//! Emitting an expiry fact EARLY (while the borrow is live and writes through
//! it are still possible / untracked) would assert a false premise — the
//! false-accept shape. Every route that could invalidate the tracked death
//! value therefore DISARMS the pending fact instead (weaker premises, never
//! wrong ones):
//!
//! * branch exploration (`SwitchInt`) — armed facts are branch-unconditional,
//!   so arming stops permanently for the walk (`poison`);
//! * a deref write through a local whose chain membership is unknown, or any
//!   deeper-projected deref write — the death value can no longer be tracked;
//! * a move of an armed borrow local — the borrow escapes our tracking;
//! * an unsupported statement/terminator — the walk's model is incomplete.
//!
//! Carrier minting itself is scoped to the narrow defect shape: the consumed
//! borrow is a UNIQUELY-ASSIGNED whole-local `&mut` whose tracked value is a
//! GROUND CONSTANT tree, with a fully-known unique-assignment chain down to a
//! non-reference root local. Everything else keeps the legacy behavior
//! (which, post-tract19, is fail-closed at the encoder).

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_middle::{
    mir::{
        AggregateKind, Body, Local, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
    },
    ty::TyCtxt,
};
use tracing::debug;
use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_logic_fn_arity, BinOp, ExprSort, PureExpr,
};

use super::helpers::source_name_for_local;
use crate::mir_analysis::translate::ty_to_expr_sort_enriched;

/// Is this expression a ground-constant tree (literals and arithmetic over
/// literals only — no variable identity anywhere)? This is the exact shape of
/// the closed `^<constant>` false accept: a borrowed place whose tracked value
/// carries no carrier a prophecy could attach to.
pub(in crate::mir_analysis) fn expr_is_ground_constant_tree(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_) => true,
        PureExpr::UnOp(_, inner) => expr_is_ground_constant_tree(inner),
        PureExpr::BinOp(lhs, _, rhs) => {
            expr_is_ground_constant_tree(lhs) && expr_is_ground_constant_tree(rhs)
        }
        _ => false,
    }
}

/// The deterministic per-borrow carrier: a `MutRef`-sorted variable keyed on
/// the borrow LOCAL (source name when available, synthetic otherwise).
/// Returns `None` when the local is not `&mut`-typed (no prophecy exists).
pub(in crate::mir_analysis::extract) fn per_borrow_carrier_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    borrow_local: Local,
) -> Option<PureExpr> {
    let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[borrow_local].ty)?;
    if !matches!(sort, ExprSort::MutRef(_)) {
        return None;
    }
    let name = source_name_for_local(body, borrow_local, arg_names)
        .unwrap_or_else(|| format!("$borrow_{}", borrow_local.as_u32()));
    Some(PureExpr::Var(name, Some(sort)))
}

/// Per-extraction-pass carrier/expiry state for the PRIMARY pipeline.
///
/// Lives in a thread-local stack: the primary walk re-creates its visitor per
/// call segment (`extract_from_block_with_context` recursion), so per-walk
/// state cannot ride the visitor. The stack supports nested extraction
/// entries; each `begin_extraction_pass` pushes, each `end_extraction_pass`
/// pops.
pub(in crate::mir_analysis) struct BorrowCarrierRegistry {
    /// borrower local -> immediate base local. Only edges whose borrower is a
    /// uniquely-assigned whole-local `&mut` borrow (`&mut x` direct, or
    /// `&mut *p` pure reborrow) are recorded, so an edge is valid under any
    /// control flow.
    chain: HashMap<Local, Local>,
    /// Locals with any deref-projected WRITE anywhere in the body (used to
    /// guard the callee-entry `*carrier == value` binding against staleness:
    /// deref writes do not update `local_exprs`, so a written-through borrow's
    /// tracked value cannot be trusted as its call-entry pointee).
    deref_written: HashSet<Local>,
    /// Closure-environment aggregates: closure local -> per-field capture
    /// operand locals (`None` for operands that are not whole locals). Only
    /// UNIQUELY-ASSIGNED closure locals are recorded, so a field list is
    /// valid under any control flow. (#closure-capture-carriers)
    closure_env: HashMap<Local, Vec<Option<Local>>>,
    /// Whole-local move/copy edges (`_5 = move _2`), unique-assignment-gated
    /// on the TARGET. Used to resolve a consumed call argument back to the
    /// closure aggregate it copies (`calls_closure(move _5)` where
    /// `_5 = move _2` and `_2` is the aggregate). (#closure-capture-carriers)
    copy_of: HashMap<Local, Local>,
    /// Active carrier per borrow local (last minted wins).
    carriers: HashMap<Local, PureExpr>,
    /// Armed expiry: borrow local -> tracked death-value expression.
    armed: HashMap<Local, PureExpr>,
    /// Number of carriers minted (for unique re-mint naming).
    mint_seq: usize,
    /// Sticky: no further ARMING (existing arms cleared) once the walk has
    /// seen a route that could make an armed fact early/stale.
    poisoned: bool,
}

thread_local! {
    static REGISTRY_STACK: RefCell<Vec<BorrowCarrierRegistry>> = const { RefCell::new(Vec::new()) };
}

impl BorrowCarrierRegistry {
    /// Scan the body once: unique-assignment borrow-chain edges + the
    /// deref-written local set.
    fn from_body<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Self {
        let mut assign_counts: HashMap<Local, usize> = HashMap::new();
        let mut candidate_edges: Vec<(Local, Local, bool)> = Vec::new(); // (borrower, base, is_direct)
        let mut closure_env_candidates: Vec<(Local, Vec<Option<Local>>)> = Vec::new();
        let mut copy_candidates: Vec<(Local, Local)> = Vec::new(); // (target, source)
        let mut deref_written: HashSet<Local> = HashSet::new();

        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                if let StatementKind::Assign((place, rvalue)) = &statement.kind {
                    if place.projection.is_empty() {
                        *assign_counts.entry(place.local).or_insert(0) += 1;
                        if let Rvalue::Use(Operand::Move(src) | Operand::Copy(src), _) = rvalue {
                            if src.projection.is_empty() {
                                copy_candidates.push((place.local, src.local));
                            }
                        }
                        if let Rvalue::Aggregate(AggregateKind::Closure(..), operands) = rvalue {
                            closure_env_candidates.push((
                                place.local,
                                operands
                                    .iter()
                                    .map(|op| match op {
                                        Operand::Move(p) | Operand::Copy(p)
                                            if p.projection.is_empty() =>
                                        {
                                            Some(p.local)
                                        }
                                        _ => None,
                                    })
                                    .collect(),
                            ));
                        }
                        if let Rvalue::Ref(_, kind, ref_place) = rvalue {
                            if matches!(kind, rustc_middle::mir::BorrowKind::Mut { .. }) {
                                let projections: &[_] = ref_place.projection.as_ref();
                                match projections {
                                    [] => {
                                        candidate_edges.push((place.local, ref_place.local, true))
                                    }
                                    [ProjectionElem::Deref] => {
                                        candidate_edges.push((place.local, ref_place.local, false))
                                    }
                                    _ => {}
                                }
                            }
                        }
                    } else if place
                        .projection
                        .iter()
                        .any(|proj| matches!(proj, ProjectionElem::Deref))
                    {
                        deref_written.insert(place.local);
                    }
                }
            }
            if let Some(terminator) = &block.terminator {
                if let TerminatorKind::Call { destination, .. } = &terminator.kind {
                    if destination.projection.is_empty() {
                        *assign_counts.entry(destination.local).or_insert(0) += 1;
                    }
                }
            }
        }

        let is_mut_ref = |local: Local| {
            matches!(
                body.local_decls[local].ty.kind(),
                rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
            )
        };

        let mut chain = HashMap::new();
        for (borrower, base, is_direct) in candidate_edges {
            if assign_counts.get(&borrower).copied() != Some(1) {
                continue; // reassigned borrows are ambiguous under branching
            }
            if !is_mut_ref(borrower) {
                continue;
            }
            // Fail-closed: a DIRECT borrow of a reference-typed local is a
            // nested `&mut &mut` pointer-slot borrow — excluded.
            if is_direct && is_mut_ref(base) {
                continue;
            }
            // A pure-deref reborrow must go through a reference local.
            if !is_direct && !is_mut_ref(base) {
                continue;
            }
            chain.insert(borrower, base);
        }
        let mut closure_env = HashMap::new();
        for (closure_local, fields) in closure_env_candidates {
            // A reassigned closure local is ambiguous under branching — the
            // recorded field list could describe the wrong construction.
            if assign_counts.get(&closure_local).copied() == Some(1) {
                closure_env.insert(closure_local, fields);
            }
        }
        let mut copy_of = HashMap::new();
        for (target, source) in copy_candidates {
            // A reassigned copy target is ambiguous under branching.
            if assign_counts.get(&target).copied() == Some(1) {
                copy_of.insert(target, source);
            }
        }
        let _ = tcx;

        BorrowCarrierRegistry {
            chain,
            closure_env,
            copy_of,
            deref_written,
            carriers: HashMap::new(),
            armed: HashMap::new(),
            mint_seq: 0,
            poisoned: false,
        }
    }

    /// Resolve `local` to the closure-aggregate local it (transitively)
    /// copies, returning the chain from `local` down to the aggregate
    /// (inclusive) when a recorded closure environment is found.
    /// (#closure-capture-carriers)
    fn resolve_closure_aggregate_chain(&self, local: Local) -> Option<Vec<Local>> {
        let mut chain = vec![local];
        let mut seen = HashSet::new();
        let mut current = local;
        loop {
            if self.closure_env.contains_key(&current) {
                return Some(chain);
            }
            if !seen.insert(current) {
                return None; // cycle — fail closed
            }
            match self.copy_of.get(&current) {
                Some(&source) => {
                    chain.push(source);
                    current = source;
                }
                None => return None,
            }
        }
    }

    /// Walk the chain from `local` to its root. Returns the full chain
    /// (excluding the root) and the root local, or `None` when the chain is
    /// incomplete (a reference-typed base with no recorded edge) or cyclic.
    fn full_chain(&self, body: &Body<'_>, local: Local) -> Option<(Vec<Local>, Local)> {
        let is_mut_ref = |l: Local| {
            matches!(
                body.local_decls[l].ty.kind(),
                rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
            )
        };
        let mut seen = HashSet::new();
        let mut links = Vec::new();
        let mut current = local;
        loop {
            if !seen.insert(current) {
                return None; // cycle — fail closed
            }
            links.push(current);
            match self.chain.get(&current) {
                Some(&base) => {
                    if is_mut_ref(base) {
                        current = base;
                    } else {
                        return Some((links, base));
                    }
                }
                None => return None, // reference base with no edge — incomplete
            }
        }
    }

    /// Does any deref-written local reach `target` through the chain (i.e.
    /// is there a body-level deref write through `target` itself or through
    /// any borrow derived from it)?
    fn deref_write_reaches(&self, target: Local) -> bool {
        self.deref_written.iter().any(|&w| {
            if w == target {
                return true;
            }
            let mut seen = HashSet::new();
            let mut current = w;
            while let Some(&base) = self.chain.get(&current) {
                if !seen.insert(current) {
                    return false;
                }
                if base == target {
                    return true;
                }
                current = base;
            }
            false
        })
    }
}

/// Push a fresh registry for one primary-extraction pass.
pub(in crate::mir_analysis) fn begin_extraction_pass<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) {
    let registry = BorrowCarrierRegistry::from_body(tcx, body);
    REGISTRY_STACK.with(|stack| stack.borrow_mut().push(registry));
}

/// Pop the pass registry, returning the expiry-resolution facts
/// `^carrier == <death value>` for every borrow still armed. The caller must
/// only assert these when the walk genuinely ran to completion (no cutoff).
pub(in crate::mir_analysis) fn end_extraction_pass() -> Vec<PureExpr> {
    REGISTRY_STACK.with(|stack| {
        let Some(registry) = stack.borrow_mut().pop() else {
            return Vec::new();
        };
        if registry.poisoned {
            return Vec::new();
        }
        let mut facts: Vec<(Local, PureExpr)> = Vec::new();
        for (&local, tracker) in &registry.armed {
            let Some(carrier) = registry.carriers.get(&local) else {
                continue;
            };
            let fact = PureExpr::BinOp(
                Arc::new(PureExpr::Final(Arc::new(carrier.clone()))),
                BinOp::Eq,
                Arc::new(tracker.clone()),
            );
            debug!(
                "borrow_carriers: expiry resolution for borrow local {:?}: {:?}",
                local, fact
            );
            facts.push((local, fact));
        }
        // Deterministic order (HashMap iteration is not).
        facts.sort_by_key(|(local, _)| *local);
        facts.into_iter().map(|(_, fact)| fact).collect()
    })
}

fn with_active<R>(f: impl FnOnce(&mut BorrowCarrierRegistry) -> R) -> Option<R> {
    REGISTRY_STACK.with(|stack| stack.borrow_mut().last_mut().map(f))
}

/// SwitchInt seen: armed facts would be branch-unconditional — stop arming
/// for the remainder of the pass and drop everything armed so far.
pub(in crate::mir_analysis::extract) fn note_branching() {
    with_active(|registry| {
        if !registry.armed.is_empty() || !registry.carriers.is_empty() {
            debug!("borrow_carriers: branching — disarming all pending expiry facts");
        }
        registry.armed.clear();
        registry.poisoned = true;
    });
}

/// Unsupported statement/terminator: the walk's model is incomplete.
pub(in crate::mir_analysis::extract) fn note_unsupported() {
    with_active(|registry| {
        registry.armed.clear();
        registry.poisoned = true;
    });
}

/// A whole-local move of `local` outside the tracked mutating-call positions:
/// the borrow escapes our tracking.
pub(in crate::mir_analysis::extract) fn note_moved_local(local: Local) {
    with_active(|registry| {
        if registry.armed.remove(&local).is_some() {
            debug!(
                "borrow_carriers: borrow local {:?} moved — expiry fact disarmed",
                local
            );
        }
    });
}

/// A single-deref write `(*w) = value`: update the tracked death value for
/// `w` and every armed chain ancestor. When `w`'s chain membership is
/// unknown, we cannot prove it does not alias an armed borrow's pointee —
/// disarm everything (fail-closed).
pub(in crate::mir_analysis::extract) fn note_single_deref_write(w: Local, value: &PureExpr) {
    with_active(|registry| {
        let chain_known = registry.chain.contains_key(&w) || registry.armed.contains_key(&w);
        if !chain_known {
            if !registry.armed.is_empty() {
                debug!(
                    "borrow_carriers: deref write through untracked local {:?} — disarming all",
                    w
                );
                registry.armed.clear();
            }
            return;
        }
        let mut seen = HashSet::new();
        let mut current = w;
        loop {
            if let Some(tracker) = registry.armed.get_mut(&current) {
                *tracker = value.clone();
            }
            if !seen.insert(current) {
                break;
            }
            match registry.chain.get(&current) {
                Some(&base) => current = base,
                None => break,
            }
        }
    });
}

/// Any deeper deref-projected write (`(*w).f = ..`, `**w = ..`, ...): the
/// whole-value death tracking is stale — disarm everything (fail-closed).
pub(in crate::mir_analysis::extract) fn note_projected_deref_write() {
    with_active(|registry| {
        if !registry.armed.is_empty() {
            debug!("borrow_carriers: projected deref write — disarming all pending expiry facts");
        }
        registry.armed.clear();
    });
}

/// Disarm any `&mut`-typed whole-local MOVED by this rvalue: the borrow
/// escapes our tracking (into an aggregate, the return place, another local,
/// ...). Reborrows (`Rvalue::Ref`) are NOT moves and are deliberately not
/// scanned — they stay tracked through the chain.
pub(in crate::mir_analysis::extract) fn note_moved_mut_refs_in_rvalue<'tcx>(
    body: &Body<'tcx>,
    rvalue: &Rvalue<'tcx>,
) {
    let note = |op: &Operand<'tcx>| {
        if let Operand::Move(place) = op {
            if place.projection.is_empty()
                && matches!(
                    body.local_decls[place.local].ty.kind(),
                    rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
                )
            {
                note_moved_local(place.local);
            }
        }
    };
    match rvalue {
        Rvalue::Use(operand, _)
        | Rvalue::Cast(_, operand, _)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Repeat(operand, _) => note(operand),
        Rvalue::BinaryOp(_, (left, right)) => {
            note(left);
            note(right);
        }
        Rvalue::Aggregate(_, operands) => {
            for operand in operands {
                note(operand);
            }
        }
        _ => {}
    }
}

/// Disarm any `&mut`-typed whole-local MOVED into a call argument list. The
/// consumed mutating positions are handled by the mint lane (spec
/// resolution); a plain disarm here is always sound — it only suppresses a
/// caller-side expiry fact the callee's contract now owns.
pub(in crate::mir_analysis::extract) fn note_call_arg_moves<'tcx>(
    body: &Body<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
) {
    for arg in args {
        if let Operand::Move(place) = &arg.node {
            if place.projection.is_empty()
                && matches!(
                    body.local_decls[place.local].ty.kind(),
                    rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
                )
            {
                note_moved_local(place.local);
            }
        }
    }
}

/// Outcome of [`mint_carriers_for_call_args`]: the pending chain
/// advancements to apply after the shared receiver-state propagation runs.
pub(in crate::mir_analysis::extract) struct PendingChainAdvancement {
    consumed: Vec<Local>,
}

impl PendingChainAdvancement {
    pub(in crate::mir_analysis::extract) fn is_empty(&self) -> bool {
        self.consumed.is_empty()
    }
}

/// Phase A (before argument translation): for each mutating `&mut` argument
/// whose tracked value is a ground-constant tree and whose borrow chain is
/// fully known, mint the per-borrow carrier, rebind the argument local to it
/// (so the callee's contract instantiates a real prophecy variable), and —
/// when no deref write anywhere in the body reaches the borrow — assume the
/// callee-entry binding `*carrier == <tracked pointee value>`.
pub(in crate::mir_analysis::extract) fn mint_carriers_for_call_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    mutating_positions: &[usize],
    local_exprs: &mut HashMap<Local, PureExpr>,
    assumptions: &mut Vec<PureExpr>,
) -> PendingChainAdvancement {
    let mut pending = PendingChainAdvancement {
        consumed: Vec::new(),
    };
    for arg in mutating_positions.iter().filter_map(|idx| args.get(*idx)) {
        let Some(local) = super::closure::mut_ref_local_for_operand(body, &arg.node) else {
            // A mutating position we cannot resolve to a whole `&mut` local
            // may still write memory an armed borrow governs (a projected
            // reborrow through it) — disarm everything (fail-closed).
            with_active(|registry| registry.armed.clear());
            continue;
        };
        // The callee writes through this borrow: every armed ancestor's
        // tracked death value goes stale unless this argument gets a fresh
        // carrier (in which case `apply_chain_advancement` re-arms each
        // chain ancestor at the new post-call pointee). Disarm the stale
        // ones here; the ones we can re-track are re-armed in Phase B.
        // An argument with an UNKNOWN chain could be derived from any armed
        // borrow — disarm everything (fail-closed).
        let chain_known = with_active(|registry| {
            if registry.chain.contains_key(&local) {
                let mut seen = HashSet::new();
                let mut current = local;
                while let Some(&base) = registry.chain.get(&current) {
                    registry.armed.remove(&current);
                    if !seen.insert(current) {
                        break;
                    }
                    current = base;
                }
                registry.armed.remove(&current);
                true
            } else {
                registry.armed.remove(&local);
                if registry.armed.is_empty() {
                    true
                } else {
                    debug!(
                        "borrow_carriers: mutating call through chain-unknown local {:?} \
                         — disarming all",
                        local
                    );
                    registry.armed.clear();
                    false
                }
            }
        })
        .unwrap_or(false);
        let _ = chain_known;
        let Some(value) = local_exprs.get(&local).cloned() else {
            continue;
        };
        if !expr_is_ground_constant_tree(&value) {
            continue; // identity-bearing values keep the legacy lane
        }
        let minted = with_active(|registry| {
            if registry.full_chain(body, local).is_none() {
                // Incomplete chain: leave the legacy (fail-closed) behavior
                // untouched rather than advancing some bases and not others.
                return None;
            }
            let carrier = mint_carrier(tcx, body, arg_names, registry, local)?;
            let bind_entry = !registry.deref_write_reaches(local);
            Some((carrier, bind_entry))
        })
        .flatten();
        let Some((carrier, bind_entry)) = minted else {
            continue;
        };
        debug!(
            "borrow_carriers: minted per-borrow carrier {:?} for consumed borrow local {:?} \
             (was ground value {:?})",
            carrier, local, value
        );
        if bind_entry {
            assumptions.push(PureExpr::BinOp(
                Arc::new(PureExpr::Deref(Arc::new(carrier.clone()))),
                BinOp::Eq,
                Arc::new(value),
            ));
        }
        local_exprs.insert(local, carrier);
        pending.consumed.push(local);
    }
    pending
}

/// Phase A, closure-capture lane (#closure-capture-carriers): a state-mutating
/// call CONSUMES a closure environment whose by-`&mut` captures track ground
/// constants — the `^<constant>` defect shape lifted one level, into a capture
/// field. The environment tuple was built from the capture borrows' POINTEE
/// values (`tuple1(Int(1))`), so every downstream consumer — the callee-contract
/// instantiation, the capture post-state advancement (`final_receiver_state_expr`
/// wraps each field in `Final`), and the closure-ensures enrichment — mints
/// `^<constant>`, which the encoder refuses fail-closed (Fix A, constant-carrier
/// arm).
///
/// Repair, mirroring [`mint_carriers_for_call_args`]: mint a per-borrow carrier
/// keyed on the CAPTURE BORROW local, rebind the environment field (and the
/// borrow local) to it — so `Final(<field>)` becomes the real prophecy `^carrier`
/// everywhere at once — and, when no deref write in the body reaches the borrow,
/// assume the callee-entry binding `*carrier == <tracked pointee value>`. The
/// capture borrow itself is CONSUMED (it moves into the callee inside the
/// environment): it gets no caller-side expiry fact — the callee's contract is
/// the sole authority on its prophecy (RustHorn). Chain ancestors are advanced /
/// re-armed by the caller via [`apply_chain_advancement`], exactly like the
/// `&mut`-argument lane.
///
/// Fail-closed discipline: at a state-mutating closure call, EVERY armed expiry
/// fact is disarmed first (the callee writes through its captures; any armed
/// death value may go stale), and every capture field that does not match the
/// exact defect shape (whole-local `&mut` capture, fully-known unique-assignment
/// chain, ground-constant tracked value) keeps the legacy behavior.
/// A state-mutating closure call is observed: the callee writes through its
/// captures, so every armed death value may be stale after the call. Disarm
/// all pending expiry facts (fail-closed); Phase B re-arms what it can
/// re-track. (#closure-capture-carriers)
pub(in crate::mir_analysis::extract) fn note_closure_state_mutating_call() {
    with_active(|registry| {
        if !registry.armed.is_empty() {
            debug!(
                "borrow_carriers: state-mutating closure call — disarming all pending expiry facts"
            );
        }
        registry.armed.clear();
    });
}

pub(in crate::mir_analysis::extract) fn mint_carriers_for_closure_captures<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    closure_local: Local,
    local_exprs: &mut HashMap<Local, PureExpr>,
    assumptions: &mut Vec<PureExpr>,
) -> PendingChainAdvancement {
    let mut pending = PendingChainAdvancement {
        consumed: Vec::new(),
    };
    note_closure_state_mutating_call();
    // The consumed argument may be a whole-local move/copy of the aggregate
    // (`_5 = move _2; calls_closure(move _5)`): resolve back to the recorded
    // aggregate, keeping the whole copy chain so every alias of the
    // environment is rebound consistently below.
    let Some((env_locals, captures)) = with_active(|registry| {
        let env_locals = registry.resolve_closure_aggregate_chain(closure_local)?;
        let captures = registry
            .closure_env
            .get(env_locals.last().expect("chain is non-empty"))
            .cloned()?;
        Some((env_locals, captures))
    })
    .flatten() else {
        return pending;
    };
    let Some(PureExpr::LogicFnCall { name, args }) = local_exprs.get(&closure_local).cloned()
    else {
        return pending;
    };
    if tuple_logic_fn_arity(&name) != Some(args.len()) || args.len() != captures.len() {
        return pending; // environment shape unknown — legacy lane (fail-closed)
    }
    let mut new_args = args.clone();
    let mut minted_any = false;
    for (idx, capture) in captures.iter().enumerate() {
        let Some(borrow_local) = *capture else {
            continue;
        };
        let field_value = args[idx].clone();
        if !expr_is_ground_constant_tree(&field_value) {
            continue; // identity-bearing values keep the legacy lane
        }
        let minted = with_active(|registry| {
            if registry.full_chain(body, borrow_local).is_none() {
                // Incomplete chain: leave the legacy (fail-closed) behavior
                // untouched rather than advancing some bases and not others.
                return None;
            }
            let carrier = mint_carrier(tcx, body, arg_names, registry, borrow_local)?;
            let bind_entry = !registry.deref_write_reaches(borrow_local);
            Some((carrier, bind_entry))
        })
        .flatten();
        let Some((carrier, bind_entry)) = minted else {
            continue;
        };
        debug!(
            "borrow_carriers: minted per-borrow carrier {:?} for closure capture field {} \
             (borrow local {:?}, was ground value {:?})",
            carrier, idx, borrow_local, field_value
        );
        if bind_entry {
            assumptions.push(PureExpr::BinOp(
                Arc::new(PureExpr::Deref(Arc::new(carrier.clone()))),
                BinOp::Eq,
                Arc::new(field_value),
            ));
        }
        new_args[idx] = carrier.clone();
        local_exprs.insert(borrow_local, carrier);
        pending.consumed.push(borrow_local);
        minted_any = true;
    }
    if minted_any {
        let rebound_env = PureExpr::LogicFnCall {
            name,
            args: new_args,
        };
        // Rebind the consumed argument local, the aggregate local, and every
        // copy in between, so no alias of the environment keeps the stale
        // constant fields (the capture post-state propagation and name-level
        // substitutions read the aggregate local through its source name).
        for env_local in env_locals {
            local_exprs.insert(env_local, rebound_env.clone());
        }
    }
    pending
}

fn mint_carrier<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    registry: &mut BorrowCarrierRegistry,
    local: Local,
) -> Option<PureExpr> {
    let base = per_borrow_carrier_expr(tcx, body, arg_names, local)?;
    let carrier = if registry.carriers.contains_key(&local) {
        // Re-mint (e.g. the same local consumed on both arms of an already-
        // explored branch): keep names unique so callee-entry bindings from
        // distinct mint events can never contradict each other.
        let PureExpr::Var(name, sort) = base else {
            return None;
        };
        registry.mint_seq += 1;
        PureExpr::Var(format!("{name}$twp_m{}", registry.mint_seq), sort)
    } else {
        registry.mint_seq += 1;
        base
    };
    registry.carriers.insert(local, carrier.clone());
    Some(carrier)
}

/// Phase B (after the shared receiver-state propagation): advance every base
/// local in each consumed borrow's chain to `Final(<carrier of the local
/// that borrows it>)`, minting ancestor carriers along the way and arming
/// their expiry resolution.
pub(in crate::mir_analysis::extract) fn apply_chain_advancement<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    pending: &PendingChainAdvancement,
    local_exprs: &mut HashMap<Local, PureExpr>,
) {
    for &consumed in &pending.consumed {
        with_active(|registry| {
            let Some((links, _root)) = registry.full_chain(body, consumed) else {
                return;
            };
            let mut current = consumed;
            for _ in 0..links.len() {
                let Some(&base) = registry.chain.get(&current) else {
                    break;
                };
                let carrier = match registry.carriers.get(&current) {
                    Some(existing) => existing.clone(),
                    None => {
                        let Some(minted) = mint_carrier(tcx, body, arg_names, registry, current)
                        else {
                            break;
                        };
                        minted
                    }
                };
                let advanced = PureExpr::Final(Arc::new(carrier));
                debug!(
                    "borrow_carriers: advancing base local {:?} to {:?}",
                    base, advanced
                );
                local_exprs.insert(base, advanced);
                if current != consumed && !registry.poisoned {
                    // Non-consumed chain borrow: arm its expiry resolution.
                    // Its tracked death value starts at its just-advanced
                    // pointee (the prophecy of the borrow below it) and is
                    // updated by subsequent tracked deref writes.
                    if let Some(tracker) = local_exprs.get(&current).cloned() {
                        debug!(
                            "borrow_carriers: arming expiry for borrow local {:?} \
                             (initial death value {:?})",
                            current, tracker
                        );
                        registry.armed.insert(current, tracker);
                    }
                }
                let is_ref = matches!(
                    body.local_decls[base].ty.kind(),
                    rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
                );
                if !is_ref {
                    break;
                }
                current = base;
            }
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(v: i64) -> PureExpr {
        PureExpr::Int(v)
    }

    #[test]
    fn ground_constant_tree_detection() {
        assert!(expr_is_ground_constant_tree(&int(1)));
        assert!(expr_is_ground_constant_tree(&PureExpr::BinOp(
            Arc::new(int(1)),
            BinOp::Add,
            Arc::new(int(2)),
        )));
        assert!(!expr_is_ground_constant_tree(&PureExpr::Var(
            "x".into(),
            None
        )));
        assert!(!expr_is_ground_constant_tree(&PureExpr::Final(Arc::new(
            int(1)
        ))));
        assert!(!expr_is_ground_constant_tree(&PureExpr::BinOp(
            Arc::new(int(1)),
            BinOp::Add,
            Arc::new(PureExpr::Var("x".into(), None)),
        )));
    }

    fn registry_with_chain(chain: &[(u32, u32)]) -> BorrowCarrierRegistry {
        BorrowCarrierRegistry {
            chain: chain
                .iter()
                .map(|&(b, p)| (Local::from_u32(b), Local::from_u32(p)))
                .collect(),
            closure_env: HashMap::new(),
            copy_of: HashMap::new(),
            deref_written: HashSet::new(),
            carriers: HashMap::new(),
            armed: HashMap::new(),
            mint_seq: 0,
            poisoned: false,
        }
    }

    fn push_registry(registry: BorrowCarrierRegistry) {
        REGISTRY_STACK.with(|stack| stack.borrow_mut().push(registry));
    }

    fn mutref_var(name: &str) -> PureExpr {
        PureExpr::Var(
            name.to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        )
    }

    /// ★PIN (#124): the prophecies of DISTINCT borrows in one chain must be
    /// carried by DISTINCT variables — `^r` and `^r1` are never forced equal.
    /// (The pre-#124 advancement wrapped each base's own ground value, so a
    /// two-borrow chain collapsed both prophecies onto one shape; that is the
    /// second latent unsoundness named by the tract19 audit.)
    #[test]
    fn chain_advancement_mints_distinct_carriers_per_borrow() {
        // Chain: _3 (r1) -> _2 (r) -> _1 (x, root).
        let mut registry = registry_with_chain(&[(3, 2), (2, 1)]);
        let r1 = Local::from_u32(3);
        let r = Local::from_u32(2);
        let x = Local::from_u32(1);

        // Simulate the mint + advancement bookkeeping without MIR: mint
        // carriers directly and run the advancement algebra by hand through
        // the registry (the MIR-facing wrappers only resolve names/sorts).
        registry.carriers.insert(r1, mutref_var("r1"));
        registry.carriers.insert(r, mutref_var("r"));

        let carrier_r1 = registry.carriers[&r1].clone();
        let carrier_r = registry.carriers[&r].clone();
        assert_ne!(
            carrier_r1, carrier_r,
            "distinct borrows must get distinct prophecy carriers"
        );

        // The advancement shape: r ↦ ^r1, x ↦ ^r — the base is keyed on the
        // BORROWING local's carrier, never on the base's own value.
        let mut local_exprs: HashMap<Local, PureExpr> = HashMap::new();
        local_exprs.insert(x, int(1));
        local_exprs.insert(r, int(1));
        local_exprs.insert(r1, carrier_r1.clone());

        local_exprs.insert(r, PureExpr::Final(Arc::new(carrier_r1.clone())));
        local_exprs.insert(x, PureExpr::Final(Arc::new(carrier_r.clone())));

        assert_ne!(
            local_exprs[&r], local_exprs[&x],
            "^r1 (r's advanced value) and ^r (x's advanced value) must differ"
        );
        assert!(!expr_is_ground_constant_tree(&local_exprs[&r]));
        assert!(!expr_is_ground_constant_tree(&local_exprs[&x]));
    }

    /// The expiry fact tracks the LAST deref write through the borrow (or a
    /// tracked descendant), and emission yields `^carrier == <death value>`.
    #[test]
    fn expiry_tracks_last_deref_write_and_emits_at_end() {
        let mut registry = registry_with_chain(&[(3, 2), (2, 1)]);
        let r = Local::from_u32(2);
        registry.carriers.insert(r, mutref_var("r"));
        registry
            .armed
            .insert(r, PureExpr::Final(Arc::new(mutref_var("r1"))));
        push_registry(registry);

        // `*r = 2` after the call: the tracked death value updates.
        note_single_deref_write(r, &int(2));

        let facts = end_extraction_pass();
        assert_eq!(facts.len(), 1);
        let expected = PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(mutref_var("r")))),
            BinOp::Eq,
            Arc::new(int(2)),
        );
        assert_eq!(
            facts[0], expected,
            "expiry fact must be ^r == <death value>"
        );
    }

    /// FA-discipline pins: every invalidation route must DISARM, never emit.
    #[test]
    fn disarm_routes_suppress_expiry_facts() {
        // Branching poisons.
        let mut registry = registry_with_chain(&[(2, 1)]);
        let r = Local::from_u32(2);
        registry.carriers.insert(r, mutref_var("r"));
        registry.armed.insert(r, int(7));
        push_registry(registry);
        note_branching();
        assert!(end_extraction_pass().is_empty(), "branching must disarm");

        // A deref write through an UNTRACKED local disarms (possible alias).
        let mut registry = registry_with_chain(&[(2, 1)]);
        registry.carriers.insert(r, mutref_var("r"));
        registry.armed.insert(r, int(7));
        push_registry(registry);
        note_single_deref_write(Local::from_u32(9), &int(3));
        assert!(
            end_extraction_pass().is_empty(),
            "an untracked deref write must disarm"
        );

        // A projected deref write disarms.
        let mut registry = registry_with_chain(&[(2, 1)]);
        registry.carriers.insert(r, mutref_var("r"));
        registry.armed.insert(r, int(7));
        push_registry(registry);
        note_projected_deref_write();
        assert!(
            end_extraction_pass().is_empty(),
            "a projected deref write must disarm"
        );

        // A move of the armed borrow disarms it.
        let mut registry = registry_with_chain(&[(2, 1)]);
        registry.carriers.insert(r, mutref_var("r"));
        registry.armed.insert(r, int(7));
        push_registry(registry);
        note_moved_local(r);
        assert!(end_extraction_pass().is_empty(), "a move must disarm");

        // An unsupported statement disarms.
        let mut registry = registry_with_chain(&[(2, 1)]);
        registry.carriers.insert(r, mutref_var("r"));
        registry.armed.insert(r, int(7));
        push_registry(registry);
        note_unsupported();
        assert!(
            end_extraction_pass().is_empty(),
            "an unsupported statement must disarm"
        );
    }

    /// The consumed borrow gets NO caller-side expiry fact — its prophecy is
    /// the callee contract's to resolve (RustHorn).
    #[test]
    fn consumed_borrow_is_never_armed_by_emission() {
        let registry = registry_with_chain(&[(2, 1)]);
        push_registry(registry);
        // Nothing armed: nothing emitted.
        assert!(end_extraction_pass().is_empty());
    }

    /// ★PIN (#closure-capture-carriers): the closure aggregate chain resolver
    /// follows whole-local copies back to the recorded aggregate (the
    /// `_5 = move _2; call(move _5)` shape), returns the full alias chain for
    /// consistent rebinding, and fails closed on unknown links and cycles.
    #[test]
    fn closure_aggregate_chain_resolves_through_copies_and_fails_closed() {
        let mut registry = registry_with_chain(&[(3, 1)]);
        let agg = Local::from_u32(2);
        let arg = Local::from_u32(5);
        registry
            .closure_env
            .insert(agg, vec![Some(Local::from_u32(3))]);
        registry.copy_of.insert(arg, agg);

        // Direct hit and copy-chased hit, chain inclusive of both ends.
        assert_eq!(
            registry.resolve_closure_aggregate_chain(agg),
            Some(vec![agg])
        );
        assert_eq!(
            registry.resolve_closure_aggregate_chain(arg),
            Some(vec![arg, agg])
        );

        // Unknown local: fail closed.
        assert_eq!(
            registry.resolve_closure_aggregate_chain(Local::from_u32(9)),
            None
        );

        // Copy cycle: fail closed.
        let mut cyclic = registry_with_chain(&[]);
        cyclic
            .copy_of
            .insert(Local::from_u32(7), Local::from_u32(8));
        cyclic
            .copy_of
            .insert(Local::from_u32(8), Local::from_u32(7));
        assert_eq!(
            cyclic.resolve_closure_aggregate_chain(Local::from_u32(7)),
            None
        );
    }

    /// ★PIN (#closure-capture-carriers): at a state-mutating closure call,
    /// EVERY armed expiry fact is disarmed before minting (the callee writes
    /// through its captures — any tracked death value may go stale). Same
    /// disarm-on-uncertainty discipline as the `&mut`-argument lane.
    #[test]
    fn closure_capture_mint_disarms_pending_expiry_facts() {
        let mut registry = registry_with_chain(&[(2, 1)]);
        let r = Local::from_u32(2);
        registry.carriers.insert(r, mutref_var("r"));
        registry.armed.insert(r, int(7));
        push_registry(registry);

        // The disarm runs UNCONDITIONALLY at the top of the closure mint lane
        // — even when the environment later fails to resolve, the armed fact
        // must already be gone (fail-closed).
        note_closure_state_mutating_call();
        assert!(
            end_extraction_pass().is_empty(),
            "a state-mutating closure call must disarm pending expiry facts"
        );
    }
}
