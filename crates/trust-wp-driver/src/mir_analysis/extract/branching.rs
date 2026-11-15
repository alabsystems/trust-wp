// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//! Branching and switch extraction logic for MIR control flow.
//!
//! Contains handlers for boolean and integer `SwitchInt` terminators
//! and switch guard assumption construction.
//!
//! Try-operator (`?`) pattern recognition lives in [`super::try_operator`].

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_middle::{
    mir::{BasicBlock, Body, Local, SwitchTargets, TerminatorKind},
    ty::TyCtxt,
};
use trust_wp_core::formula::{BinOp, PureExpr, UnOp};

use super::{
    super::{
        diagnostics::ExtractionDiagKind,
        effects::{fail_closed_marker, CallEffects},
    },
    branching_diag::record_switch_diag,
    extract_from_block_with_context,
    helpers::{
        block_can_reach_cutoff, block_can_reach_location, block_diverges_via_panic,
        block_must_diverge, block_must_early_return, join_with_and, join_with_or,
        switch_discr_is_single_call_result, switch_discr_is_value_stable, wrap_projected_facts,
    },
    panic_site_coverage::{record_switch_edge, walked_path},
    BlockExtractionContext,
};
use crate::mir_analysis::translate::{switch_value_to_expr, switch_value_to_i64, DiscrIntTy};

/// Owned traversal state for a boolean SwitchInt branch handler.
///
/// Bundles the per-block extraction state (`local_exprs`, `visited`,
/// `projected_write_facts`) together with the source basic block `bb`
/// (used only for diagnostics). This avoids passing five separate
/// parameters through `handle_bool_switch_with_context`. (#2657)
pub(super) struct BoolSwitchState {
    pub(super) bb: BasicBlock,
    pub(super) local_exprs: HashMap<Local, PureExpr>,
    pub(super) visited: HashSet<BasicBlock>,
    pub(super) projected_write_facts: Vec<(PureExpr, PureExpr)>,
}

/// Owned traversal state for an integer/enum SwitchInt branch handler.
///
/// Bundles the per-block extraction state (`local_exprs`, `visited`,
/// `projected_write_facts`) together with `discr_int_ty` (the integer
/// type of the switch discriminant, needed for value decoding).
pub(super) struct IntSwitchState {
    /// Source basic block of the switch, from which the discriminant operand
    /// is recovered for the panic-arm value-stability check.
    pub(super) bb: BasicBlock,
    pub(super) discr_int_ty: DiscrIntTy,
    pub(super) local_exprs: HashMap<Local, PureExpr>,
    pub(super) visited: HashSet<BasicBlock>,
    pub(super) projected_write_facts: Vec<(PureExpr, PureExpr)>,
}

fn cutoff_mode(ctx: &BlockExtractionContext<'_>) -> bool {
    ctx.cutoff_span.is_some() || ctx.cutoff_location.is_some()
}

/// Count extraction diagnostics recorded so far.
fn diag_count(ctx: &BlockExtractionContext<'_>) -> usize {
    ctx.diagnostics
        .map_or(0, |sink| sink.borrow().entries.len())
}

/// Whether a failed branch only emitted `ControlFlowCycle` diagnostics.
///
/// A branch that failed purely on a loop back-edge is treated like a
/// diverging one and the sibling branch is recovered
/// (`handle_bool_switch_with_context`). If extraction records any other
/// diagnostic, the failure is not attributable solely to the cycle and the
/// collapse to the sibling must not happen.
#[allow(clippy::ref_option)] // &Option<PureExpr> matches call-site ownership
fn failed_only_due_to_cycle(
    ctx: &BlockExtractionContext<'_>,
    diag_start: usize,
    branch_expr: &Option<PureExpr>,
) -> bool {
    if branch_expr.is_some() {
        return false;
    }
    ctx.diagnostics.is_some_and(|sink| {
        let diagnostics = sink.borrow();
        let new_entries = &diagnostics.entries[diag_start..];
        !new_entries.is_empty()
            && new_entries
                .iter()
                .all(|entry| entry.kind == ExtractionDiagKind::ControlFlowCycle)
    })
}

fn block_reaches_cutoff<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    ctx: &BlockExtractionContext<'_>,
) -> bool {
    if let Some(location) = ctx.cutoff_location {
        return block_can_reach_location(body, bb, location, &mut HashSet::new());
    }
    if let Some(cutoff) = ctx.cutoff_span {
        return block_can_reach_cutoff(body, bb, cutoff, &mut HashSet::new());
    }
    false
}

/// Build the branch guard implied by taking a concrete SwitchInt target.
///
/// Used in cutoff mode (`proof_assert` extraction): when only one branch can
/// reach the assertion site, that branch's discriminant condition must become
/// an explicit assumption to preserve path sensitivity for the VC.
pub(super) fn switch_target_guard_assumption(
    discr_expr: &PureExpr,
    targets: &SwitchTargets,
    target_bb: BasicBlock,
    discr_int_ty: DiscrIntTy,
) -> Option<PureExpr> {
    if target_bb == targets.otherwise() {
        let mut guards = Vec::new();
        for (value, _) in targets.iter() {
            let value_i64 = switch_value_to_i64(value, discr_int_ty)?;
            let eq = PureExpr::BinOp(
                Arc::new(discr_expr.clone()),
                BinOp::Eq,
                Arc::new(PureExpr::Int(value_i64)),
            );
            guards.push(PureExpr::UnOp(UnOp::Not, Arc::new(eq)));
        }
        return if guards.is_empty() {
            Some(PureExpr::Bool(true))
        } else {
            join_with_and(guards)
        };
    }

    let mut guards = Vec::new();
    for (value, target) in targets.iter() {
        if target != target_bb {
            continue;
        }
        let value_i64 = switch_value_to_i64(value, discr_int_ty)?;
        guards.push(PureExpr::BinOp(
            Arc::new(discr_expr.clone()),
            BinOp::Eq,
            Arc::new(PureExpr::Int(value_i64)),
        ));
    }
    join_with_or(guards)
}

/// The condition under which ONE walk of the arm `target` runs: `condition ==
/// value` for the walk of a valued arm, and `!(condition == v)` for every
/// value of the switch for the walk of the otherwise arm. Values are spelled by
/// `switch_value_to_expr`, the spelling the arm's `Ite` uses, so a value
/// outside `i64` still forms its equality.
fn switch_walk_edge_condition(
    condition: &PureExpr,
    targets: &SwitchTargets,
    walked_value: Option<u128>,
    discr_int_ty: DiscrIntTy,
) -> Option<PureExpr> {
    let equals = |value: u128| -> Option<PureExpr> {
        Some(PureExpr::BinOp(
            Arc::new(condition.clone()),
            BinOp::Eq,
            Arc::new(switch_value_to_expr(value, discr_int_ty)?),
        ))
    };
    match walked_value {
        Some(value) => equals(value),
        None => {
            let mut excluded = Vec::new();
            for (value, _) in targets.iter() {
                excluded.push(PureExpr::UnOp(UnOp::Not, Arc::new(equals(value)?)));
            }
            Some(join_with_and(excluded).unwrap_or(PureExpr::Bool(true)))
        }
    }
}

/// The arm one walk of a switch ran, for the edge that scopes its premises.
#[derive(Clone, Copy)]
enum WalkedArm {
    /// A boolean switch's true arm: `c`.
    Then,
    /// A boolean switch's false arm: `!c`.
    Else,
    /// An integer switch's arm for one value: `c == v`.
    Value(u128),
    /// An integer switch's otherwise arm: `!(c == v)` for every value.
    Otherwise,
}

/// The condition that may scope one switch's arm premises, found at most once
/// per switch and only when an arm recorded a premise.
///
/// It must denote the value the switch tests. The walk's translated condition
/// does when the discriminant is value-stable (`switch_at_block_is_value_stable`,
/// the test the arm's panic goal uses). When it is not, but the discriminant
/// is a local whose only definition is one call
/// (`switch_discr_is_single_call_result`), that call's result symbol does: it
/// names the value the call returned, which is the value the switch reads,
/// whatever memory the call's arguments read and however the call lane
/// translated the result (`x.id_ghost() == y.id_ghost()` on `x: &mut _` is
/// translated through `eq`'s postcondition to a condition over `x`).
struct PremiseEdge<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    switch_bb: BasicBlock,
    targets: &'a SwitchTargets,
    discr_int_ty: Option<DiscrIntTy>,
    condition: &'a PureExpr,
    faithful: Option<Option<PureExpr>>,
}

impl<'a, 'tcx> PremiseEdge<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        switch_bb: BasicBlock,
        targets: &'a SwitchTargets,
        discr_int_ty: Option<DiscrIntTy>,
        condition: &'a PureExpr,
    ) -> Self {
        Self {
            tcx,
            body,
            switch_bb,
            targets,
            discr_int_ty,
            condition,
            faithful: None,
        }
    }

    fn faithful_condition(&mut self) -> Option<PureExpr> {
        self.faithful
            .get_or_insert_with(|| {
                if switch_at_block_is_value_stable(self.tcx, self.body, self.switch_bb) {
                    return Some(self.condition.clone());
                }
                let TerminatorKind::SwitchInt { discr, .. } =
                    &self.body.basic_blocks[self.switch_bb].terminator().kind
                else {
                    return None;
                };
                switch_discr_is_single_call_result(self.body, discr, self.switch_bb)
                    .map(|local| super::call_args::call_result_symbol(self.body, local, self.tcx))
            })
            .clone()
    }

    /// The condition under which the walk of `arm` runs, spelled over the
    /// faithful condition, or `None` when there is none.
    fn edge(&mut self, arm: WalkedArm) -> Option<PureExpr> {
        let condition = self.faithful_condition()?;
        match arm {
            WalkedArm::Then => Some(condition),
            WalkedArm::Else => Some(PureExpr::UnOp(UnOp::Not, Arc::new(condition))),
            WalkedArm::Value(value) => switch_walk_edge_condition(
                &condition,
                self.targets,
                Some(value),
                self.discr_int_ty?,
            ),
            WalkedArm::Otherwise => {
                switch_walk_edge_condition(&condition, self.targets, None, self.discr_int_ty?)
            }
        }
    }
}

/// Scope the assumptions ONE arm walk recorded (`assumptions[snapshot..]`) to
/// that arm: each becomes `edge ==> assumption`.
///
/// The primary walk keeps assumptions in one flat list, and every goal of the
/// function is proved under every assumption. A callee's postcondition
/// assumed on one arm (`if flag { below(x) }`) holds only on executions that
/// took the arm, so unscoped it discharges the goals the walk states on the
/// sibling arms (`!flag ==> !(x >= 100)`) and a panic arm's unreachability
/// goal, which is pushed after both arms are walked and so escapes the
/// earlier-obligation guard a call puts on its postconditions
/// (`assert!(x < 100); below(x);`). The arms' edge conditions are pairwise
/// exclusive, so a premise scoped to one arm cannot discharge a goal owed only
/// where a sibling's edge holds, whether or not that goal carries its own
/// guard: an execution that takes another arm falsifies the edge and
/// satisfies the premise.
///
/// The literal `false` is left alone: it is the `assert!(false)` marker the
/// arm's gate turns into the unreachability OBLIGATION `!edge`, and assuming
/// `edge ==> false`, i.e. `!edge`, would grant that goal instead of owing it.
///
/// The edge scopes a premise only if it denotes the branch the execution
/// really takes: a condition read through memory the extractor cannot track
/// may be stale, and `stale ==> a` hands `a` to an execution that took a
/// sibling arm. So with no faithful condition (`PremiseEdge`), the arm's other
/// assumptions are dropped, never kept unscoped. SOUND: `edge ==> a` is
/// implied by `a`, and dropping `a` removes it, so this only removes
/// derivations.
fn guard_branch_assumptions(
    effects: &mut CallEffects,
    snapshot: usize,
    arm: WalkedArm,
    premise_edge: &mut PremiseEdge<'_, '_>,
) {
    if effects.assumptions.len() <= snapshot {
        return;
    }
    let edge = premise_edge.edge(arm);
    scope_arm_assumptions(effects, snapshot, edge.as_ref());
}

/// Guard the obligations ONE walk of a plain integer match arm recorded
/// (`obligations[snapshot..]`) by that arm's edge: each becomes
/// `edge ==> obligation`, the obligation being owed only on executions that
/// take the arm.
///
/// The edge is the one the arm's premises are scoped by (`PremiseEdge`), so a
/// premise the arm establishes and a goal the arm owes are read under the same
/// condition: without it, `match pick(a) { 0 => { below(x); assert!(x < 100) }
/// .. }` scoped `below`'s postcondition to `pick(a) == 0` and owed the assert on
/// every path. The condition denotes the value the switch tests at every point
/// of the body, so a term it shares with an obligation found later in the arm
/// reads the same value there. With no faithful condition the obligations stay
/// unconditional: stronger, never unsound.
fn guard_int_arm_obligations(
    effects: &mut CallEffects,
    snapshot: usize,
    arm: WalkedArm,
    premise_edge: &mut PremiseEdge<'_, '_>,
) {
    if effects.obligations.len() <= snapshot {
        return;
    }
    let edge = premise_edge.edge(arm);
    guard_arm_obligations_by_edge(effects, snapshot, edge.as_ref());
}

/// `guard_int_arm_obligations` once the edge is known (`Some`) or refused
/// (`None`, the obligations stay unconditional).
///
/// A literal `false` stays unconditional. It is either a fail-closed marker the
/// walk owes for a construct it cannot model, or a callee's written
/// `requires(false)`, and the verdict tells them apart by that literal alone
/// (`fail_closed_marker_count`, `user_written_false_obligations`): wrapped in
/// the edge, a marker no longer withholds the refutation it manufactures, and
/// the count of written ones subtracts a marker instead. Unconditional, the
/// goal is only stronger: never unsound, and an arm a precondition excludes
/// still owes its `false`, as every integer arm did before the edge.
fn guard_arm_obligations_by_edge(
    effects: &mut CallEffects,
    snapshot: usize,
    edge: Option<&PureExpr>,
) {
    let Some(edge) = edge else {
        return;
    };
    for obligation in effects.obligations.iter_mut().skip(snapshot) {
        if pure_expr_is_literal_false(obligation) {
            continue;
        }
        let owed = std::mem::replace(obligation, PureExpr::Bool(true));
        *obligation = PureExpr::BinOp(Arc::new(edge.clone()), BinOp::Implies, Arc::new(owed));
    }
}

/// `guard_branch_assumptions` once the edge is known to be faithful (`Some`)
/// or not usable (`None`).
fn scope_arm_assumptions(effects: &mut CallEffects, snapshot: usize, edge: Option<&PureExpr>) {
    let Some(edge) = edge else {
        let mut index = snapshot;
        while index < effects.assumptions.len() {
            if pure_expr_is_literal_false(&effects.assumptions[index]) {
                index += 1;
            } else {
                effects.assumptions.remove(index);
            }
        }
        return;
    };
    let mut start = snapshot;
    while start < effects.assumptions.len() {
        let end = effects.assumptions[start..]
            .iter()
            .position(pure_expr_is_literal_false)
            .map_or(effects.assumptions.len(), |offset| start + offset);
        crate::mir_analysis::effects::guard_assumptions(
            &mut effects.assumptions[start..end],
            Some(edge),
        );
        start = end + 1;
    }
}

/// Whether a `SwitchInt` discriminant condition is an *enum discriminant* read
/// (`discriminant(place)`), as opposed to a plain integer scrutinee.
///
/// Enum `match`es lower to `_d = discriminant(scrutinee); switchInt(_d) { .. }`,
/// and `Rvalue::Discriminant` is translated to a
/// `MethodCall { method: "discriminant" }` (see `translate/rvalue.rs`). This gate
/// keeps the arm-path-condition obligation guarding (below) scoped to enum
/// matches, where the arm is entered under a genuine variant refinement.
/// Plain integer `match`es guard by the edge their premises are scoped by
/// (`guard_int_arm_obligations`), booleans by their own condition; a refused
/// guard is a completeness cost only (see `guard_branch_obligations`).
fn condition_is_enum_discriminant(condition: &PureExpr) -> bool {
    matches!(
        condition,
        PureExpr::MethodCall { method, .. } if method == "discriminant"
    )
}

/// Retroactively guard the obligations collected while extracting a single
/// enum-discriminant `SwitchInt` branch with that branch's path condition.
///
/// Obligations discovered inside a `match` arm body — e.g. a callee precondition
/// on a recursive call such as `l.sum_x()` inside `match self { Cons(a,l) => .. }`
/// — are appended to the flat `effects.obligations` list *without* the arm's
/// discriminant refinement, because the arm's guard is otherwise only re-attached
/// to the return *value* (the `Ite` chain), never to the obligations. The MIR
/// switch edge enters the arm only under `discriminant(self) == <variant_index>`
/// (equivalently `is-<Ctor>(self)`), so — by the weakest-precondition calculus —
/// the obligation is only required to hold on that path. This rewrites each
/// obligation added since `snapshot` into `guard ==> obligation`, mirroring the
/// loop-body walker's `wrap_with_guard` (see `loop_body.rs`).
///
/// SOUND / completeness-improving: `guard` is the exact MIR switch-edge condition
/// (`switch_target_guard_assumption`) for this branch, so this only *weakens* each
/// obligation to its true reachability — it can make more obligations provable
/// (UNSAT), never fewer, and never masks a genuinely-reachable failure. A `None`
/// guard (unrepresentable switch value) leaves the obligations unconditional
/// (strictly conservative). Applied only under `condition_is_enum_discriminant`.
/// Whether a branch condition still denotes the same value at the call site.
///
/// `guard_branch_obligations` rewrites an obligation into `guard ==> obligation`,
/// and that is only the weakest-precondition rule if `guard` and `obligation`
/// are read at the same program point. Between the switch and the call, the arm
/// body runs — and this extractor does not propagate a store through a
/// projection into a later call-argument expression (see the
/// `place.projection.is_empty()` gate in `primary.rs`). So for a guard that
/// reads through a reference or a field, the *pre-store* condition and the
/// *post-store* argument print as the same `PureExpr`:
///
/// ```text
/// if s.f >= 0 { s.f = -1; callee(s.f) } else { 0 }
/// ```
///
/// Both the guard and the callee's substituted precondition come out as
/// `__trust_wp_tuple_get_0(*s) >= 0`, so `guard ==> obligation` is `X ==> X`,
/// its negation is UNSAT, and a function that genuinely calls `callee(-1)` on
/// every reachable path through the branch verifies. That is a false accept —
/// exactly the failure mode `invalidate_overlapping_projected_write_facts`
/// (`primary.rs`) exists for: stale facts that survive calls mutating the
/// referenced path produce vacuous verification.
///
/// Rather than assume the arm performs no such store, this refuses to guard at
/// all whenever the condition reads memory the arm could have rewritten. A
/// refused guard leaves the obligation unconditional: conservative, possibly
/// incomplete, never unsound. A by-value comparison on a plain local carries
/// no such read and is guarded normally.
fn guard_reads_only_immutable_locals(guard: &PureExpr) -> bool {
    match guard {
        // A dereference or a field/tuple projection is a memory read whose
        // value the arm may have changed before the call.
        PureExpr::Deref(_) => false,
        PureExpr::LogicFnCall { name, .. } if name.starts_with("__trust_wp_tuple_get_") => false,
        // A method call can read through `self` and can be a projection
        // accessor in disguise; `discriminant` is the one the enum lane
        // depends on, and a discriminant read is invalidated by a store to the
        // scrutinee just as a field read is.
        PureExpr::MethodCall { receiver, args, .. } => {
            guard_reads_only_immutable_locals(receiver)
                && args.iter().all(guard_reads_only_immutable_locals)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().all(guard_reads_only_immutable_locals),
        PureExpr::BinOp(left, _, right) => {
            guard_reads_only_immutable_locals(left) && guard_reads_only_immutable_locals(right)
        }
        PureExpr::UnOp(_, inner) | PureExpr::View(inner) | PureExpr::Old(inner) => {
            guard_reads_only_immutable_locals(inner)
        }
        PureExpr::Ite(condition, then_branch, else_branch) => {
            guard_reads_only_immutable_locals(condition)
                && guard_reads_only_immutable_locals(then_branch)
                && guard_reads_only_immutable_locals(else_branch)
        }
        // `^p` is by definition the post-mutation value: it never denotes what
        // the switch read.
        PureExpr::Final(_) => false,
        PureExpr::Var(..) | PureExpr::Int(_) | PureExpr::Bool(_) => true,
        // Anything not enumerated here is refused rather than assumed safe:
        // the cost of refusing is an obligation that stays unconditional, and
        // the cost of wrongly allowing is a false "verified".
        _ => false,
    }
}

/// `!true` -> `false`, `!false` -> `true`; anything else unchanged.
///
/// A diverging THEN arm's fact is built as `!condition`, so on a literal
/// switch it arrives as `!true` / `!false`, and the literal route in
/// `push_returning_path_fact` must see the literal. Unfolded, the statically
/// taken `if true { panic!() }` arm missed that route, and `!true` became a
/// returning-path fact premising every postcondition with `false` while no
/// lane charged the panic (`literal_true_switch_panic_arm*` adversarial
/// cases).
fn fold_negated_literal(fact: PureExpr) -> PureExpr {
    match fact {
        PureExpr::UnOp(UnOp::Not, inner) => match inner.as_ref() {
            PureExpr::Bool(value) => PureExpr::Bool(!value),
            _ => PureExpr::UnOp(UnOp::Not, inner),
        },
        other => other,
    }
}

/// Record a #1075/#1401 surviving-path fact: the function only RETURNS through
/// paths where `fact` holds. Facts premise only the function's own
/// postconditions (see `CallEffects::returning_path_facts`), never obligations.
///
/// Dropped (a completeness cost only) when the switch condition may be stale
/// (read through tracked-unstable memory) or the fact reads memory whose
/// entry/final meaning differs from the postcondition's (a dereference, a
/// projection, a method call).
fn push_returning_path_fact<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    switch_bb: BasicBlock,
    effects: &mut CallEffects,
    fact: PureExpr,
) {
    // A literal fact comes from a switch on a constant. A literal `false` is
    // the `assert!(false)` shape: it stays a literal-`false` ASSUMPTION,
    // because the enclosing switch's `gate_constant_false_branch_assumptions`
    // converts it into the unreachability OBLIGATION `!guard` (routed here
    // instead, `if x > 0 { assert!(false) }` verifies). A literal `true` fact
    // says nothing and is dropped.
    let fact = fold_negated_literal(fact);
    match fact {
        PureExpr::Bool(false) => {
            effects.assumptions.push(fact);
            return;
        }
        PureExpr::Bool(true) => return,
        _ => {}
    }
    if guard_reads_only_immutable_locals(&fact)
        && switch_at_block_is_value_stable(tcx, body, switch_bb)
    {
        effects.returning_path_facts.push(fact);
    }
}

/// Guard the returning-path facts an arm walk discovered with the arm's edge
/// condition: `guard ==> fact`. A fact found inside one arm says nothing about
/// paths through the sibling arms. When the guard is unavailable or may be
/// stale, the arm's facts are DROPPED (never kept unguarded).
fn guard_branch_returning_path_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    switch_bb: BasicBlock,
    effects: &mut CallEffects,
    snapshot: usize,
    guard: Option<PureExpr>,
) {
    if effects.returning_path_facts.len() <= snapshot {
        return;
    }
    match guard {
        Some(guard)
            if guard_reads_only_immutable_locals(&guard)
                && switch_at_block_is_value_stable(tcx, body, switch_bb) =>
        {
            for fact in effects.returning_path_facts.iter_mut().skip(snapshot) {
                let existing = std::mem::replace(fact, PureExpr::Bool(true));
                *fact =
                    PureExpr::BinOp(Arc::new(guard.clone()), BinOp::Implies, Arc::new(existing));
            }
        }
        _ => effects.returning_path_facts.truncate(snapshot),
    }
}

fn guard_branch_obligations(effects: &mut CallEffects, snapshot: usize, guard: Option<PureExpr>) {
    guard_branch_obligations_if(effects, snapshot, guard, false);
}

/// [`guard_branch_obligations`] for a bool switch whose discriminant reads
/// only frozen memory ([`switch_discr_reads_frozen_memory`]): a guard reading
/// through a shared reference or a closure capture is then read at the same
/// value where the obligation is, and guards it.
fn guard_bool_branch_obligations<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    switch_bb: BasicBlock,
    effects: &mut CallEffects,
    snapshot: usize,
    guard: PureExpr,
) {
    let frozen = match &body.basic_blocks[switch_bb].terminator().kind {
        TerminatorKind::SwitchInt { discr, .. } => {
            super::helpers::switch_discr_reads_frozen_memory(tcx, body, discr)
        }
        _ => false,
    };
    guard_branch_obligations_if(effects, snapshot, Some(guard), frozen);
}

fn guard_branch_obligations_if(
    effects: &mut CallEffects,
    snapshot: usize,
    guard: Option<PureExpr>,
    discr_reads_frozen_memory: bool,
) {
    let Some(guard) = guard else {
        return;
    };
    if !discr_reads_frozen_memory && !guard_reads_only_immutable_locals(&guard) {
        return;
    }
    for obligation in effects.obligations.iter_mut().skip(snapshot) {
        let existing = std::mem::replace(obligation, PureExpr::Bool(true));
        *obligation = PureExpr::BinOp(Arc::new(guard.clone()), BinOp::Implies, Arc::new(existing));
    }
}

/// Detect whether a `PureExpr` is the literal `false` constant.
///
/// Used to recognise the divergence-path assumption produced by an
/// `assert!(false)` / `panic!()` reachability check (see
/// [`gate_constant_false_branch_assumptions`]).
fn pure_expr_is_literal_false(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Bool(false))
}

/// Turn an `assert!(false)` divergence into a genuine *unreachability
/// obligation* `guard ⟹ false` (equivalently `!guard`).
///
/// When a switch branch body contains `assert!(false)` (or any always-failing
/// `assert!`), the assert-fact extraction records the surviving-path condition
/// (`false`) as a global assumption in `effects.assumptions` (see
/// `wrap_continuation_with_assert_fact`). That literal `false` loses the
/// *enclosing* branch guard `G` under which the assertion was reached.
///
/// Two tempting treatments are both wrong:
///
/// * Leaving the `false` in place poisons the whole function context with an
///   unconditional contradiction: every obligation "proves" vacuously and the
///   vacuity guard then reports the function as `vacuous` rather than verifying
///   it (e.g. `peek_bit_array8`'s provably-unreachable `None` arm).
/// * Rewriting `false` into a `!guard` *assumption* is UNSOUND: it grants
///   `!guard` for free without proving the branch is
///   unreachable. For a reachable branch (e.g. `if a == b { assert!(false); }`
///   with `#[ensures(a@ != b@)]`) it hands the solver `a != b` and the bogus
///   postcondition "verifies".
///
/// The correct WP treatment of `assert!(false)` reached under guard `G` is:
/// the program asserts the branch is unreachable, so we must *prove*
/// `G ⟹ false`, i.e. prove `!G`. This drops the literal-`false` assumption and
/// pushes `!guard` as a real proof OBLIGATION (which is merged into the
/// function's `effective_ensures` and discharged under the function's
/// preconditions, never assumed). Then:
///
/// * `peek_bit_array8`'s `None` arm (`guard` = `addr.get(left/8) == None`) is
///   provably unreachable under `#[requires(left < 8 * addr.len())]`, so the
///   obligation discharges and the function still verifies.
/// * `bogus`'s `a == b` arm has no precondition forbidding `a == b`, so the
///   obligation `a != b` fails and the function is correctly REJECTED.
///
/// Returns `true` when an unreachability obligation was emitted, so the
/// SwitchInt handler knows this branch's divergence is an *assert-false*
/// divergence and must NOT additionally assume the negated path condition (the
/// obligation already establishes — and must be allowed to fail on — it; also,
/// assuming `!guard` while obligated to prove it would make the obligation
/// vacuous, re-introducing the unsoundness).
fn gate_constant_false_branch_assumptions(
    effects: &mut CallEffects,
    snapshot_len: usize,
    guard: Option<&PureExpr>,
) -> bool {
    let Some(guard) = guard else {
        return false;
    };
    let mut emitted_unreachability_obligation = false;
    let mut idx = snapshot_len;
    while idx < effects.assumptions.len() {
        if pure_expr_is_literal_false(&effects.assumptions[idx]) {
            // Drop the literal-`false` assumption and replace it with a real
            // proof obligation `!guard` (i.e. prove the branch unreachable).
            effects.assumptions.remove(idx);
            effects
                .obligations
                .push(PureExpr::UnOp(UnOp::Not, Arc::new(guard.clone())));
            emitted_unreachability_obligation = true;
        } else {
            idx += 1;
        }
    }
    emitted_unreachability_obligation
}

/// Whether the `SwitchInt` at `bb` has a value-stable discriminant (see
/// `switch_discr_is_value_stable`). Anything but a `SwitchInt` terminator is
/// reported unstable, so callers fail closed.
fn switch_at_block_is_value_stable<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
) -> bool {
    match &body.basic_blocks[bb].terminator().kind {
        TerminatorKind::SwitchInt { discr, .. } => {
            switch_discr_is_value_stable(tcx, body, discr, false)
        }
        _ => false,
    }
}

/// A match arm that diverges into a panic entry point
/// (`unreachable!()`, `panic!()`, ...) must be PROVED unreachable, so push
/// `!guard` as an obligation. The arm's recovery `LetAssume` over the surviving
/// arms stays scoped to the result expression and is backed by this proof.
/// A guard that cannot be reconstructed — or whose discriminant is not value
/// stable — fails closed as the obligation `false`.
///
/// The caller then treats the arm like an `assert!(false)` arm: its negated
/// guard is EXCLUDED from the surviving-arm recovery `LetAssume`, because ay
/// hoists a result-position `LetAssume` into the unconditional premise set and
/// assuming `!guard` there would make this obligation vacuous.
fn push_panic_arm_unreachability_obligation(effects: &mut CallEffects, guard: Option<PureExpr>) {
    effects.obligations.push(match guard {
        Some(guard) => PureExpr::UnOp(UnOp::Not, Arc::new(guard)),
        None => fail_closed_marker("panic-arm-guard-unreconstructed"),
    });
}

/// Handle boolean `SwitchInt` in the context-aware extractor.
///
/// Translates a MIR boolean branch (`if condition { ... } else { ... }`) into a
/// `PureExpr::Ite` or `PureExpr::LetAssume` depending on cutoff scoping and
/// branch divergence analysis.
pub(super) fn handle_bool_switch_with_context<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    condition: PureExpr,
    targets: &SwitchTargets,
    state: BoolSwitchState,
    ctx: &BlockExtractionContext<'_>,
    effects: &mut CallEffects,
) -> Option<PureExpr> {
    let BoolSwitchState {
        bb,
        local_exprs,
        visited,
        projected_write_facts,
    } = state;
    let walked = walked_path(body, &visited);
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
        record_switch_diag(
            ctx,
            body,
            bb,
            ExtractionDiagKind::UnsupportedSwitchShape,
            "bool SwitchInt collapsed to a single successor",
        );
        return None;
    }
    if cutoff_mode(ctx) {
        let then_reaches_cutoff = block_reaches_cutoff(body, then_bb, ctx);
        let else_reaches_cutoff = block_reaches_cutoff(body, else_bb, ctx);
        match (then_reaches_cutoff, else_reaches_cutoff) {
            (true, false) => {
                let then_expr = wrap_projected_facts(
                    projected_write_facts.to_owned(),
                    extract_from_block_with_context(
                        tcx,
                        body,
                        then_bb,
                        local_exprs,
                        visited,
                        ctx,
                        effects,
                    ),
                )?;
                return Some(PureExpr::LetAssume {
                    assumption: Arc::new(condition.clone()),
                    body: Arc::new(then_expr),
                });
            }
            (false, true) => {
                let else_expr = wrap_projected_facts(
                    projected_write_facts.to_owned(),
                    extract_from_block_with_context(
                        tcx,
                        body,
                        else_bb,
                        local_exprs,
                        visited,
                        ctx,
                        effects,
                    ),
                )?;
                return Some(PureExpr::LetAssume {
                    assumption: Arc::new(PureExpr::UnOp(UnOp::Not, Arc::new(condition.clone()))),
                    body: Arc::new(else_expr),
                });
            }
            (false, false) => {
                record_switch_diag(
                    ctx,
                    body,
                    bb,
                    ExtractionDiagKind::FeatureGap,
                    "cutoff-mode bool SwitchInt lost both branches before the cutoff",
                );
                return None;
            }
            (true, true) => {}
        }
    }
    let mut premise_edge = PremiseEdge::new(tcx, body, bb, targets, None, &condition);
    let then_diag_start = diag_count(ctx);
    let then_assumptions_snapshot = effects.assumptions.len();
    // Obligations discovered inside this arm are only required on this arm's
    // path, exactly as for the enum lane below. Snapshot before the walk so
    // `guard_branch_obligations` can tell them from obligations that were
    // already present.
    let then_obligations_snapshot = effects.obligations.len();
    let then_facts_snapshot = effects.returning_path_facts.len();
    let then_expr = extract_from_block_with_context(
        tcx,
        body,
        then_bb,
        local_exprs.clone(),
        visited.clone(),
        ctx,
        effects,
    );
    // Then-branch guard is `condition`; convert any `assert!(false)`-derived
    // literal-`false` assumption into an unreachability OBLIGATION (`!condition`)
    // (see `gate_constant_false_branch_assumptions`).
    // Guard BEFORE the unreachability gate, for the reason the int lane
    // documents: guard only what the arm walk discovered, never the
    // `guard ==> false` obligation the gate is about to emit — that one is
    // already stated in terms of the guard and wrapping it again would make it
    // vacuous.
    guard_bool_branch_obligations(
        tcx,
        body,
        bb,
        effects,
        then_obligations_snapshot,
        condition.clone(),
    );
    guard_branch_returning_path_facts(
        tcx,
        body,
        bb,
        effects,
        then_facts_snapshot,
        Some(condition.clone()),
    );
    let then_emitted_unreachability_obligation = gate_constant_false_branch_assumptions(
        effects,
        then_assumptions_snapshot,
        Some(&condition),
    );
    guard_branch_assumptions(
        effects,
        then_assumptions_snapshot,
        WalkedArm::Then,
        &mut premise_edge,
    );
    let then_expr = wrap_projected_facts(projected_write_facts.to_owned(), then_expr);
    let then_failed_only_due_to_cycle = failed_only_due_to_cycle(ctx, then_diag_start, &then_expr);
    let else_diag_start = diag_count(ctx);
    let else_assumptions_snapshot = effects.assumptions.len();
    let else_obligations_snapshot = effects.obligations.len();
    let else_facts_snapshot = effects.returning_path_facts.len();
    let else_expr =
        extract_from_block_with_context(tcx, body, else_bb, local_exprs, visited, ctx, effects);
    // Else-branch guard is `!condition`.
    let else_guard = PureExpr::UnOp(UnOp::Not, Arc::new(condition.clone()));
    guard_bool_branch_obligations(
        tcx,
        body,
        bb,
        effects,
        else_obligations_snapshot,
        else_guard.clone(),
    );
    guard_branch_returning_path_facts(
        tcx,
        body,
        bb,
        effects,
        else_facts_snapshot,
        Some(else_guard.clone()),
    );
    let else_emitted_unreachability_obligation = gate_constant_false_branch_assumptions(
        effects,
        else_assumptions_snapshot,
        Some(&else_guard),
    );
    guard_branch_assumptions(
        effects,
        else_assumptions_snapshot,
        WalkedArm::Else,
        &mut premise_edge,
    );
    let else_expr = wrap_projected_facts(projected_write_facts.to_owned(), else_expr);
    let else_failed_only_due_to_cycle = failed_only_due_to_cycle(ctx, else_diag_start, &else_expr);
    // Compute each DFS answer once: both arms' divergence and cutoff results
    // are consulted several times below.
    let then_diverges = block_must_diverge(body, then_bb, &mut HashSet::new());
    let else_diverges = block_must_diverge(body, else_bb, &mut HashSet::new());
    let is_cutoff = cutoff_mode(ctx);
    let then_cutoff = is_cutoff && block_reaches_cutoff(body, then_bb, ctx);
    let else_cutoff = is_cutoff && block_reaches_cutoff(body, else_bb, ctx);
    // A plain `assert!(c)` lowers to `SwitchInt(c)` whose
    // failing arm calls a panic entry point. That arm is Creusot's `Abort`: it
    // must be PROVED unreachable, so its negated guard becomes an OBLIGATION
    // (discharged under the function's preconditions) instead of an assumption
    // pushed into `effects.assumptions` (an effective precondition — which is
    // what let `#[ensures(true)] fn f(x: i32) { assert!(x > 0) }` verify).
    // Enclosing switches guard this obligation through
    // `guard_branch_obligations`.
    //
    // The asserted fact is deliberately NOT re-introduced for the continuation:
    // not as an assumption, and not as a result-position `LetAssume` either —
    // ay hoists a result-position `LetAssume` into the unconditional premise
    // set (`LetAssume { x > 0, x }` puts `x > 0` beside the negated
    // obligation `!(x > 0)` and the slice closes UNSAT), which would make this
    // obligation circular. Continuation facts that need the assertion must
    // re-derive it from the preconditions; that is a completeness cost only.
    //
    // Carve-outs that keep their existing (sound) lanes:
    // * cutoff mode (proof_assert slices) — the function-level extraction owns
    //   the obligation;
    // * an arm whose literal-`false` assumption was already converted by
    //   `gate_constant_false_branch_assumptions`;
    // * a switch on a literal constant, whose would-be assumption is the
    //   literal `false` that the ENCLOSING switch's gate turns into `!guard`.
    // User `-> !` functions are not panic entry points and keep their
    // returning-path fact (`push_returning_path_fact`).
    let then_panic_obligation = !is_cutoff
        && !then_emitted_unreachability_obligation
        && !matches!(condition, PureExpr::Bool(_))
        && block_diverges_via_panic(tcx, body, then_bb);
    let else_panic_obligation = !is_cutoff
        && !else_emitted_unreachability_obligation
        && !matches!(condition, PureExpr::Bool(_))
        && block_diverges_via_panic(tcx, body, else_bb);
    if then_panic_obligation || else_panic_obligation {
        // A condition read through memory the extractor cannot track (a write
        // through a projection, a `&mut` borrow, or a `&mut`-typed local) may
        // denote a STALE value; such an obligation fails closed as `false`.
        let stable = switch_at_block_is_value_stable(tcx, body, bb);
        if then_panic_obligation {
            effects.obligations.push(if stable {
                PureExpr::UnOp(UnOp::Not, Arc::new(condition.clone()))
            } else {
                fail_closed_marker("panic-arm-guard-unstable")
            });
        }
        if else_panic_obligation {
            effects.obligations.push(if stable {
                condition.clone()
            } else {
                fail_closed_marker("panic-arm-guard-unstable")
            });
        }
    }
    let then_emitted_unreachability_obligation =
        then_emitted_unreachability_obligation || then_panic_obligation;
    let else_emitted_unreachability_obligation =
        else_emitted_unreachability_obligation || else_panic_obligation;
    // D-142: an arm this walk just charged unreachable, or the arm a
    // value-stable literal never selects, is not taken on this walk's path
    // while the verdict holds. Only a stable discriminant proves it: over a
    // stale read the charged `!guard` is about the wrong value.
    if !is_cutoff {
        let stable = switch_at_block_is_value_stable(tcx, body, bb);
        record_switch_edge(
            body,
            bb,
            then_bb,
            stable
                && (then_emitted_unreachability_obligation
                    || matches!(condition, PureExpr::Bool(false))),
            walked.as_ref(),
        );
        record_switch_edge(
            body,
            bb,
            else_bb,
            stable
                && (else_emitted_unreachability_obligation
                    || matches!(condition, PureExpr::Bool(true))),
            walked.as_ref(),
        );
    }
    match (then_expr, else_expr) {
        (Some(then_expr), Some(else_expr)) => Some(PureExpr::Ite(
            Arc::new(condition),
            Arc::new(then_expr),
            Arc::new(else_expr),
        )),
        (Some(then_expr), None) if is_cutoff && !else_cutoff => Some(PureExpr::LetAssume {
            assumption: Arc::new(condition.clone()),
            body: Arc::new(then_expr),
        }),
        (None, Some(else_expr)) if is_cutoff && !then_cutoff => Some(PureExpr::LetAssume {
            assumption: Arc::new(PureExpr::UnOp(UnOp::Not, Arc::new(condition.clone()))),
            body: Arc::new(else_expr),
        }),
        // In cutoff mode, keep the reachable branch when the other
        // branch provably diverges (panic/abort path).
        (Some(then_expr), None) if is_cutoff && else_diverges => Some(PureExpr::LetAssume {
            assumption: Arc::new(condition.clone()),
            body: Arc::new(then_expr),
        }),
        (None, Some(else_expr)) if is_cutoff && then_diverges => Some(PureExpr::LetAssume {
            assumption: Arc::new(PureExpr::UnOp(UnOp::Not, Arc::new(condition.clone()))),
            body: Arc::new(else_expr),
        }),
        // Non-cutoff mode: when one branch provably diverges (calls a
        // `!`-returning function, panics, etc.), the function only
        // returns through the surviving branch.
        //
        // That is a RETURNING-PATH fact, not an assumption. Pushed into
        // `effects.assumptions` it would be an unguarded premise of every
        // goal, which (a) discharges the diverging arm's own call-precondition
        // obligations (`if x <= 0 { die(x) }` with `die: requires(x > 0)`), (b)
        // discharges obligations emitted BEFORE the switch (`need(b); if b {
        // spin() }` with `need: requires(!b)`;
        // `s40_prior_obligation_before_spin`), and (c) escapes an enclosing
        // arm (`if c { if b { spin() } }` proves `ensures(!b)`;
        // `s40_nested_spin_fact_escapes`). The fact premises only the
        // function's postconditions, and every enclosing arm guards it with
        // its own condition.
        //
        // EXCEPTION: when the branch diverges via a panic / `assert!(false)`
        // we already emitted an unreachability OBLIGATION. The branch is NOT
        // trusted-divergent — its unreachability must be PROVEN — so no fact.
        (Some(then_expr), None) if else_diverges => {
            if !else_emitted_unreachability_obligation {
                push_returning_path_fact(tcx, body, bb, effects, condition.clone());
            }
            Some(then_expr)
        }
        (None, Some(else_expr)) if then_diverges => {
            if !then_emitted_unreachability_obligation {
                push_returning_path_fact(
                    tcx,
                    body,
                    bb,
                    effects,
                    PureExpr::UnOp(UnOp::Not, Arc::new(condition.clone())),
                );
            }
            Some(else_expr)
        }
        // Loop-cycle recovery: when one branch returned None specifically
        // because its block walker hit a control-flow cycle (for-loop
        // back-edge), the function only returns through the surviving
        // branch. Treat cycles like divergence for result recovery. (#2116)
        (Some(then_expr), None) if else_failed_only_due_to_cycle => {
            push_returning_path_fact(tcx, body, bb, effects, condition.clone());
            Some(then_expr)
        }
        (None, Some(else_expr)) if then_failed_only_due_to_cycle => {
            push_returning_path_fact(
                tcx,
                body,
                bb,
                effects,
                PureExpr::UnOp(UnOp::Not, Arc::new(condition.clone())),
            );
            Some(else_expr)
        }
        // Both branches return None (e.g., unit-returning function with
        // one divergent branch). Record the returning-path fact so
        // `fn g(b: bool) { if b { never_returns(); } }` with `#[ensures(!b)]`
        // verifies. (#1075)
        (None, None) if then_diverges && !else_diverges => {
            if !then_emitted_unreachability_obligation {
                push_returning_path_fact(
                    tcx,
                    body,
                    bb,
                    effects,
                    PureExpr::UnOp(UnOp::Not, Arc::new(condition.clone())),
                );
            }
            None
        }
        (None, None) if else_diverges && !then_diverges => {
            if !else_emitted_unreachability_obligation {
                push_returning_path_fact(tcx, body, bb, effects, condition.clone());
            }
            None
        }
        _ => {
            record_switch_diag(
                ctx,
                body,
                bb,
                ExtractionDiagKind::FeatureGap,
                "bool SwitchInt branches could not be merged into a return expression",
            );
            None
        }
    }
}

/// Handle integer/enum `SwitchInt` in the context-aware extractor.
///
/// Translates a MIR integer or enum discriminant branch into an `ITE` chain,
/// with support for cutoff-scoped extraction and try-operator recovery (skipping
/// early-return branches from `?` desugaring).
pub(super) fn handle_int_switch_with_context<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    condition: &PureExpr,
    targets: &SwitchTargets,
    state: IntSwitchState,
    ctx: &BlockExtractionContext<'_>,
    effects: &mut CallEffects,
) -> Option<PureExpr> {
    let IntSwitchState {
        bb: switch_bb,
        discr_int_ty,
        local_exprs,
        visited,
        projected_write_facts,
    } = state;
    let walked = walked_path(body, &visited);
    // Enum-discriminant switches thread the arm's variant refinement into
    // in-arm obligations (see `guard_branch_obligations`); a plain integer
    // match guards them by the edge its premises are scoped by
    // (`guard_int_arm_obligations`).
    let guard_arm_obligations = condition_is_enum_discriminant(condition);
    if cutoff_mode(ctx) {
        let mut candidate_targets: Vec<BasicBlock> = targets
            .all_targets()
            .iter()
            .copied()
            .filter(|target| block_reaches_cutoff(body, *target, ctx))
            .collect();
        candidate_targets.sort_by_key(|target| target.as_u32());
        candidate_targets.dedup();
        if candidate_targets.len() == 1 {
            let target = candidate_targets[0];
            let branch_expr = wrap_projected_facts(
                projected_write_facts.to_owned(),
                extract_from_block_with_context(
                    tcx,
                    body,
                    target,
                    local_exprs,
                    visited,
                    ctx,
                    effects,
                ),
            )?;
            if let Some(guard) =
                switch_target_guard_assumption(condition, targets, target, discr_int_ty)
            {
                return Some(PureExpr::LetAssume {
                    assumption: Arc::new(guard),
                    body: Arc::new(branch_expr),
                });
            }
            return Some(branch_expr);
        }
    }
    let otherwise_bb = targets.otherwise();
    let mut premise_edge =
        PremiseEdge::new(tcx, body, switch_bb, targets, Some(discr_int_ty), condition);
    let otherwise_diag_start = diag_count(ctx);
    let otherwise_assumptions_snapshot = effects.assumptions.len();
    let otherwise_obligations_snapshot = effects.obligations.len();
    let otherwise_facts_snapshot = effects.returning_path_facts.len();
    let otherwise_expr = extract_from_block_with_context(
        tcx,
        body,
        otherwise_bb,
        local_exprs.clone(),
        visited.clone(),
        ctx,
        effects,
    );
    // Guard the otherwise/default arm's in-arm obligations with its edge
    // condition (the conjunction of `discriminant(self) != <value>` over the
    // explicit arms). Done *before* `gate_constant_false_branch_assumptions`, so
    // only the obligations discovered during extraction — not any unreachability
    // obligation the gate emits — are wrapped. (#match-arm-discriminant)
    if guard_arm_obligations {
        guard_branch_obligations(
            effects,
            otherwise_obligations_snapshot,
            switch_target_guard_assumption(condition, targets, otherwise_bb, discr_int_ty),
        );
    } else {
        guard_int_arm_obligations(
            effects,
            otherwise_obligations_snapshot,
            WalkedArm::Otherwise,
            &mut premise_edge,
        );
    }
    guard_branch_returning_path_facts(
        tcx,
        body,
        switch_bb,
        effects,
        otherwise_facts_snapshot,
        switch_target_guard_assumption(condition, targets, otherwise_bb, discr_int_ty),
    );
    let otherwise_emitted_unreachability_obligation = gate_constant_false_branch_assumptions(
        effects,
        otherwise_assumptions_snapshot,
        switch_target_guard_assumption(condition, targets, otherwise_bb, discr_int_ty).as_ref(),
    );
    let otherwise_emitted_unreachability_obligation = if !cutoff_mode(ctx)
        && !otherwise_emitted_unreachability_obligation
        && block_diverges_via_panic(tcx, body, otherwise_bb)
    {
        push_panic_arm_unreachability_obligation(
            effects,
            switch_at_block_is_value_stable(tcx, body, switch_bb)
                .then(|| {
                    switch_target_guard_assumption(condition, targets, otherwise_bb, discr_int_ty)
                })
                .flatten(),
        );
        true
    } else {
        otherwise_emitted_unreachability_obligation
    };
    guard_branch_assumptions(
        effects,
        otherwise_assumptions_snapshot,
        WalkedArm::Otherwise,
        &mut premise_edge,
    );
    if !cutoff_mode(ctx) {
        record_switch_edge(
            body,
            switch_bb,
            otherwise_bb,
            otherwise_emitted_unreachability_obligation
                && switch_at_block_is_value_stable(tcx, body, switch_bb),
            walked.as_ref(),
        );
    }
    let otherwise_expr = wrap_projected_facts(projected_write_facts.to_owned(), otherwise_expr);
    let otherwise_failed_only_due_to_cycle =
        failed_only_due_to_cycle(ctx, otherwise_diag_start, &otherwise_expr);
    let target_pairs: Vec<(u128, BasicBlock)> = targets.iter().collect();

    // Collect extraction results for all branches (value targets +
    // otherwise). Branches that fail extraction are recorded as None;
    // early-return branches (try-operator `?` break path) are
    // identified below and skipped instead of aborting the whole
    // extraction. The `failed_only_due_to_cycle` flag tracks whether a failed
    // branch only emitted loop-back-edge diagnostics rather than any broader
    // extraction gap. (#1266, #2116) The final `bool` records whether the
    // branch emitted an `assert!(false)` unreachability obligation, so the
    // failed-branch recovery below does not *also* assume the negated guard
    // (which would make that obligation vacuous; see
    // `gate_constant_false_branch_assumptions`).
    // Element 0 is the switch value as a `PureExpr` for valued branches (or
    // `None` for the otherwise/default arm). Using a `PureExpr` rather than an
    // `i64` lets out-of-i64-range switch values (e.g. `i128::MIN`, `u128::MAX`)
    // form exact guard equalities instead of truncating. (#negative_int_pats)
    let mut branch_results: Vec<(Option<PureExpr>, BasicBlock, Option<PureExpr>, bool, bool)> =
        Vec::new();
    branch_results.push((
        None,
        otherwise_bb,
        otherwise_expr,
        otherwise_failed_only_due_to_cycle,
        otherwise_emitted_unreachability_obligation,
    ));
    for &(value, target) in &target_pairs {
        let value_expr = switch_value_to_expr(value, discr_int_ty)?;
        let diag_start = diag_count(ctx);
        let branch_assumptions_snapshot = effects.assumptions.len();
        let branch_obligations_snapshot = effects.obligations.len();
        let branch_facts_snapshot = effects.returning_path_facts.len();
        let branch_expr = extract_from_block_with_context(
            tcx,
            body,
            target,
            local_exprs.clone(),
            visited.clone(),
            ctx,
            effects,
        );
        // Guard this arm's in-arm obligations with its edge condition
        // (`discriminant(self) == <value>`). See the otherwise arm above.
        // (#match-arm-discriminant)
        if guard_arm_obligations {
            guard_branch_obligations(
                effects,
                branch_obligations_snapshot,
                switch_target_guard_assumption(condition, targets, target, discr_int_ty),
            );
        } else {
            guard_int_arm_obligations(
                effects,
                branch_obligations_snapshot,
                WalkedArm::Value(value),
                &mut premise_edge,
            );
        }
        guard_branch_returning_path_facts(
            tcx,
            body,
            switch_bb,
            effects,
            branch_facts_snapshot,
            switch_target_guard_assumption(condition, targets, target, discr_int_ty),
        );
        let branch_emitted_unreachability_obligation = gate_constant_false_branch_assumptions(
            effects,
            branch_assumptions_snapshot,
            switch_target_guard_assumption(condition, targets, target, discr_int_ty).as_ref(),
        );
        let branch_emitted_unreachability_obligation = if !cutoff_mode(ctx)
            && !branch_emitted_unreachability_obligation
            && block_diverges_via_panic(tcx, body, target)
        {
            push_panic_arm_unreachability_obligation(
                effects,
                switch_at_block_is_value_stable(tcx, body, switch_bb)
                    .then(|| {
                        switch_target_guard_assumption(condition, targets, target, discr_int_ty)
                    })
                    .flatten(),
            );
            true
        } else {
            branch_emitted_unreachability_obligation
        };
        guard_branch_assumptions(
            effects,
            branch_assumptions_snapshot,
            WalkedArm::Value(value),
            &mut premise_edge,
        );
        if !cutoff_mode(ctx) {
            record_switch_edge(
                body,
                switch_bb,
                target,
                branch_emitted_unreachability_obligation
                    && switch_at_block_is_value_stable(tcx, body, switch_bb),
                walked.as_ref(),
            );
        }
        let branch_expr = wrap_projected_facts(projected_write_facts.to_owned(), branch_expr);
        let failed_only_due_to_cycle = failed_only_due_to_cycle(ctx, diag_start, &branch_expr);
        branch_results.push((
            Some(value_expr),
            target,
            branch_expr,
            failed_only_due_to_cycle,
            branch_emitted_unreachability_obligation,
        ));
    }

    let all_succeeded = branch_results.iter().all(|(_, _, e, _, _)| e.is_some());
    if all_succeeded {
        // Fast path: all branches extracted — build the ITE chain directly.
        let mut acc = branch_results[0].2.clone().expect("all_succeeded ⇒ Some");
        for (value_expr_opt, _, expr_opt, _, _) in branch_results.iter().skip(1).rev() {
            let value_expr = value_expr_opt
                .clone()
                .expect("valued branch always has Some(expr)");
            let cond =
                PureExpr::BinOp(Arc::new(condition.clone()), BinOp::Eq, Arc::new(value_expr));
            acc = PureExpr::Ite(
                Arc::new(cond),
                Arc::new(expr_opt.clone().expect("all_succeeded ⇒ Some")),
                Arc::new(acc),
            );
        }
        Some(acc)
    } else {
        // Some branches failed extraction. Check whether each failed
        // branch is an early-return path (e.g., try-operator `?` break
        // path that calls `FromResidual::from_residual()` then
        // returns), or a cycle (for-loop back-edge, #2116). If so, the
        // surviving branches represent the only path to the function's
        // final return expression.
        let succeeded: Vec<_> = branch_results
            .iter()
            .filter(|(_, _, e, _, _)| e.is_some())
            .collect();
        let failed_non_early_return =
            branch_results
                .iter()
                .any(|(_, bb, e, failed_only_due_to_cycle, _)| {
                    // In cutoff mode (proof_assert extraction), a failed branch
                    // that can REACH the cutoff is never recoverable by assuming
                    // its negated guard: the branch rejoins the surviving path
                    // before the assertion, so the negation is a manufactured
                    // fact. `block_must_early_return` is a gross
                    // over-approximation there — in a body whose every path ends
                    // in `Return`, ANY rejoining arm "must early return" — and
                    // asserting the negation alongside facts that force the arm
                    // (e.g. `is-Some(get_mut_ghost(..))` after an insert)
                    // collapses the base premises to UNSAT (ghost/ghost_map
                    // vacuity). Fail closed: refuse recovery instead.
                    e.is_none()
                        && !failed_only_due_to_cycle
                        && ((cutoff_mode(ctx) && block_reaches_cutoff(body, *bb, ctx))
                            || (!block_must_early_return(body, *bb, &mut HashSet::new())
                                && !block_must_diverge(body, *bb, &mut HashSet::new())))
                });

        if succeeded.is_empty() || failed_non_early_return {
            // Cannot recover: either no branch succeeded or a failed
            // branch is neither early-return nor divergent.
            return None;
        }

        // Build expression from surviving branches with LetAssume
        // constraints so the solver only considers parameter values
        // that take the non-early-return path.
        let surviving_conditions: Vec<PureExpr> = succeeded
            .iter()
            .filter_map(|(value_expr_opt, _, _, _, _)| {
                value_expr_opt
                    .clone()
                    .map(|v| PureExpr::BinOp(Arc::new(condition.clone()), BinOp::Eq, Arc::new(v)))
            })
            .collect();

        // Build the assumption: discr == v1 || discr == v2 || ...
        // If the otherwise branch survived (value_i64 == None), we
        // use the negation of all failed-branch conditions instead.
        // The otherwise arm (`v == None`) has no single switch value, so it
        // cannot join the surviving-arm disjunction below. When it failed with
        // an unreachability OBLIGATION it must still stay inside the assumed
        // set, so use the complement form: exclude only the valued arms that
        // failed WITHOUT an obligation. (Otherwise `match x { 0 =>
        // 1, _ => unreachable!() }` verifies under `LetAssume { x == 0 }`,
        // which ay hoists into the premises and uses to discharge the
        // otherwise obligation `!(x != 0)` circularly.)
        let otherwise_failed_with_obligation =
            branch_results
                .iter()
                .any(|(v, _, e, _, emitted_obligation)| {
                    v.is_none() && e.is_none() && *emitted_obligation
                });
        let assumption = if otherwise_failed_with_obligation
            || succeeded.iter().any(|(v, _, _, _, _)| v.is_none())
        {
            // Otherwise branch survived — assume discr is NOT any of
            // the failed branches' values. EXCLUDE failed branches that
            // diverged via `assert!(false)`: their unreachability is already
            // emitted as a proof OBLIGATION (`!guard`), and assuming the same
            // `!guard` here would make that obligation vacuous (re-introducing
            // the false-accept). The obligation, not an assumption, is what
            // keeps such a branch sound.
            let failed_values: Vec<PureExpr> = branch_results
                .iter()
                .filter(|(_, _, e, _, emitted_obligation)| e.is_none() && !emitted_obligation)
                .filter_map(|(v, _, _, _, _)| {
                    v.clone().map(|val| {
                        PureExpr::UnOp(
                            UnOp::Not,
                            Arc::new(PureExpr::BinOp(
                                Arc::new(condition.clone()),
                                BinOp::Eq,
                                Arc::new(val),
                            )),
                        )
                    })
                })
                .collect();
            failed_values
                .into_iter()
                .reduce(|a, b| PureExpr::BinOp(Arc::new(a), BinOp::And, Arc::new(b)))
        } else {
            // Surviving-arm disjunction. A failed arm that carries an
            // unreachability OBLIGATION (`assert!(false)` gate, or a panic
            // arm) must stay INSIDE the assumed disjunction: ay
            // hoists a result-position `LetAssume` into the unconditional
            // premise set, so assuming `discr == <surviving>` alone would imply
            // `!(discr == <obligation arm>)` and discharge that obligation
            // circularly (otherwise `match o { Some(_) => 0, None =>
            // unreachable!() }` verifies under `LetAssume { discr == 1 }`).
            // Only arms that failed WITHOUT an obligation (early return,
            // non-panic divergence) are excluded, exactly as in the
            // otherwise-survived form above.
            let obligation_arm_conditions = branch_results
                .iter()
                .filter(|(_, _, e, _, emitted_obligation)| e.is_none() && *emitted_obligation)
                .filter_map(|(v, _, _, _, _)| {
                    v.clone().map(|val| {
                        PureExpr::BinOp(Arc::new(condition.clone()), BinOp::Eq, Arc::new(val))
                    })
                });
            surviving_conditions
                .into_iter()
                .chain(obligation_arm_conditions)
                .reduce(|a, b| PureExpr::BinOp(Arc::new(a), BinOp::Or, Arc::new(b)))
        };

        // Build the ITE chain from surviving branches only.
        // Start with the otherwise branch (index 0) as the base
        // if it survived, then layer valued branches as ITE conditions.
        // This mirrors the fast path structure where branch_results[0]
        // is the otherwise/default arm.
        let mut acc: Option<PureExpr> = branch_results[0].2.clone(); // otherwise branch (may be None if it failed)
        for (value_expr_opt, _, expr_opt, _, _) in branch_results.iter().skip(1).rev() {
            if let Some(expr) = expr_opt {
                // valued branches always have Some; default defensively to 0
                let value_expr = value_expr_opt.clone().unwrap_or(PureExpr::Int(0));
                let cond =
                    PureExpr::BinOp(Arc::new(condition.clone()), BinOp::Eq, Arc::new(value_expr));
                if let Some(current_acc) = acc {
                    acc = Some(PureExpr::Ite(
                        Arc::new(cond),
                        Arc::new(expr.clone()),
                        Arc::new(current_acc),
                    ));
                } else {
                    // No base yet (otherwise failed) — first surviving
                    // valued branch becomes the base expression.
                    acc = Some(expr.clone());
                }
            }
        }

        // Cutoff mode (proof_assert slices) keeps the result-position
        // LetAssume. Otherwise the surviving-arm condition is a RETURNING-PATH
        // fact: ay hoists a result-position LetAssume into the unconditional
        // premise set, where it would discharge the failed arms' own
        // obligations (a `-> !` callee's precondition) and obligations emitted
        // before the switch. See `push_returning_path_fact`.
        match (acc, assumption) {
            (Some(body_expr), Some(assume)) if cutoff_mode(ctx) => Some(PureExpr::LetAssume {
                assumption: Arc::new(assume),
                body: Arc::new(body_expr),
            }),
            (Some(body_expr), Some(assume)) => {
                push_returning_path_fact(tcx, body, switch_bb, effects, assume);
                Some(body_expr)
            }
            (Some(body_expr), None) => Some(body_expr),
            _ => None,
        }
    }
}

#[cfg(test)]
mod gate_assumption_tests {
    use super::*;

    fn bool_var(name: &str) -> PureExpr {
        PureExpr::Var(
            name.to_string(),
            Some(trust_wp_core::formula::ExprSort::Bool),
        )
    }

    /// An arm's premises hold only where its edge does, the literal `false`
    /// its gate owes as a goal stays unscoped, and premises recorded before
    /// the arm's snapshot are not touched.
    #[test]
    fn arm_premises_are_scoped_to_the_arm_edge() {
        let mut effects = CallEffects::new();
        effects.assumptions.push(bool_var("before"));
        let snapshot = effects.assumptions.len();
        effects.assumptions.push(bool_var("post_1"));
        effects.assumptions.push(PureExpr::Bool(false));
        effects.assumptions.push(bool_var("post_2"));
        let edge = bool_var("flag");

        scope_arm_assumptions(&mut effects, snapshot, Some(&edge));

        let scoped = |post: &str| {
            PureExpr::BinOp(
                Arc::new(edge.clone()),
                BinOp::Implies,
                Arc::new(bool_var(post)),
            )
        };
        assert_eq!(
            effects.assumptions,
            vec![
                bool_var("before"),
                scoped("post_1"),
                PureExpr::Bool(false),
                scoped("post_2"),
            ]
        );
    }

    /// With no faithful edge an arm's premises are dropped, never kept
    /// unscoped; the literal `false` stays for the gate.
    #[test]
    fn arm_premises_without_an_edge_are_dropped() {
        let mut effects = CallEffects::new();
        effects.assumptions.push(bool_var("before"));
        let snapshot = effects.assumptions.len();
        effects.assumptions.push(bool_var("post_1"));
        effects.assumptions.push(PureExpr::Bool(false));
        effects.assumptions.push(bool_var("post_2"));

        scope_arm_assumptions(&mut effects, snapshot, None);

        assert_eq!(
            effects.assumptions,
            vec![bool_var("before"), PureExpr::Bool(false)]
        );
    }

    /// An integer arm's goals are owed only where its edge holds; goals
    /// recorded before the arm's snapshot are not touched, and with no
    /// faithful edge every goal stays unconditional.
    #[test]
    fn int_arm_obligations_are_owed_under_the_arm_edge() {
        let mut effects = CallEffects::new();
        effects.obligations.push(bool_var("before"));
        let snapshot = effects.obligations.len();
        effects.obligations.push(bool_var("pre_1"));
        effects.obligations.push(bool_var("pre_2"));
        let edge = bool_var("edge");

        let mut refused = effects.clone();
        guard_arm_obligations_by_edge(&mut refused, snapshot, None);
        assert_eq!(refused.obligations, effects.obligations);

        guard_arm_obligations_by_edge(&mut effects, snapshot, Some(&edge));
        let owed = |pre: &str| {
            PureExpr::BinOp(
                Arc::new(edge.clone()),
                BinOp::Implies,
                Arc::new(bool_var(pre)),
            )
        };
        assert_eq!(
            effects.obligations,
            vec![bool_var("before"), owed("pre_1"), owed("pre_2")]
        );
    }

    /// A literal `false` an integer arm owes stays the bare literal the
    /// verdict counts as a fail-closed marker or a written `requires(false)`;
    /// the arm's other goals are still owed under its edge.
    #[test]
    fn int_arm_literal_false_obligation_stays_unconditional() {
        let mut effects = CallEffects::new();
        let snapshot = effects.obligations.len();
        effects.obligations.push(bool_var("pre_1"));
        effects.obligations.push(PureExpr::Bool(false));
        let edge = bool_var("edge");

        guard_arm_obligations_by_edge(&mut effects, snapshot, Some(&edge));

        assert_eq!(
            effects.obligations,
            vec![
                PureExpr::BinOp(
                    Arc::new(edge.clone()),
                    BinOp::Implies,
                    Arc::new(bool_var("pre_1")),
                ),
                PureExpr::Bool(false),
            ]
        );
        assert_eq!(
            trust_wp_ay::fail_closed_marker_count(&effects.obligations),
            1
        );
    }

    fn int_var(name: &str) -> PureExpr {
        PureExpr::Var(
            name.to_string(),
            Some(trust_wp_core::formula::ExprSort::Int),
        )
    }

    fn discriminant_eq_zero() -> PureExpr {
        PureExpr::BinOp(
            Arc::new(int_var("discr")),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        )
    }

    #[test]
    fn literal_false_assumption_becomes_unreachability_obligation() {
        // Mirrors `peek_bit_array8`: the `None` arm's `assert!(false)` records a
        // literal `false` divergence assumption. The int-switch guard for that
        // arm is `discr == 0`, so the assertion must become an OBLIGATION to
        // prove the arm unreachable — i.e. `!(discr == 0)` — and the literal
        // `false` must be removed from the assumption context (not assumed).
        let mut effects = CallEffects::new();
        let snapshot = effects.assumptions.len();
        effects.assumptions.push(PureExpr::Bool(false));

        let guard = discriminant_eq_zero();
        let emitted = gate_constant_false_branch_assumptions(&mut effects, snapshot, Some(&guard));

        assert!(emitted, "an unreachability obligation must be reported");
        // The literal `false` is not an assumption (it neither poisons
        // the context nor is silently granted as `!guard`).
        assert!(effects.assumptions.is_empty());
        // It is a proof obligation `!guard`, discharged under the
        // function's preconditions.
        assert_eq!(effects.obligations.len(), 1);
        match &effects.obligations[0] {
            PureExpr::UnOp(UnOp::Not, inner) => assert_eq!(**inner, guard),
            other => panic!("expected `!guard` obligation, got {other:?}"),
        }
    }

    #[test]
    fn pre_snapshot_false_assumption_is_untouched() {
        // A `Bool(false)` already present before the branch extraction (e.g.
        // genuinely contradictory user preconditions) must NOT be touched —
        // only assumptions added by *this* branch are converted. This preserves
        // the vacuity guard for `#[ensures(false)]`-style contradictions.
        let mut effects = CallEffects::new();
        effects.assumptions.push(PureExpr::Bool(false));
        let snapshot = effects.assumptions.len();

        let guard = discriminant_eq_zero();
        let emitted = gate_constant_false_branch_assumptions(&mut effects, snapshot, Some(&guard));

        assert!(!emitted);
        assert_eq!(effects.assumptions, vec![PureExpr::Bool(false)]);
        assert!(effects.obligations.is_empty());
    }

    #[test]
    fn non_false_assumptions_are_preserved() {
        // Only the literal `false` divergence marker is converted; ordinary
        // surviving-path constraints (e.g. `x > 5` from `assert!(x > 5)`) keep
        // their original form as assumptions.
        let mut effects = CallEffects::new();
        let snapshot = effects.assumptions.len();
        let real = PureExpr::BinOp(
            Arc::new(int_var("x")),
            BinOp::Gt,
            Arc::new(PureExpr::Int(5)),
        );
        effects.assumptions.push(real.clone());

        let guard = discriminant_eq_zero();
        let emitted = gate_constant_false_branch_assumptions(&mut effects, snapshot, Some(&guard));

        assert!(!emitted);
        assert_eq!(effects.assumptions, vec![real]);
        assert!(effects.obligations.is_empty());
    }

    /// The then-arm fact of a literal switch is `!literal`; it must reach the
    /// literal route as the literal it denotes, and nothing else is rewritten.
    #[test]
    fn negated_literal_facts_fold_to_the_literal() {
        let not = |inner: PureExpr| PureExpr::UnOp(UnOp::Not, Arc::new(inner));
        assert_eq!(
            fold_negated_literal(not(PureExpr::Bool(true))),
            PureExpr::Bool(false)
        );
        assert_eq!(
            fold_negated_literal(not(PureExpr::Bool(false))),
            PureExpr::Bool(true)
        );
        let symbolic = not(discriminant_eq_zero());
        assert_eq!(fold_negated_literal(symbolic.clone()), symbolic);
        let double = not(not(PureExpr::Bool(true)));
        assert_eq!(fold_negated_literal(double.clone()), double);
    }

    #[test]
    fn missing_guard_is_a_noop() {
        // With no recoverable branch guard, the literal `false` is left intact
        // (sound fail-closed: it poisons the context → vacuity guard catches it).
        let mut effects = CallEffects::new();
        let snapshot = effects.assumptions.len();
        effects.assumptions.push(PureExpr::Bool(false));

        let emitted = gate_constant_false_branch_assumptions(&mut effects, snapshot, None);

        assert!(!emitted);
        assert_eq!(effects.assumptions, vec![PureExpr::Bool(false)]);
        assert!(effects.obligations.is_empty());
    }
}

#[cfg(test)]
mod guard_gate_tests {
    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn ge_zero(inner: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(inner), BinOp::Ge, Arc::new(PureExpr::Int(0)))
    }

    /// A comparison on plain locals is guarded: nothing in it can have been
    /// rewritten between the switch and the call, so `guard ==> obligation` is
    /// the weakest-precondition rule and nothing else.
    #[test]
    fn a_by_value_comparison_is_guarded() {
        assert!(guard_reads_only_immutable_locals(&ge_zero(var("n"))));
        assert!(guard_reads_only_immutable_locals(&PureExpr::BinOp(
            Arc::new(ge_zero(var("n"))),
            BinOp::And,
            Arc::new(ge_zero(var("m"))),
        )));
        assert!(guard_reads_only_immutable_locals(&PureExpr::UnOp(
            UnOp::Not,
            Arc::new(ge_zero(var("n"))),
        )));
    }

    /// A guard that reads through a reference or a projection is REFUSED.
    ///
    /// This is the false accept the gate exists for. `if s.f >= 0 { s.f = -1;
    /// callee(s.f) }` produces a guard and an obligation that are the same
    /// `PureExpr` byte for byte, because a store through a projection is not
    /// propagated into the later call-argument expression. Guarding would make
    /// it `X ==> X`, whose negation is UNSAT, and a function that genuinely
    /// calls `callee(-1)` would verify.
    #[test]
    fn a_guard_that_reads_memory_the_arm_could_rewrite_is_refused() {
        let field = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Deref(Arc::new(var("s")))],
        };
        assert!(!guard_reads_only_immutable_locals(&ge_zero(field)));
        assert!(!guard_reads_only_immutable_locals(&ge_zero(
            PureExpr::Deref(Arc::new(var("p")))
        )));
        // `^p` is the post-mutation value by definition: it never denotes what
        // the switch read.
        assert!(!guard_reads_only_immutable_locals(&ge_zero(
            PureExpr::Final(Arc::new(var("p")))
        )));
        // Refusal is contagious through the operators, so a mutable read
        // cannot be laundered by burying it in a conjunction.
        assert!(!guard_reads_only_immutable_locals(&PureExpr::BinOp(
            Arc::new(ge_zero(var("n"))),
            BinOp::And,
            Arc::new(ge_zero(PureExpr::Deref(Arc::new(var("p"))))),
        )));
    }

    /// Refusing leaves the obligation exactly as it was — unconditional.
    /// Refusal costs completeness and can never cost soundness.
    #[test]
    fn a_refused_guard_leaves_the_obligation_untouched() {
        let mut effects = CallEffects::default();
        effects.obligations.push(ge_zero(var("x")));
        let unsafe_guard = ge_zero(PureExpr::Deref(Arc::new(var("p"))));
        guard_branch_obligations(&mut effects, 0, Some(unsafe_guard));
        assert_eq!(effects.obligations, vec![ge_zero(var("x"))]);

        // ...while an accepted guard does wrap it.
        let mut effects = CallEffects::default();
        effects.obligations.push(ge_zero(var("x")));
        guard_branch_obligations(&mut effects, 0, Some(ge_zero(var("n"))));
        assert!(matches!(
            effects.obligations.first(),
            Some(PureExpr::BinOp(_, BinOp::Implies, _))
        ));
    }

    /// A guard that reads through a dereference wraps the arm's obligations
    /// only when the switch operand reads frozen memory (D-118): the caller
    /// proves that from the MIR, and without it the guard is refused exactly
    /// as before.
    #[test]
    fn a_frozen_memory_guard_through_a_dereference_wraps() {
        let deref_guard = ge_zero(PureExpr::Deref(Arc::new(var("p"))));
        let mut effects = CallEffects::default();
        effects.obligations.push(ge_zero(var("x")));
        guard_branch_obligations_if(&mut effects, 0, Some(deref_guard.clone()), false);
        assert_eq!(effects.obligations, vec![ge_zero(var("x"))]);

        let mut effects = CallEffects::default();
        effects.obligations.push(ge_zero(var("x")));
        guard_branch_obligations_if(&mut effects, 0, Some(deref_guard), true);
        assert!(matches!(
            effects.obligations.first(),
            Some(PureExpr::BinOp(_, BinOp::Implies, _))
        ));
    }

    /// Only obligations discovered since the snapshot are guarded: an
    /// obligation from an enclosing scope is not this arm's to weaken.
    #[test]
    fn obligations_older_than_the_snapshot_are_left_alone() {
        let mut effects = CallEffects::default();
        effects.obligations.push(ge_zero(var("outer")));
        let snapshot = effects.obligations.len();
        effects.obligations.push(ge_zero(var("inner")));
        guard_branch_obligations(&mut effects, snapshot, Some(ge_zero(var("n"))));
        assert_eq!(effects.obligations[0], ge_zero(var("outer")));
        assert!(matches!(
            effects.obligations[1],
            PureExpr::BinOp(_, BinOp::Implies, _)
        ));
    }
}
