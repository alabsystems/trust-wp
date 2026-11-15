// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop body effect extraction via symbolic execution (#1669).
//!
//! Walks the loop body in execution order, tracking symbolic expressions for each
//! MIR local. For each modified named variable, records the update expression (e.g.,
//! `i' = i + 1`). Handles internal branching via ITE merge, nested loop skip, and
//! call-site spec modeling.

mod branch_merge;
mod call_modeling;
mod inner_loops;

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use call_modeling::CallPremise;
use rustc_middle::{
    mir::{
        BasicBlock, Body, CastKind, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{Ty, TyKind},
};
use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_field_logic_fn_name, PureExpr, INDEX_MUT_OPAQUE_VALUE,
};

use super::{
    super::translate::{translate_rvalue, translate_rvalue_typed},
    condition::base_var_name,
    CallSpecContext,
};

/// Body effects extraction result: direct effects, deref effects, and double-deref effects.
pub(super) struct BodyEffects {
    /// Direct variable effects: `var = expr`.
    pub(super) effects: HashMap<String, PureExpr>,
    /// Deref variable effects: `*var = expr`. Maps variable name to the value
    /// written through its dereference. (#1295)
    pub(super) deref_effects: HashMap<String, PureExpr>,
    /// Double-deref variable effects: `**var = expr`. Maps variable name to the
    /// value written through a double dereference. For `**x = 0` where
    /// `x: &mut &mut i32`, constrains `x_prime_current_current = 0` during
    /// preservation. (#1295)
    pub(super) double_deref_effects: HashMap<String, PureExpr>,
    /// Callee postconditions stated at the calls' results, each guarded by the
    /// path condition reaching its call and the callee's own premises.
    pub(super) call_facts: Vec<PureExpr>,
    /// Premises the program supplies that the walk could not state.
    pub(super) dropped_premises: Vec<DroppedPremise>,
}

/// A premise some path through the loop body supplies that the loop VC does
/// not state. A model of that VC may violate it, so a model is not a
/// counterexample to the program while one of these stands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DroppedPremise {
    /// The block whose semantics were left out.
    pub(crate) block: BasicBlock,
    /// What was left out, as the withheld verdict's reason.
    pub(crate) what: String,
    /// The premise is an `Iterator::next` step, which a for-loop's own
    /// structural facts state instead of the call's contract.
    pub(crate) iterator_step: bool,
    /// The premise speaks only of this variable's post-iteration value; `None`
    /// when it may constrain any value.
    pub(crate) only_about: Option<String>,
}

pub(super) fn extract_body_effects<'a, 'tcx: 'a>(
    body: &'a Body<'tcx>,
    body_blocks: &'a HashSet<BasicBlock>,
    header: BasicBlock,
    local_exprs: &HashMap<Local, PureExpr>,
    local_to_name: &'a HashMap<Local, String>,
    inner_loops: Vec<(BasicBlock, HashSet<BasicBlock>)>,
    call_spec_ctx: Option<CallSpecContext<'a, 'tcx>>,
) -> BodyEffects {
    let initial_state = BodyExtractionState {
        working_exprs: local_exprs.clone(),
        effects: HashMap::new(),
        deref_effects: HashMap::new(),
        double_deref_effects: HashMap::new(),
        pending_index_mut: HashMap::new(),
        // Carry the length frame for an indexed write whose value is un-modeled
        // (e.g. `v[i] = !v[i]`), so a single loop's own `v@.len() == K` invariant
        // is preserved. The `set` records an opaque value; loop preservation
        // (`extend_point_write_facts_for_receiver`) suppresses the element-content
        // fact for the opaque marker, so only the sound length / off-index frame
        // is asserted. (gap nested-loop-outer-element-and-indexed-write-frame)
        index_mut_length_only_on_value_failure: true,
        path_guard: Vec::new(),
        path_guard_opaque: false,
        call_facts: Vec::new(),
        dropped_premises: Vec::new(),
    };
    let lent_body_locals = lent_body_locals(body, body_blocks, call_spec_ctx.map(|ctx| ctx.tcx));
    let ctx = BodyExtractionCtx {
        body,
        body_blocks,
        header,
        local_to_name,
        inner_loops,
        call_spec_ctx,
        lent_body_locals,
    };
    let result = ctx.extract_from_block(header, false, initial_state, HashSet::new());
    result.map_or_else(
        || BodyEffects {
            effects: HashMap::new(),
            deref_effects: HashMap::new(),
            double_deref_effects: HashMap::new(),
            call_facts: Vec::new(),
            // Every modified variable is havoced, and whatever the body
            // established about any other value is gone with it.
            dropped_premises: vec![DroppedPremise {
                block: header,
                what: "the loop body walk does not reach the back edge on every path".to_string(),
                iterator_step: false,
                only_about: None,
            }],
        },
        |state| BodyEffects {
            effects: state.effects,
            deref_effects: state.deref_effects,
            double_deref_effects: state.double_deref_effects,
            call_facts: state.call_facts,
            dropped_premises: state.dropped_premises,
        },
    )
}

/// The value a loop condition reads from the call that computes it on the
/// header path, with the premises the callee's contract supplies about it.
pub(super) struct ConditionCallValue {
    /// The destination's value: the modeled `result == e`, or the symbol
    /// naming the value this evaluation returns. `None` when it has neither.
    pub(super) value: Option<PureExpr>,
    /// The postcondition clauses stated at `value`, under the callee's own
    /// premises at its arguments.
    pub(super) facts: Vec<PureExpr>,
    /// What the contract supplies that no premise states.
    pub(super) dropped: Vec<DroppedPremise>,
}

/// State the call that ends block `bb` the way the body walk states it, for
/// the loop condition that reads its result.
///
/// The body walk passes the same call on its way from the header, so the
/// condition and the walk's premises name the same value
/// (loop_condition_call_postcondition_control). `None` when `bb` does not end
/// in a call.
pub(super) fn condition_call_value<'a, 'tcx: 'a>(
    body: &'a Body<'tcx>,
    body_blocks: &'a HashSet<BasicBlock>,
    header: BasicBlock,
    local_to_name: &'a HashMap<Local, String>,
    call_spec_ctx: CallSpecContext<'a, 'tcx>,
    bb: BasicBlock,
    working_exprs: &HashMap<Local, PureExpr>,
) -> Option<ConditionCallValue> {
    let TerminatorKind::Call {
        func,
        args,
        destination,
        ..
    } = &body.basic_blocks[bb].terminator().kind
    else {
        return None;
    };
    // The body walk's own lent set, so the call is stated in its environment.
    let lent_body_locals = lent_body_locals(body, body_blocks, Some(call_spec_ctx.tcx));
    let ctx = BodyExtractionCtx {
        body,
        body_blocks,
        header,
        local_to_name,
        inner_loops: Vec::new(),
        call_spec_ctx: Some(call_spec_ctx),
        lent_body_locals,
    };
    let mut state = BodyExtractionState {
        working_exprs: working_exprs.clone(),
        effects: HashMap::new(),
        deref_effects: HashMap::new(),
        double_deref_effects: HashMap::new(),
        pending_index_mut: HashMap::new(),
        index_mut_length_only_on_value_failure: false,
        path_guard: Vec::new(),
        path_guard_opaque: false,
        call_facts: Vec::new(),
        dropped_premises: Vec::new(),
    };
    ctx.apply_call_terminator(bb, func, args, destination, &mut state);
    ctx.forget_body_locals_written_at_terminator(bb, &mut state);
    Some(ConditionCallValue {
        value: destination
            .projection
            .is_empty()
            .then(|| state.working_exprs.get(&destination.local).cloned())
            .flatten(),
        facts: state.call_facts,
        dropped: state.dropped_premises,
    })
}

#[derive(Clone)]
pub(super) struct BodyExtractionState {
    pub(super) working_exprs: HashMap<Local, PureExpr>,
    pub(super) effects: HashMap<String, PureExpr>,
    /// Deref effects: maps variable name to the value written through its dereference.
    pub(super) deref_effects: HashMap<String, PureExpr>,
    /// Double-deref effects: maps variable name to the value written through
    /// a double dereference (`**var = expr`). (#1295)
    pub(super) double_deref_effects: HashMap<String, PureExpr>,
    /// Pending `IndexMut::index_mut` call results awaiting `*result = value`.
    pub(super) pending_index_mut: HashMap<Local, PendingIndexMutWrite>,
    /// When set, an `IndexMut` deref-write whose value cannot be translated still
    /// records a LENGTH-ONLY `set` deref effect with an opaque placeholder value
    /// (the length of `Seq::set` is value-invariant). This lets both the main walk
    /// AND the nested-loop inner-walk scratch state summarize a `v[i] = <expr>` write
    /// as the collection's length frame even when the written value is itself an
    /// un-modeled indexed read (e.g. `door_open[i] = !door_open[i]`). Soundness rests
    /// entirely on loop preservation suppressing the element-content fact for the
    /// opaque marker (`extend_point_write_facts_for_receiver` /
    /// `is_index_mut_opaque_value`): only the length and off-index frame facts are
    /// asserted, never `index_logic(updated, i) == <opaque>`.
    /// (gap nested-loop-outer-element-and-indexed-write-frame)
    pub(super) index_mut_length_only_on_value_failure: bool,
    /// Branch conditions taken on the path from the header to this point.
    pub(super) path_guard: Vec<PureExpr>,
    /// The path took a branch whose condition does not translate, so no fact
    /// recorded on it could be guarded.
    pub(super) path_guard_opaque: bool,
    /// See [`BodyEffects::call_facts`].
    pub(super) call_facts: Vec<PureExpr>,
    /// See [`BodyEffects::dropped_premises`].
    pub(super) dropped_premises: Vec<DroppedPremise>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct PendingIndexMutWrite {
    pub(super) param_name: String,
    pub(super) index: PureExpr,
}

/// Classification of a defining assignment during the cons-tail reborrow def-use
/// walk (`try_model_cons_tail_reassignment`). Either the root cons-tail-box
/// reference, or a value-preserving forward step to a source local.
enum CtRef {
    /// `&[mut] (((*scrutinee) as VARIANT).FIELD)` — the cons-tail box reference.
    DowncastFieldRef {
        scrutinee: Local,
        variant: rustc_abi::VariantIdx,
        field_idx: usize,
    },
    /// A value-preserving reshaping (`copy`, reborrow, pointer cast) of another
    /// local; continue tracing from it.
    Forward(Local),
}

pub(super) struct BodyExtractionCtx<'a, 'tcx> {
    pub(super) body: &'a Body<'tcx>,
    pub(super) body_blocks: &'a HashSet<BasicBlock>,
    pub(super) header: BasicBlock,
    pub(super) local_to_name: &'a HashMap<Local, String>,
    /// Inner (nested) loops within this loop's body.
    pub(super) inner_loops: Vec<(BasicBlock, HashSet<BasicBlock>)>,
    /// Optional spec context for modeling call results. (#1463)
    pub(super) call_spec_ctx: Option<CallSpecContext<'a, 'tcx>>,
    /// Locals declared in this loop's body, and those of them whose own
    /// memory the body lends out ([`lent_body_locals`]): a value bound to one
    /// is forgotten wherever it may be written behind the walk.
    pub(super) lent_body_locals: LentBodyLocals,
}

/// Locals declared inside a loop body (their `StorageLive` is in it): all of
/// them, and those whose own memory the body lends out.
#[derive(Default)]
pub(super) struct LentBodyLocals {
    born: HashSet<Local>,
    lent: HashSet<Local>,
}

/// The locals DECLARED inside a loop body (their `StorageLive` is in it), and
/// those of them whose own memory the body borrows `&mut` or raw (not a
/// reborrow through a `Deref`), or borrows shared while their type is not
/// `Freeze`.
///
/// The walk binds a local at its projection-free assignments. Through such a
/// loan the local also changes at a `Drop` whose glue writes it
/// (`{ let _g = G(&mut m); }`, D-140), inside a callee handed the loan
/// (`set5(&mut m)`), and at a store through a reference; a loop-carried local
/// copied from it before the back edge (`n = m`) would carry the value from
/// before (loop_body_local_drop_glue_write_unseen_by_invariant.rs,
/// loop_body_local_written_by_callee_unseen.rs,
/// loop_variant_reads_body_local_before_drop_glue_write.rs). Forgetting a
/// body-local makes a later read its name, a symbol nothing constrains. A
/// loop-carried local's name is its value at the header, so forgetting it
/// would read a stale value instead; `WriteSites` havocs those. Without a
/// `tcx` the interior-mutability clause is not asked.
fn lent_body_locals<'tcx>(
    body: &Body<'tcx>,
    body_blocks: &HashSet<BasicBlock>,
    tcx: Option<rustc_middle::ty::TyCtxt<'tcx>>,
) -> LentBodyLocals {
    use rustc_middle::mir::{BorrowKind, RawPtrKind};
    let mut born = HashSet::new();
    let mut lent = HashSet::new();
    for bb in body_blocks {
        for stmt in &body.basic_blocks[*bb].statements {
            match &stmt.kind {
                StatementKind::StorageLive(local) => {
                    born.insert(*local);
                }
                StatementKind::Assign((_, rvalue)) => {
                    let (place, may_write) = match rvalue {
                        Rvalue::Ref(_, kind, place) => {
                            (place, matches!(kind, BorrowKind::Mut { .. }))
                        }
                        Rvalue::RawPtr(kind, place) => (place, !matches!(kind, RawPtrKind::Const)),
                        _ => continue,
                    };
                    if place.is_indirect() {
                        continue;
                    }
                    let interior = !may_write
                        && tcx.is_some_and(|tcx| {
                            let ty = body.local_decls[place.local].ty;
                            !ty.is_freeze(tcx, body.typing_env(tcx))
                        });
                    if may_write || interior {
                        lent.insert(place.local);
                    }
                }
                _ => {}
            }
        }
    }
    lent.retain(|local| born.contains(local));
    LentBodyLocals { born, lent }
}

impl<'a, 'tcx> BodyExtractionCtx<'a, 'tcx> {
    pub(super) fn extract_from_block(
        &self,
        bb: BasicBlock,
        entered_header: bool,
        mut state: BodyExtractionState,
        mut visited: HashSet<BasicBlock>,
    ) -> Option<BodyExtractionState> {
        let mut entered_header = entered_header;
        if bb == self.header {
            // Re-entering header means we've reached the one-iteration back-edge.
            if entered_header {
                return Some(state);
            }
            entered_header = true;
        } else if !self.body_blocks.contains(&bb) {
            // Exiting the loop body before the back-edge (`break`, early return)
            // is unsupported for body-effect extraction; force fallback havoc.
            return None;
        }

        // Check if this block is an inner loop header. If so, skip the entire
        // inner loop body and continue from the exit target. (#1295)
        if let Some(exit_target) = self.find_inner_loop_exit(bb, &mut state, &mut visited) {
            return self.extract_from_block(exit_target, entered_header, state, visited);
        }

        if !visited.insert(bb) {
            return None;
        }

        self.apply_assignments(bb, &mut state);

        let terminator = &self.body.basic_blocks[bb].terminator().kind;
        match terminator {
            TerminatorKind::Goto { target, .. }
            | TerminatorKind::Assert { target, .. }
            | TerminatorKind::Drop { target, .. } => {
                self.extract_from_block(*target, entered_header, state, visited)
            }
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => {
                self.extract_from_block(*real_target, entered_header, state, visited)
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                self.extract_switch(bb, entered_header, state, visited, discr, targets)
            }
            TerminatorKind::Call {
                target: Some(target),
                ..
            } => self.extract_from_block(*target, entered_header, state, visited),
            // Unsupported or diverging control flow keeps extraction conservative.
            _ => None,
        }
    }

    /// For unnamed temporaries assigned from a deref of a named variable,
    /// wrap the expression in `Deref()` to preserve dereference structure.
    /// This enables double-deref detection. (#1295)
    fn deref_wrap_working_expr(
        &self,
        local: Local,
        rvalue: &Rvalue<'tcx>,
        expr: &PureExpr,
    ) -> PureExpr {
        if self.local_to_name.contains_key(&local) {
            return expr.clone();
        }
        if let Rvalue::Use(Operand::Copy(source) | Operand::Move(source), _) = rvalue {
            if source.projection.len() == 1
                && matches!(source.projection.first(), Some(ProjectionElem::Deref))
                && self.local_to_name.contains_key(&source.local)
            {
                if matches!(expr, PureExpr::Deref(_)) {
                    return expr.clone();
                }
                return PureExpr::Deref(Arc::new(expr.clone()));
            }
        }
        expr.clone()
    }

    fn translate_rvalue_for_effect(
        &self,
        rvalue: &Rvalue<'tcx>,
        state: &BodyExtractionState,
    ) -> Option<PureExpr> {
        self.call_spec_ctx
            .and_then(|ctx| {
                translate_rvalue_typed(ctx.tcx, rvalue, &state.working_exprs, Some(self.body))
            })
            .or_else(|| self.translate_box_raw_pointer_cast(rvalue, state))
            .or_else(|| translate_rvalue(rvalue, &state.working_exprs, Some(self.body)))
            .or_else(|| self.named_local_copy_from_rvalue(rvalue))
    }

    fn translate_box_raw_pointer_cast(
        &self,
        rvalue: &Rvalue<'tcx>,
        state: &BodyExtractionState,
    ) -> Option<PureExpr> {
        // The box-deref elaboration's cast is `BoxDerefTransmute`, a transmute
        // whose input is a valid `Box` pointer.
        let Rvalue::Cast(CastKind::Transmute | CastKind::BoxDerefTransmute, operand, target_ty) =
            rvalue
        else {
            return None;
        };
        if !matches!(target_ty.kind(), TyKind::RawPtr(..)) {
            return None;
        }
        let (Operand::Copy(source) | Operand::Move(source)) = operand else {
            return None;
        };
        if source.projection.is_empty()
            || !source
                .projection
                .iter()
                .all(|proj| matches!(proj, ProjectionElem::Field(_, _)))
        {
            return None;
        }
        let source_ty = self.body.local_decls[source.local].ty.peel_refs();
        if !matches!(source_ty.kind(), TyKind::Adt(adt_def, _) if adt_def.is_box()) {
            return None;
        }
        let box_expr = state.working_exprs.get(&source.local)?.clone();
        Some(PureExpr::Deref(Arc::new(box_expr)))
    }

    fn current_named_expr(&self, state: &BodyExtractionState, name: &str) -> PureExpr {
        state
            .effects
            .get(name)
            .cloned()
            .or_else(|| {
                self.local_to_name.iter().find_map(|(local, local_name)| {
                    (local_name == name)
                        .then(|| state.working_exprs.get(local).cloned())
                        .flatten()
                })
            })
            .unwrap_or_else(|| PureExpr::Var(name.to_string(), None))
    }

    fn specialize_expr_for_branch(
        expr: &PureExpr,
        cond: &PureExpr,
        take_then_branch: bool,
    ) -> PureExpr {
        expr.rewrite_bottom_up(|node| match node {
            PureExpr::Ite(inner_cond, then_expr, else_expr) if inner_cond.as_ref() == cond => {
                if take_then_branch {
                    then_expr.as_ref().clone()
                } else {
                    else_expr.as_ref().clone()
                }
            }
            other => other,
        })
    }

    /// Split a deref write through an ITE alias into conditional direct effects. (#2366)
    ///
    /// When `working_expr = ITE(cond, Var(a), Var(b))`, writing `*local = expr`
    /// produces: `a' = ITE(cond, expr, a_current)`, `b' = ITE(cond, b_current, expr)`.
    #[allow(clippy::needless_pass_by_value)] // PureExpr by-value matches other effect methods
    fn apply_ite_alias_split(
        &self,
        state: &mut BodyExtractionState,
        cond: &PureExpr,
        then_name: &str,
        else_name: &str,
        expr: PureExpr,
    ) {
        let then_current = self.current_named_expr(state, then_name);
        let else_current = self.current_named_expr(state, else_name);
        let then_expr = Self::specialize_expr_for_branch(&expr, cond, true);
        let else_expr = Self::specialize_expr_for_branch(&expr, cond, false);
        state.effects.insert(
            then_name.to_string(),
            PureExpr::Ite(
                Arc::new(cond.clone()),
                Arc::new(then_expr),
                Arc::new(then_current),
            ),
        );
        state.effects.insert(
            else_name.to_string(),
            PureExpr::Ite(
                Arc::new(cond.clone()),
                Arc::new(else_current),
                Arc::new(else_expr),
            ),
        );
    }

    /// Process deref and double-deref assignments. (#1295)
    fn apply_deref_assignment(
        &self,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        state: &mut BodyExtractionState,
    ) {
        if place.projection.len() == 1
            && matches!(place.projection.first(), Some(ProjectionElem::Deref))
        {
            if let Some(pending) = state.pending_index_mut.remove(&place.local) {
                if let Some(value) = self.translate_rvalue_for_effect(rvalue, state) {
                    apply_indexed_write_effect(state, &pending.param_name, pending.index, value);
                } else if state.index_mut_length_only_on_value_failure {
                    // The written value cannot be translated (e.g. it is itself an
                    // un-modeled indexed read, `v[i] = !v[i]`). For the LENGTH frame
                    // the value is irrelevant — `len(set(s, i, _)) == len(s)` — so
                    // record an opaque-value `set` purely to carry length preservation.
                    // Loop preservation suppresses the element-content fact for the
                    // opaque marker, so element content is never faked.
                    apply_indexed_write_effect(
                        state,
                        &pending.param_name,
                        pending.index,
                        PureExpr::Var(INDEX_MUT_OPAQUE_VALUE.to_string(), None),
                    );
                }
                return;
            }
        }

        if place.projection.len() == 1
            && matches!(place.projection.first(), Some(ProjectionElem::Deref))
        {
            if let Some(var_name) = self.local_to_name.get(&place.local) {
                // Check if the named variable holds an ITE alias — if so, split the
                // deref write into conditional direct effects on the underlying targets
                // in ADDITION to recording the deref effect on the named alias. (#2366)
                let ite_alias = state.working_exprs.get(&place.local).and_then(|we| {
                    if let PureExpr::Ite(c, t, e) = we {
                        if let (PureExpr::Var(tn, _), PureExpr::Var(en, _)) =
                            (t.as_ref(), e.as_ref())
                        {
                            return Some((c.clone(), tn.clone(), en.clone()));
                        }
                    }
                    None
                });
                if let Some(expr) = self.translate_rvalue_for_effect(rvalue, state) {
                    state.deref_effects.insert(var_name.clone(), expr.clone());
                    if let Some((cond, tn, en)) = ite_alias {
                        self.apply_ite_alias_split(state, &cond, &tn, &en, expr);
                    }
                } else {
                    state.deref_effects.remove(var_name);
                }
            } else if let Some(working_expr) = state.working_exprs.get(&place.local).cloned() {
                match &working_expr {
                    PureExpr::Deref(inner) => {
                        if let PureExpr::Var(ref base_name, _) = **inner {
                            if let Some(expr) = self.translate_rvalue_for_effect(rvalue, state) {
                                state.double_deref_effects.insert(base_name.clone(), expr);
                            }
                        }
                    }
                    PureExpr::Var(ref base_name, _) => {
                        // Deref through copied parameter: `_tmp = x; *_tmp = 0` (#2085).
                        if let Some(expr) = self.translate_rvalue_for_effect(rvalue, state) {
                            state.deref_effects.insert(base_name.clone(), expr);
                        }
                    }
                    PureExpr::Ite(cond, then_alias, else_alias) => {
                        // Conditional alias split: `*ITE(cond, a, b) = expr` (#2366).
                        if let (PureExpr::Var(tn, _), PureExpr::Var(en, _)) =
                            (then_alias.as_ref(), else_alias.as_ref())
                        {
                            if let Some(expr) = self.translate_rvalue_for_effect(rvalue, state) {
                                self.apply_ite_alias_split(state, cond, tn, en, expr);
                            }
                        }
                    }
                    _ => {}
                }
            }
        } else if place.projection.len() == 2
            && matches!(
                (place.projection.first(), place.projection.get(1)),
                (Some(ProjectionElem::Deref), Some(ProjectionElem::Deref))
            )
        {
            // Direct double-deref: `(*(*local)) = rvalue` (#1295)
            if let Some(var_name) = self.local_to_name.get(&place.local) {
                if let Some(expr) = self.translate_rvalue_for_effect(rvalue, state) {
                    state.double_deref_effects.insert(var_name.clone(), expr);
                }
            }
        }
    }

    /// Model a by-value struct FIELD write `x.i = rvalue` as a functional
    /// struct update (#2702).
    ///
    /// For a by-value struct local `x` (no leading `Deref`) with a single
    /// `Field(i)` projection, MIR emits `Assign(x.i, rvalue)`. Without an
    /// effect, the post-iteration value of `x` is havoced in
    /// `build_prime_substitutions`, so every loop VC that mentions `x` (or its
    /// other fields) fails spuriously: the primed `x_prime` is unconstrained.
    ///
    /// We record `effects[x] = StructName(f_0, ..., f_{n-1})` where the written
    /// field slot `i` holds the new value and every sibling slot `j != i` holds
    /// the field's *prior* value — taken from the in-progress effect on `x`
    /// (so chained field writes in one iteration compose) or, for slots not yet
    /// written, the field accessor `__trust_wp_tuple_get_j(x)` on the original
    /// loop-entry value. The encoder lowers `StructName(...)` to the datatype
    /// constructor, so `customvariant_j(x_prime)` reduces to the recorded slot
    /// by the SMT theory of datatypes.
    ///
    /// SOUNDNESS: this only constrains `x_prime` to its *actual* post-body
    /// value. Untouched siblings are carried forward verbatim, and the written
    /// slot uses the already-resolved rvalue translation (the same expression an
    /// invariant read of `x.i` would produce). It adds exactly the true body
    /// transition for `x`; it cannot turn an otherwise-SAT (free) goal UNSAT.
    /// If the field value cannot be translated, or the struct shape cannot be
    /// recovered, we leave `x` havoced (no effect) — never a fabricated value.
    fn apply_struct_field_assignment(
        &self,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        state: &mut BodyExtractionState,
    ) -> bool {
        // Single `Field(i)` projection on a by-value struct local (no Deref).
        if place.projection.len() != 1 {
            return false;
        }
        let Some(ProjectionElem::Field(field, _)) = place.projection.first() else {
            return false;
        };
        let field_idx = field.as_u32() as usize;
        let Some(var_name) = self.local_to_name.get(&place.local).cloned() else {
            return false;
        };
        // Recover the struct name and field count from the local's type. Only a
        // single-variant struct ADT (tuple or record) is modeled here; enums and
        // non-ADT types are left havoced.
        let Some(ctx) = self.call_spec_ctx else {
            return false;
        };
        let local_ty = self.body.local_decls[place.local].ty;
        let TyKind::Adt(adt_def, _) = local_ty.kind() else {
            return false;
        };
        if !adt_def.is_struct() {
            return false;
        }
        let field_count = adt_def.non_enum_variant().fields.len();
        if field_idx >= field_count || field_count == 0 {
            return false;
        }
        // Translate the written value. Bail (leave havoced) if it cannot be
        // modeled rather than substitute a placeholder.
        let Some(written) = self.translate_rvalue_for_effect(rvalue, state) else {
            return false;
        };
        let struct_name = ctx.tcx.item_name(adt_def.did()).to_string();
        // Base value of `x` for sibling fields: the in-progress effect (to
        // compose multiple field writes in one iteration) or the original
        // loop-entry `x`.
        let base_var = state
            .effects
            .get(&var_name)
            .cloned()
            .unwrap_or_else(|| self.field_write_base_var(place.local, &var_name));
        let args = (0..field_count)
            .map(|j| {
                if j == field_idx {
                    written.clone()
                } else {
                    PureExpr::LogicFnCall {
                        name: tuple_field_logic_fn_name(j),
                        args: vec![base_var.clone()],
                    }
                }
            })
            .collect();
        // SOUNDNESS GUARD for chained dependent field writes. The written value
        // was translated against `working_exprs[local]`, which field writes do
        // NOT update — so a read of a SIBLING field already written earlier in
        // this iteration (e.g. `x.1 = x.0` after `x.0 -= 1`) would resolve to the
        // STALE loop-entry value, producing a wrong post-body struct. Detect that
        // case: if the written value reads a sibling field `tuple_get_j(x)`
        // (j != i) of this same local AND that sibling was already updated this
        // iteration (present in the in-progress effect), bail to a conservative
        // havoc rather than emit a possibly-incorrect effect. The common
        // independent pattern (`x.0 -= 1; x.1 -= 1`, each field reading only its
        // own value) is unaffected.
        if let Some(PureExpr::LogicFnCall {
            name: in_progress_ctor,
            ..
        }) = state.effects.get(&var_name)
        {
            if *in_progress_ctor == struct_name
                && written_reads_other_updated_field(&written, &var_name, field_idx)
            {
                state.effects.remove(&var_name);
                state.working_exprs.remove(&place.local);
                return true;
            }
        }
        let updated = PureExpr::LogicFnCall {
            name: struct_name,
            args,
        };
        state.effects.insert(var_name, updated);
        true
    }

    /// Original loop-entry value expression for a named struct local, used as
    /// the base for sibling fields in a struct field-write update.
    fn field_write_base_var(&self, local: Local, var_name: &str) -> PureExpr {
        self.named_local_expr(local)
            .unwrap_or_else(|| PureExpr::Var(var_name.to_string(), None))
    }

    fn apply_indexed_place_assignment(
        &self,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        state: &mut BodyExtractionState,
    ) -> bool {
        if place.projection.len() != 2 {
            return false;
        }
        let (Some(ProjectionElem::Deref), Some(ProjectionElem::Index(index_local))) =
            (place.projection.first(), place.projection.get(1))
        else {
            return false;
        };

        let param_name = self.local_to_name.get(&place.local).cloned().or_else(|| {
            state
                .working_exprs
                .get(&place.local)
                .and_then(base_var_name)
                .map(str::to_string)
        });
        let Some(param_name) = param_name else {
            return false;
        };
        let Some(value) = self.translate_rvalue_for_effect(rvalue, state) else {
            return false;
        };
        let index = state
            .working_exprs
            .get(index_local)
            .cloned()
            .or_else(|| self.named_local_expr(*index_local))
            .unwrap_or_else(|| PureExpr::Var(format!("$_{}", index_local.as_u32()), None));
        apply_indexed_write_effect(state, &param_name, index, value);
        true
    }

    fn record_pending_index_mut(
        &self,
        func: &Operand<'tcx>,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        state: &mut BodyExtractionState,
    ) -> bool {
        if !self.is_index_mut_call(func) || args.len() < 2 {
            return false;
        }
        let Some(receiver) =
            super::super::translate::translate_operand(&args[0].node, &state.working_exprs)
        else {
            return false;
        };
        let Some(param_name) = base_var_name(&receiver).map(str::to_string) else {
            return false;
        };
        let Some(index) =
            self.translate_operand_or_named_local(&args[1].node, &state.working_exprs)
        else {
            return false;
        };
        state.pending_index_mut.insert(
            destination.local,
            PendingIndexMutWrite { param_name, index },
        );
        true
    }

    fn translate_operand_or_named_local(
        &self,
        operand: &Operand<'tcx>,
        working_exprs: &HashMap<Local, PureExpr>,
    ) -> Option<PureExpr> {
        super::super::translate::translate_operand(operand, working_exprs).or_else(|| {
            let place = match operand {
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => place,
                Operand::Constant(_)
                | Operand::Copy(_)
                | Operand::Move(_)
                | Operand::RuntimeChecks(_) => return None,
            };
            self.named_local_expr(place.local)
        })
    }

    fn pending_index_mut_alias_from_rvalue(
        rvalue: &Rvalue<'tcx>,
        state: &BodyExtractionState,
    ) -> Option<PendingIndexMutWrite> {
        let Rvalue::Use(Operand::Copy(source) | Operand::Move(source), _) = rvalue else {
            return None;
        };
        if !source.projection.is_empty() {
            return None;
        }
        state.pending_index_mut.get(&source.local).cloned()
    }

    fn named_local_copy_from_rvalue(&self, rvalue: &Rvalue<'tcx>) -> Option<PureExpr> {
        let Rvalue::Use(Operand::Copy(source) | Operand::Move(source), _) = rvalue else {
            return None;
        };
        if !source.projection.is_empty() {
            return None;
        }
        self.named_local_expr(source.local)
    }

    /// Build the collection view `View(Var(name, sort))` for a loop-visible
    /// base variable, carrying the enriched sort of its named local so the
    /// encoder's `MutRef -> Deref` view redirect resolves the right
    /// (`_view` vs `_current_view`) term. Returns `None` when no local carries
    /// this name (e.g. the receiver is a temporary derived expression).
    fn named_local_view_for(&self, name: &str) -> Option<PureExpr> {
        let local = self
            .local_to_name
            .iter()
            .find_map(|(local, local_name)| (local_name == name).then_some(*local))?;
        let inner = self.named_local_expr(local)?;
        Some(PureExpr::View(Arc::new(inner)))
    }

    fn named_local_expr(&self, local: Local) -> Option<PureExpr> {
        let name = self.local_to_name.get(&local)?;
        let sort = self.call_spec_ctx.map_or_else(
            || super::super::translate::ty_to_expr_sort(self.body.local_decls[local].ty),
            |ctx| {
                super::super::translate::ty_to_expr_sort_enriched(
                    ctx.tcx,
                    self.body.local_decls[local].ty,
                )
            },
        );
        Some(PureExpr::Var(name.clone(), sort))
    }

    fn is_index_mut_call(&self, func: &Operand<'tcx>) -> bool {
        let Some(spec_ctx) = self.call_spec_ctx else {
            return false;
        };
        let Some(def_id) = super::super::call_resolve::extract_call_def_id(func) else {
            return false;
        };
        let path = spec_ctx.tcx.def_path_str(def_id);
        path.ends_with("::index_mut")
    }

    /// Whether `func` resolves to an `Index::index` (read-only `recv[ix]`) call.
    ///
    /// Matches the `index` method of the `Index` trait (the by-reference read
    /// indexer), excluding `index_mut`. This is the `Vec<T>`/`[T]` indexing that
    /// MIR lowers to a `Call` (returning `&T`) rather than a primitive `Index`
    /// projection (which slices of statically-known length use).
    fn is_index_read_call(&self, func: &Operand<'tcx>) -> bool {
        let Some(spec_ctx) = self.call_spec_ctx else {
            return false;
        };
        let Some(def_id) = super::super::call_resolve::extract_call_def_id(func) else {
            return false;
        };
        let path = spec_ctx.tcx.def_path_str(def_id);
        path.ends_with("::index") && !path.ends_with("::index_mut")
    }

    /// Model the result of an `Index::index` read call so the dereferenced
    /// element `*result` translates to `self@.index_logic(ix@)`.
    ///
    /// For `Vec<T>`/`[T]` (when the slice length is not statically known) MIR
    /// emits `_r = <_ as Index>::index(recv, ix)` returning a `&T`, then
    /// `_v = *_r`. The `index` callee's std spec is the predicate
    /// `ix.has_value(self@, result)` which, for a scalar `usize` index, is
    /// definitionally `self@.index_logic(ix@) == *result` (see
    /// `SliceIndexSpec::<usize>::has_value`). `try_model_call_result` returns
    /// `None` for this predicate shape, leaving `_r` (and therefore the guard
    /// `*_r > 0`) havoced — which collapses an `if recv[ix] > 0 { .. }` body
    /// into an opaque conservative merge that drops a one-branch accumulator
    /// effect (e.g. `count`).
    ///
    /// We store the dereferenced VALUE `self@.index_logic(ix@)` as the working
    /// expression for the result reference. A subsequent `*_r` projection reads
    /// it back verbatim (the value is not ref-like, so the `Deref` projection
    /// does not re-wrap it). This makes `recv[ix]` translatable in the loop
    /// body without changing any value semantics.
    ///
    /// SOUNDNESS: this binds `*result` to exactly the value the callee's own
    /// `has_value` postcondition guarantees — the element currently at `ix` of
    /// the (immutable, read-only) receiver. It only makes a TRUE read
    /// translatable; it never constrains a mutable post-state and cannot
    /// over-strengthen a body effect. Modeling is restricted to a
    /// SEQUENCE-indexable receiver (`Vec<T>` / `[T]` / `[T; N]`) whose logical
    /// element accessor genuinely IS `self@.index_logic(ix)` — NOT a map
    /// (`HashMap`/`BTreeMap`), whose `Index::index` spec is
    /// `self@.get(key) == Some(result)`, a DIFFERENT accessor: modeling a map
    /// read as `index_logic` would bind a wrong value (potential false-accept),
    /// so map receivers are left havoced. It is further restricted to a scalar
    /// (non-range) index — a range index (`recv[a..b]`) returns a sub-slice, not
    /// an element. If the receiver view or index cannot be recovered, the result
    /// is left havoced (the prior behavior).
    fn try_model_index_read_result(
        &self,
        func: &Operand<'tcx>,
        // Trust: Spanned moved to rustc_span::Spanned (source_map::Spanned is private).
        args: &[rustc_span::Spanned<Operand<'tcx>>],
        dest_local: Local,
        working_exprs: &HashMap<Local, PureExpr>,
    ) -> Option<PureExpr> {
        if !self.is_index_read_call(func) || args.len() < 2 {
            return None;
        }
        // The result must be a reference to a single element `&T`. A range
        // index returns `&[T]` (a sub-slice), whose pointee is itself a slice —
        // exclude that so we never model a sub-slice as an element value.
        let dest_ty = self.body.local_decls[dest_local].ty;
        let TyKind::Ref(_, pointee, _) = dest_ty.kind() else {
            return None;
        };
        if matches!(
            pointee.kind(),
            TyKind::Slice(_) | TyKind::Array(_, _) | TyKind::Str
        ) {
            return None;
        }
        // SOUNDNESS: the receiver collection must be sequence-indexable so that
        // `index_logic` is its genuine element accessor. A map indexer has a
        // `get(key) == Some(result)` spec instead, so modeling it as
        // `index_logic` would bind the wrong value. Require the receiver's
        // collection type (the pointee of the `&recv` receiver) to be a slice,
        // array, or `Vec`.
        let tcx = self.call_spec_ctx?.tcx;
        let recv_ty = args[0].node.ty(&self.body.local_decls, tcx);
        if !is_sequence_indexable_ty(tcx, recv_ty.peel_refs()) {
            return None;
        }
        // Receiver collection view `self@`. The receiver operand is `&recv`
        // (a shared reference to the indexed collection). We name the collection
        // by its loop-visible base variable and view it as `View(Var(recv))` —
        // exactly the form the contract's `recv@` lowers to. The base var is
        // emitted with its enriched sort so the encoder's own
        // `View(Var(.., MutRef)) -> View(Deref(..))` redirect (view.rs) applies
        // the `_current` deref iff the collection is itself a `&mut` reference
        // (e.g. an `&mut Vec` loop receiver); for an owned collection it stays
        // `recv_view`, matching the invariant's `recv@`. Constructing
        // `View(Deref(..))` directly would instead force `recv_current_view`
        // and miss the owned-collection invariant term.
        let receiver = super::super::translate::translate_operand(&args[0].node, working_exprs)?;
        let receiver_name = base_var_name(&receiver)?.to_string();
        let receiver_view = self
            .named_local_view_for(&receiver_name)
            .unwrap_or_else(|| {
                PureExpr::View(Arc::new(PureExpr::Var(receiver_name.clone(), None)))
            });
        // Scalar index `ix@`. A non-scalar (range) index would not translate to
        // a plain element offset; bail to havoc in that case.
        let index = self.translate_operand_or_named_local(&args[1].node, working_exprs)?;
        // The dereferenced element value: `self@.index_logic(ix@)`. Stored as
        // the result reference's working expr so `*result` reads it back (the
        // value is not ref-like, so the `Deref` projection leaves it intact).
        Some(PureExpr::MethodCall {
            receiver: Arc::new(receiver_view),
            method: "index_logic".to_string(),
            args: vec![index],
        })
    }

    /// Model a `while let Cons(..) = l { ..; l = <tail> }` next-iteration
    /// reassignment of a REFERENCE-typed structural-recursion loop variable as
    /// the cons-payload tail accessor `l_prime == *cons_tail_field(l)`.
    ///
    /// For an owned list (`l = *tl`), the tail flows directly as
    /// `Deref(__trust_wp_tuple_get_F(l))` and is already tracked. For a
    /// reference-typed loop variable (`l: &List` / `&mut List`, as in
    /// `binary_search_list` / `all_zero_list`), MIR lowers `l = &*tl` /
    /// `l = next` into a `Box -> NonNull -> *const List` transmute chain followed
    /// by a `&(*raw)` reborrow. None of those raw-pointer cast temporaries
    /// translate, so the loop-var reassignment is HAVOCED — the next-iteration
    /// `l_prime` becomes an unconstrained fresh `List` and the structural
    /// recursion obligation (`l_prime.len() < l.len()`, `l_prime = cons_tail(l)`)
    /// is spuriously SAT.
    ///
    /// This recognizer performs a STATIC MIR def-use walk from the loop-var
    /// reassignment RHS back to a `&[mut] (((*l) as VARIANT).FIELD)` reference
    /// whose scrutinee `l` is the SAME local being reassigned and whose field is
    /// the recursive `Box<EnumTy>` self-payload. When that root is confirmed, it
    /// returns the cons-payload tail accessor expression
    /// `Deref(__trust_wp_tuple_get_FIELD(deref(l)))` — exactly the value the
    /// owned case produces — so the registered datatype unfolding can chain the
    /// recursion.
    ///
    /// SOUNDNESS: this is the TRUE effect. The `while let Cons` condition binds
    /// the payload reference to `(*l as Cons).FIELD`; reborrowing it yields a
    /// reference whose pointee is exactly the cons tail. The accessor
    /// `__trust_wp_tuple_get_FIELD` on the `Datatype`-sorted scrutinee resolves
    /// (in the encoder) to the native `Cons` variant field selector, guarded by
    /// the loop's own `is-Cons(l)` condition that holds on every body iteration.
    /// The fact is NEVER emitted unless the def chain provably roots at the
    /// scrutinee's recursive `Box<Self>` payload field of the body-continuing
    /// variant, so it can bind no value other than the genuine tail.
    fn try_model_cons_tail_reassignment(
        &self,
        dest_local: Local,
        rvalue: &Rvalue<'tcx>,
    ) -> Option<PureExpr> {
        // The reassigned local must be a named, reference-to-enum loop variable.
        let _name = self.local_to_name.get(&dest_local)?;
        let dest_ty = self.body.local_decls[dest_local].ty;
        let TyKind::Ref(_, referent, _) = dest_ty.kind() else {
            return None;
        };
        if !matches!(referent.kind(), TyKind::Adt(adt, _) if adt.is_enum()) {
            return None;
        }
        // RHS must be a `move/copy` of a temporary (the reborrowed tail ref).
        let Rvalue::Use(Operand::Copy(src) | Operand::Move(src), _) = rvalue else {
            return None;
        };
        if !src.projection.is_empty() {
            return None;
        }
        // Walk the def chain of `src.local` within the loop body back to a
        // `&[mut] (((*S) as VARIANT).FIELD)` ref of the scrutinee S.
        let (scrutinee_local, field_idx) = self.trace_cons_tail_ref_root(src.local, dest_local)?;
        // SOUNDNESS: the scrutinee of the cons-tail ref MUST be the same local
        // being reassigned (`while let Cons(..) = l { l = tail }`). A different
        // scrutinee would not be the loop's structural-recursion variable.
        if scrutinee_local != dest_local {
            return None;
        }
        // Build the cons-payload tail accessor on the scrutinee viewed as its
        // `Datatype` value. The scrutinee is `&[mut] EnumTy`; its dereferenced
        // enum value is `Deref(Var(name, Ref/MutRef(Datatype)))` — the exact
        // form the loop's `discriminant((*l))` condition uses. The tail box
        // `__trust_wp_tuple_get_FIELD(deref(l))` routes (in the encoder) to the
        // native `Cons` variant field selector; the outer `Deref` is the
        // (transparent) `Box` deref yielding the tail `EnumTy` value — matching
        // the owned case's `Deref(__trust_wp_tuple_get_1(l))`.
        let scrutinee_expr = self.named_local_expr(scrutinee_local)?;
        let scrutinee_datatype = PureExpr::Deref(Arc::new(scrutinee_expr));
        let tail_box = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(field_idx),
            args: vec![scrutinee_datatype],
        };
        Some(PureExpr::Deref(Arc::new(tail_box)))
    }

    /// Statically trace the def chain of `local` (within the loop body) back to
    /// a `&[mut] (((*S) as VARIANT).FIELD)` ref whose field is a `Box<EnumTy>`
    /// recursive self-payload. Returns the scrutinee local `S` and the field
    /// index. The chain threads through the `Box -> NonNull -> *const T`
    /// transmute lowering and the final `&(*raw)` reborrow that MIR emits for a
    /// reference-typed `l = &*tail` reassignment.
    ///
    /// Bounded def-use: each step resolves a local's UNIQUE defining assignment
    /// across the loop body blocks. The walk follows only value-preserving
    /// pointer reshaping (`Ref`, `CopyForDeref`, transmute/ptr casts, the
    /// box-field `Copy`) so it can never reach a different value than the tail.
    fn trace_cons_tail_ref_root(
        &self,
        local: Local,
        scrutinee_local: Local,
    ) -> Option<(Local, usize)> {
        // Bound the walk to avoid pathological chains.
        let mut current = local;
        for _ in 0..16 {
            let def = self.find_unique_def(current)?;
            match def {
                // `&[mut] (((*S) as VARIANT).FIELD)` — the cons-tail box ref.
                // This is the root we are looking for.
                CtRef::DowncastFieldRef {
                    scrutinee,
                    variant,
                    field_idx,
                } => {
                    // The field must be a `Box<EnumTy>` recursive self-payload of
                    // the SPECIFIC downcast variant, and the scrutinee must deref
                    // to the same enum the loop var references. Verified below.
                    if self.is_recursive_box_field(scrutinee, scrutinee_local, variant, field_idx) {
                        return Some((scrutinee, field_idx));
                    }
                    return None;
                }
                // Value-preserving reshaping: follow the source local.
                CtRef::Forward(next) => current = next,
            }
        }
        None
    }

    /// Find the unique defining assignment of `local` across the loop body and
    /// classify it as either the cons-tail-box ref root or a value-preserving
    /// forward step (returning the source local to continue tracing).
    fn find_unique_def(&self, local: Local) -> Option<CtRef> {
        let mut found: Option<CtRef> = None;
        for &block in self.body_blocks {
            let block_data = &self.body.basic_blocks[block];
            for stmt in &block_data.statements {
                let StatementKind::Assign((place, rvalue)) = &stmt.kind else {
                    continue;
                };
                if place.local != local || !place.projection.is_empty() {
                    continue;
                }
                // More than one def of the same local in the body → ambiguous;
                // refuse to model (fail closed).
                if found.is_some() {
                    return None;
                }
                found = Some(Self::classify_cons_tail_def(rvalue)?);
            }
        }
        found
    }

    /// Classify a defining rvalue as the cons-tail-box reference root, a
    /// value-preserving forward step, or unsupported (`None`).
    fn classify_cons_tail_def(rvalue: &Rvalue<'tcx>) -> Option<CtRef> {
        match rvalue {
            // `&[mut] place` — either the downcast-field ref root, or a
            // reborrow `&(*raw)` that forwards to the raw pointer.
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                let projs: &[_] = place.projection.as_ref();
                // Root: `&[mut] (((*S) as VARIANT).FIELD)` =
                //   [Deref, Downcast(_), Field(F)].
                if let [ProjectionElem::Deref, ProjectionElem::Downcast(_, variant), ProjectionElem::Field(field, _)] =
                    projs
                {
                    return Some(CtRef::DowncastFieldRef {
                        scrutinee: place.local,
                        variant: *variant,
                        field_idx: usize::try_from(field.as_u32()).ok()?,
                    });
                }
                // Reborrow `&(*raw)` = [Deref]: forward to the pointer local.
                if let [ProjectionElem::Deref] = projs {
                    return Some(CtRef::Forward(place.local));
                }
                // Reborrow through a `&mut Box<T>` recursive tail: `&mut (*(*p))`
                // = [Deref, Deref] — deref the reference to reach the `Box`, then
                // deref the `Box` to reach the owned tail value (the shape MIR
                // emits for `loop_l = next` when `next: &mut Box<Self>` and
                // `loop_l: &mut Self`). Value-preserving pointer reshaping, so
                // forward to the pointer local. Fail-closed: the continued walk
                // still must terminate at the genuine `DowncastFieldRef` root and
                // pass `is_recursive_box_field` + `scrutinee == dest`.
                if let [ProjectionElem::Deref, ProjectionElem::Deref] = projs {
                    return Some(CtRef::Forward(place.local));
                }
                None
            }
            // `copy/move place` — forward to the source local ONLY when the
            // place projection is value-preserving for the tail address (the
            // `Box -> NonNull` field unwrap or a bare local / single deref). Any
            // other projection (e.g. a sibling tuple field) could change the
            // value, so reject it (fail closed).
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)
            | Rvalue::CopyForDeref(place) => {
                is_tail_address_preserving_projection(place.projection.as_ref())
                    .then_some(CtRef::Forward(place.local))
            }
            Rvalue::Cast(cast_kind, operand, _) => {
                // Only pointer-identity reshaping casts are value-preserving for
                // the tail address. Reject anything else (fail closed).
                if !matches!(
                    cast_kind,
                    CastKind::Transmute
                        | CastKind::BoxDerefTransmute
                        | CastKind::PtrToPtr
                        | CastKind::PointerCoercion(..)
                        | CastKind::PointerExposeProvenance
                        | CastKind::PointerWithExposedProvenance
                ) {
                    return None;
                }
                let (Operand::Copy(place) | Operand::Move(place)) = operand else {
                    return None;
                };
                is_tail_address_preserving_projection(place.projection.as_ref())
                    .then_some(CtRef::Forward(place.local))
            }
            _ => None,
        }
    }

    /// Whether the downcast `variant` of `scrutinee`'s enum has a `Box<EnumTy>`
    /// field at `field_idx` whose inner type is the SAME enum that the loop
    /// variable (`loop_var`) references — i.e. a genuine recursive self-payload.
    /// This is the soundness gate ensuring the modeled tail is the recursive
    /// list tail and not an unrelated boxed field of a different variant/type.
    fn is_recursive_box_field(
        &self,
        scrutinee: Local,
        loop_var: Local,
        variant: rustc_abi::VariantIdx,
        field_idx: usize,
    ) -> bool {
        let Some(spec_ctx) = self.call_spec_ctx else {
            return false;
        };
        let tcx = spec_ctx.tcx;
        // The loop variable references the recursive enum `EnumTy`.
        let TyKind::Ref(_, loop_referent, _) = self.body.local_decls[loop_var].ty.kind() else {
            return false;
        };
        let TyKind::Adt(loop_adt, _) = loop_referent.kind() else {
            return false;
        };
        // The scrutinee must be a reference to the SAME enum.
        let scrutinee_ty = self.body.local_decls[scrutinee].ty;
        let TyKind::Ref(_, scrut_referent, _) = scrutinee_ty.kind() else {
            return false;
        };
        let TyKind::Adt(scrut_adt, scrut_substs) = scrut_referent.kind() else {
            return false;
        };
        if scrut_adt.did() != loop_adt.did() || !scrut_adt.is_enum() {
            return false;
        }
        // The field at `field_idx` of the SPECIFIC downcast variant must be a
        // `Box<EnumTy>` with `EnumTy` the same recursive enum — the cons tail.
        let Some(variant_def) = scrut_adt.variants().get(variant) else {
            return false;
        };
        variant_def
            .fields
            .get(rustc_abi::FieldIdx::from_usize(field_idx))
            .is_some_and(|field| {
                let field_ty = field.ty(tcx, *scrut_substs).skip_norm_wip();
                matches!(field_ty.kind(), TyKind::Adt(box_def, box_substs)
                if box_def.is_box()
                    && box_substs.types().next().is_some_and(|inner| {
                        matches!(inner.kind(), TyKind::Adt(inner_adt, _)
                            if inner_adt.did() == scrut_adt.did())
                    }))
            })
    }

    fn apply_assignments(&self, bb: BasicBlock, state: &mut BodyExtractionState) {
        let bb_data = &self.body.basic_blocks[bb];
        for stmt in &bb_data.statements {
            if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
                if place.projection.is_empty() {
                    // Direct assignment: `local = rvalue`
                    let pending_index_mut_alias =
                        Self::pending_index_mut_alias_from_rvalue(rvalue, state);
                    if let Some(cons_tail) =
                        self.try_model_cons_tail_reassignment(place.local, rvalue)
                    {
                        state.working_exprs.insert(place.local, cons_tail.clone());
                        if let Some(var_name) = self.local_to_name.get(&place.local) {
                            state.effects.insert(var_name.clone(), cons_tail);
                        }
                        state.pending_index_mut.remove(&place.local);
                        continue;
                    }
                    if let Some(expr) = self.translate_rvalue_for_effect(rvalue, state) {
                        let working_expr = self.deref_wrap_working_expr(place.local, rvalue, &expr);
                        state.working_exprs.insert(place.local, working_expr);
                        if let Some(var_name) = self.local_to_name.get(&place.local) {
                            state.effects.insert(var_name.clone(), expr);
                        }
                    } else {
                        state.working_exprs.remove(&place.local);
                        if let Some(var_name) = self.local_to_name.get(&place.local) {
                            state.effects.remove(var_name);
                        }
                    }
                    if let Some(pending) = pending_index_mut_alias {
                        state.pending_index_mut.insert(place.local, pending);
                    } else {
                        state.pending_index_mut.remove(&place.local);
                    }
                } else if !self.apply_struct_field_assignment(place, rvalue, state)
                    && !self.apply_indexed_place_assignment(place, rvalue, state)
                {
                    self.apply_deref_assignment(place, rvalue, state);
                }
                if place.is_indirect() {
                    self.forget_lent_body_locals(state);
                }
            }
        }

        // A Call terminator writes to `destination`. Model with spec or havoc.
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &bb_data.terminator().kind
        {
            self.apply_call_terminator(bb, func, args, destination, state);
        }
        // Every terminator that hands off memory, a `Drop` as much as a call.
        self.forget_body_locals_written_at_terminator(bb, state);
    }

    /// Give a call's destination the value its callee's contract states, and
    /// record the premises that come with it (or the ones it cannot state).
    ///
    /// One definition for the body walk and for the loop condition's own call
    /// (`condition_call_value`): the condition a VC assumes and the premises
    /// stated about the value it reads must name the same thing.
    pub(super) fn apply_call_terminator(
        &self,
        bb: BasicBlock,
        func: &Operand<'tcx>,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        state: &mut BodyExtractionState,
    ) {
        // Model Seq ghost mutation methods (#1581)
        let seq_ghost_modeled = self.apply_seq_ghost_mutation(func, args, state);
        // Model `&mut self` mutators (push/insert/swap/...) by recording the
        // `(^self)@` post-state of the receiver as a deref body effect, so the
        // post-state reaches the loop preservation VC instead of being havoced.
        let carried_clause = self.apply_mut_self_post_state(func, args, state);
        let pending_index_mut = self.record_pending_index_mut(func, args, destination, state);

        // A model is WHOLE when it states everything the callee's contract
        // says about this call; `try_model_call_result` states one
        // `result == e` clause and leaves the rest to the premise below.
        let (modeled, whole_contract_modeled) = if !destination.projection.is_empty() {
            (None, false)
        } else if pending_index_mut {
            (None, true)
        } else if let Some(adapted) = std::env::var_os("TRUST_WP_OFFLOOP").and_then(|_| {
            // Option adapter/unwrap modeling first (#counter-cons-tail):
            // `as_mut`/`unwrap` specs are implication-style (no bare
            // `result == e` clause), so the generic spec path below
            // havocs them, severing call-chain tail advances like
            // `l = l.1.as_mut().unwrap()`. Env-gated during rollout.
            self.try_model_option_adapter_result(func, args, &state.working_exprs)
        }) {
            (Some(adapted), true)
        } else if let Some(result) =
            self.try_model_call_result(func, args, destination.local, &state.working_exprs)
        {
            (Some(result), false)
        } else if let Some(read) =
            self.try_model_index_read_result(func, args, destination.local, &state.working_exprs)
        {
            (Some(read), true)
        } else {
            (None, false)
        };
        let result_expr = if whole_contract_modeled || seq_ghost_modeled {
            modeled
        } else {
            match self.call_postcondition_premise(
                bb,
                func,
                args,
                destination,
                modeled.as_ref(),
                carried_clause,
                state,
            ) {
                CallPremise::Carried { result, facts } => {
                    for fact in facts {
                        if !state.call_facts.contains(&fact) {
                            state.call_facts.push(fact);
                        }
                    }
                    result
                }
                CallPremise::Dropped(premise) => {
                    if !state.dropped_premises.contains(&premise) {
                        state.dropped_premises.push(premise);
                    }
                    modeled
                }
            }
        };

        match result_expr.filter(|_| destination.projection.is_empty()) {
            Some(result_expr) => {
                state
                    .working_exprs
                    .insert(destination.local, result_expr.clone());
                if let Some(var_name) = self.local_to_name.get(&destination.local) {
                    state.effects.insert(var_name.clone(), result_expr);
                }
            }
            None => {
                // Unmodeled, or a projected destination: havoc for soundness.
                state.working_exprs.remove(&destination.local);
                if let Some(var_name) = self.local_to_name.get(&destination.local) {
                    state.effects.remove(var_name);
                }
            }
        }
    }

    /// Forget the body-locals the terminator of `bb` may write behind the
    /// walk; the call's own arguments and result were read above. A callee
    /// handed an argument it may write through (a `&mut`, a raw pointer, a
    /// value holding one, interior mutability) may write any lent body-local,
    /// the callee's `^` being bound by no walk here; a `Drop`
    /// or a call whose drop glue may write changes what
    /// `locals_changed_by_handoff` names, the substitution walk's own answer
    /// at the same terminator (D-140).
    fn forget_body_locals_written_at_terminator(
        &self,
        bb: BasicBlock,
        state: &mut BodyExtractionState,
    ) {
        let terminator = self.body.basic_blocks[bb].terminator();
        if !matches!(
            terminator.kind,
            TerminatorKind::Call { .. } | TerminatorKind::Drop { .. }
        ) {
            return;
        }
        let Some(ctx) = self.call_spec_ctx else {
            self.forget_lent_body_locals(state);
            return;
        };
        let lends = matches!(&terminator.kind, TerminatorKind::Call { func, args, .. }
        if crate::mir_analysis::extract::drop_glue_writes::call_may_write_through_args(
            ctx.tcx, self.body, func, args,
        ));
        if lends {
            self.forget_lent_body_locals(state);
            return;
        }
        let changed = crate::mir_analysis::extract::drop_glue_writes::locals_changed_by_handoff(
            ctx.tcx, self.body, bb, terminator,
        );
        if let Some(changed) = changed {
            let born: Vec<Local> = changed
                .into_iter()
                .filter(|local| self.lent_body_locals.born.contains(local))
                .collect();
            self.forget_locals(state, &born);
        }
    }

    /// Forget every lent body-local ([`lent_body_locals`]): a store through a
    /// reference, or a callee handed one, may have written it.
    fn forget_lent_body_locals(&self, state: &mut BodyExtractionState) {
        let lent: Vec<Local> = self.lent_body_locals.lent.iter().copied().collect();
        self.forget_locals(state, &lent);
    }

    /// A later read of a forgotten body-local is its name, which nothing
    /// constrains, and its own effect is dropped.
    fn forget_locals(&self, state: &mut BodyExtractionState, locals: &[Local]) {
        for local in locals {
            state.working_exprs.remove(local);
            if let Some(var_name) = self.local_to_name.get(local) {
                state.effects.remove(var_name);
            }
        }
    }
}

/// Whether a place projection is value-preserving for the cons-tail ADDRESS
/// during the `try_model_cons_tail_reassignment` def-use walk: a bare local
/// (no projection), a single `Deref` (box/raw-pointer unwrap), or a pure
/// `Field`-only chain (the `Box -> BoxRaw` internal field unwrap the
/// MIR `Box` lowering emits). These steps all keep the SAME tail pointer; any
/// other projection (e.g. `Index`, `Downcast` mid-chain, or a mix) could select
/// a different value, so it is rejected (fail closed).
fn is_tail_address_preserving_projection(projection: &[ProjectionElem<Local, Ty<'_>>]) -> bool {
    match projection {
        [] => true,
        [ProjectionElem::Deref] => true,
        projs
            if projs
                .iter()
                .all(|p| matches!(p, ProjectionElem::Field(_, _))) =>
        {
            true
        }
        _ => false,
    }
}

/// Whether `written` reads a field `tuple_get_j(Var(var_name))` of the same
/// struct local with `j != written_field` — i.e. it depends on a SIBLING field
/// of the local being written. Used as a conservative soundness guard for
/// chained dependent struct field writes (#2702).
fn written_reads_other_updated_field(
    written: &PureExpr,
    var_name: &str,
    written_field: usize,
) -> bool {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_index;
    let mut found = false;
    written.for_each_recursive(|node| {
        if let PureExpr::LogicFnCall { name, args } = node {
            if let Some(idx) = tuple_field_logic_fn_index(name) {
                if idx != written_field
                    && args.len() == 1
                    && matches!(&args[0], PureExpr::Var(n, _) if n == var_name)
                {
                    found = true;
                }
            }
        }
    });
    found
}

/// Whether `ty` is a sequence-indexable collection whose genuine logical
/// element accessor is `self@.index_logic(ix)`: a slice `[T]`, an array
/// `[T; N]`, or `Vec<T>`. Maps (`HashMap`/`BTreeMap`) are intentionally
/// excluded — their `Index::index` spec is `self@.get(key) == Some(result)`,
/// a DIFFERENT accessor — so modeling a map read as `index_logic` is rejected
/// to preserve soundness. `ty` is expected to be the receiver collection type
/// with references peeled.
fn is_sequence_indexable_ty<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    match ty.kind() {
        TyKind::Slice(_) | TyKind::Array(_, _) => true,
        TyKind::Adt(adt_def, _) => {
            let path = tcx.def_path_str(adt_def.did());
            // Match the concrete std sequence collection by its def-path.
            // `Vec`/`VecDeque` both expose `index_logic` as their element view;
            // any other ADT (notably maps) is rejected.
            path == "std::vec::Vec"
                || path == "alloc::vec::Vec"
                || path == "std::collections::VecDeque"
                || path == "alloc::collections::VecDeque"
                || path == "std::collections::vec_deque::VecDeque"
                || path == "alloc::collections::vec_deque::VecDeque"
        }
        _ => false,
    }
}

fn apply_indexed_write_effect(
    state: &mut BodyExtractionState,
    param_name: &str,
    index: PureExpr,
    value: PureExpr,
) {
    let current = state
        .deref_effects
        .get(param_name)
        .cloned()
        .unwrap_or_else(|| {
            PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                param_name.to_string(),
                None,
            )))))
        });
    state.deref_effects.insert(
        param_name.to_string(),
        PureExpr::MethodCall {
            receiver: Arc::new(current),
            method: "set".to_string(),
            args: vec![index, value],
        },
    );
}
