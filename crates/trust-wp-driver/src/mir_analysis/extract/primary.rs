// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, Body, Local, Location, Operand, Place, ProjectionElem, Rvalue,
        SwitchTargets, TerminatorKind,
    },
    ty::TyCtxt,
};
use rustc_span::Span;
use trust_wp_core::formula::{
    internal::tuple_lowering::{
        tuple_field_logic_fn_index, tuple_field_logic_fn_name, tuple_logic_fn_arity,
        tuple_logic_fn_name,
    },
    BinOp, ExprSort, PureExpr,
};
use trust_wp_driver::StdSpec;

use super::{
    super::{
        diagnostics::{record_extraction_diag, ExtractionDiagKind, ExtractionDiagnosticSink},
        effects::{CallEffects, ExtractionSession},
        loops::LoopAnalysis,
        translate::{
            operand_int_ty, operand_is_bool, translate_operand_detailed, ty_to_expr_sort_enriched,
            TranslationDiagContext,
        },
    },
    assertion::{assert_fact_from_condition, wrap_continuation_with_assert_fact},
    block_visitor::{self, BlockVisitor},
    branching::{
        handle_bool_switch_with_context, handle_int_switch_with_context, BoolSwitchState,
        IntSwitchState,
    },
    call_spec::handle_call_terminator,
    closure::propagate_mutating_receiver_state_with_captures,
    cutoff::{
        cutoff_reached_at_statement, cutoff_reached_at_terminator, proof_assert_state_marker,
    },
    helpers::{
        expr_references_var_name, invalidate_overlapping_projected_write_facts,
        record_projected_write_fact, source_name_for_local, translate_projected_write_lhs,
        translate_rvalue_with_enum_variants, wrap_projected_facts,
    },
};

/// Read-only context for block-level return expression extraction.
///
/// Groups the four parameters that are threaded unchanged through every
/// recursive call of `extract_from_block_with_context`, keeping the
/// function under clippy's `too_many_arguments` threshold while preserving the
/// same runtime behaviour.
pub(in crate::mir_analysis) struct BlockExtractionContext<'a> {
    pub(super) arg_names: &'a [String],
    pub(super) user_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) trait_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) extern_specs: &'a HashMap<String, StdSpec>,
    pub(super) scope_call_context: bool,
    pub(super) cutoff_span: Option<Span>,
    pub(super) cutoff_location: Option<Location>,
    pub(super) diagnostics: Option<&'a ExtractionDiagnosticSink>,
    /// Loop analysis for skipping inner loop bodies during extraction.
    /// When present, `FalseUnwind` terminators targeting inner loop headers
    /// are redirected to the loop exit block, avoiding ControlFlowCycle
    /// failures from walking into loop back-edges. (#2698)
    pub(super) loop_analysis: Option<&'a LoopAnalysis>,
}

impl BlockExtractionContext<'_> {
    pub(super) fn record_diag(
        &self,
        module: &'static str,
        kind: ExtractionDiagKind,
        detail: impl Into<String>,
        location: Option<Location>,
    ) {
        record_extraction_diag(self.diagnostics, module, kind, detail, location);
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum LoopExitResolution {
    Exit(BasicBlock),
    Infinite,
    NotALoopHeader,
}

impl BlockExtractionContext<'_> {
    /// If `target` is an inner loop header, find the loop's exit block.
    ///
    /// When `FalseUnwind` targets a loop header, the extraction pipeline
    /// should skip the entire loop body and continue from the exit block.
    /// This avoids ControlFlowCycle failures from walking into back-edges.
    ///
    /// Returns [`LoopExitResolution::Exit`] when `target` is a loop header
    /// and an exit block can be identified, [`LoopExitResolution::Infinite`]
    /// for diverging loops with no extractable exit, and
    /// [`LoopExitResolution::NotALoopHeader`] otherwise. (#2698)
    pub(super) fn find_loop_exit_for_extraction(
        &self,
        target: BasicBlock,
        body: &Body<'_>,
    ) -> LoopExitResolution {
        let Some(analysis) = self.loop_analysis else {
            return LoopExitResolution::NotALoopHeader;
        };
        let Some(loop_info) = analysis.loops.iter().find(|li| li.header == target) else {
            return LoopExitResolution::NotALoopHeader;
        };

        // The loop header is typically FalseUnwind -> cond_block (or is
        // itself the condition block). Find the SwitchInt that controls
        // the loop exit.
        let header_data = &body.basic_blocks[target];
        let cond_block = match &header_data.terminator().kind {
            TerminatorKind::SwitchInt { .. } => target,
            TerminatorKind::FalseUnwind { real_target, .. }
            | TerminatorKind::Goto {
                target: real_target,
            } => *real_target,
            // For-loop pattern: header is Call(Iterator::next) -> switch_bb.
            // Follow one hop to find the SwitchInt condition block. (#2698)
            TerminatorKind::Call {
                target: Some(switch_bb),
                ..
            } => *switch_bb,
            _ => target,
        };
        let cond_data = &body.basic_blocks[cond_block];
        // If the condition block is itself another hop (e.g., Call -> switch
        // in a for-loop pattern), follow one more level. (#2698)
        let cond_data = match &cond_data.terminator().kind {
            TerminatorKind::SwitchInt { .. } => cond_data,
            TerminatorKind::Call {
                target: Some(next_bb),
                ..
            } => &body.basic_blocks[*next_bb],
            TerminatorKind::Goto { target: next_bb } => &body.basic_blocks[*next_bb],
            _ => cond_data,
        };
        match &cond_data.terminator().kind {
            TerminatorKind::SwitchInt { targets, .. } => {
                // The exit target is the one NOT in the loop body.
                for exit_bb in targets.all_targets() {
                    if !loop_info.body_blocks.contains(exit_bb) {
                        return LoopExitResolution::Exit(*exit_bb);
                    }
                }
                LoopExitResolution::Infinite
            }
            _ => LoopExitResolution::Infinite,
        }
    }

    /// Build a [`TranslationDiagContext`] that records into this context's
    /// diagnostic sink with the given location. Returns `None` when no
    /// diagnostics sink is attached (legacy code paths).
    fn translation_diag(&self, location: Option<Location>) -> Option<TranslationDiagContext<'_>> {
        self.diagnostics.map(|sink| TranslationDiagContext {
            sink: Some(sink),
            module: "extract/primary.rs",
            location,
        })
    }
}

/// Mutable state for the primary extraction pipeline, implementing
/// [`block_visitor::BlockVisitor`] so the shared `walk_block` driver
/// handles statement dispatch and simple terminator routing.
///
/// Complex terminators (SwitchInt, Call) delegate to the existing
/// handler functions in `branching.rs` and `call_spec/dispatch.rs`, which
/// recurse via `extract_from_block_with_context`.
struct PrimaryVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    local_exprs: HashMap<Local, PureExpr>,
    projected_write_facts: Vec<(PureExpr, PureExpr)>,
    visited: HashSet<BasicBlock>,
    ctx: &'a BlockExtractionContext<'a>,
    effects: &'a mut CallEffects,
}

impl<'a, 'tcx> PrimaryVisitor<'a, 'tcx> {
    /// Build a cutoff marker from projected write facts + state marker.
    fn cutoff_marker(&self) -> PureExpr {
        let mut marker = proof_assert_state_marker(&self.local_exprs);
        for (lhs, rhs) in self.projected_write_facts.iter().rev() {
            let fact = PureExpr::BinOp(Arc::new(lhs.clone()), BinOp::Eq, Arc::new(rhs.clone()));
            marker = PureExpr::LetAssume {
                assumption: Arc::new(fact),
                body: Arc::new(marker),
            };
        }
        marker
    }

    /// Mark all blocks in the loop with the given header as visited.
    fn mark_loop_body_visited(&mut self, header: BasicBlock) {
        if let Some(analysis) = self.ctx.loop_analysis {
            if let Some(li) = analysis.loops.iter().find(|li| li.header == header) {
                for &bb in &li.body_blocks {
                    self.visited.insert(bb);
                }
            }
        }
    }

    fn block_is_in_known_loop_body(&self, block: BasicBlock) -> bool {
        self.ctx.loop_analysis.is_some_and(|analysis| {
            analysis
                .loops
                .iter()
                .any(|loop_info| loop_info.body_blocks.contains(&block))
        })
    }

    /// If `target` is a loop header, skip the entire loop body and continue
    /// from the exit block. Otherwise, continue to `target` as normal.
    ///
    /// Used by `on_false_edge` to avoid walking into loop bodies during
    /// return expression extraction. (#2698)
    fn skip_loop_or_continue(
        &mut self,
        target: BasicBlock,
    ) -> block_visitor::VisitorAction<PureExpr> {
        match self.ctx.find_loop_exit_for_extraction(target, self.body) {
            LoopExitResolution::Exit(exit_bb) => {
                self.mark_loop_body_visited(target);
                block_visitor::VisitorAction::Continue(exit_bb)
            }
            LoopExitResolution::Infinite => {
                self.mark_loop_body_visited(target);
                block_visitor::VisitorAction::bail()
            }
            LoopExitResolution::NotALoopHeader => block_visitor::VisitorAction::Continue(target),
        }
    }

    /// Handle the projected write logic shared between non-deref and
    /// deref projected writes.
    fn handle_projected_write(
        &mut self,
        place: &rustc_middle::mir::Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        body: &Body<'tcx>,
        location: Location,
    ) {
        // Per-borrow carriers (#124): a single-deref write through a tracked
        // borrow updates its armed death value; any deref write we cannot
        // track whole-value (deeper projections, untranslatable RHS) disarms
        // the pending expiry facts instead (fail-closed).
        let projections: &[_] = place.projection.as_ref();
        let is_single_deref = matches!(projections, [rustc_middle::mir::ProjectionElem::Deref]);
        let has_deref = projections
            .iter()
            .any(|proj| matches!(proj, rustc_middle::mir::ProjectionElem::Deref));
        let mut tracked_deref_write = false;
        if let Some(lhs) = translate_projected_write_lhs(
            body,
            place,
            &self.local_exprs,
            self.ctx.arg_names,
            self.tcx,
        ) {
            // Invalidate stale overlaps even when RHS translation
            // fails, otherwise older nested facts can survive.
            invalidate_overlapping_projected_write_facts(&mut self.projected_write_facts, &lhs);
            if let Some(rhs) = translate_rvalue_with_enum_variants(
                self.tcx,
                rvalue,
                &self.local_exprs,
                Some(body),
                self.ctx.diagnostics,
                Some(location),
            ) {
                if is_single_deref {
                    super::borrow_carriers::note_single_deref_write(place.local, &rhs);
                    tracked_deref_write = true;
                }
                let mut fact_lhs = lhs;
                if let Some(receiver) = receiver_for_mut_ref_result_write(&fact_lhs, self.effects) {
                    // Commit writes through borrowed `&mut` call results into
                    // the receiver's symbolic post-state so later reads use
                    // the updated receiver rather than the temporary result.
                    self.effects.has_mutating_call_effect = true;
                    propagate_mutating_receiver_state_with_captures(
                        &mut self.local_exprs,
                        body,
                        self.ctx.arg_names,
                        &receiver,
                        None,
                    );
                    let promoted_lhs = PureExpr::View(Arc::new(
                        crate::callbacks::final_receiver_state_expr(&receiver),
                    ));
                    invalidate_overlapping_projected_write_facts(
                        &mut self.projected_write_facts,
                        &promoted_lhs,
                    );
                    fact_lhs = promoted_lhs;
                }
                record_projected_write_fact(&mut self.projected_write_facts, fact_lhs, rhs);
            }
        }
        if has_deref && !tracked_deref_write {
            super::borrow_carriers::note_projected_deref_write();
        }
    }
}

fn receiver_for_mut_ref_result_write(lhs: &PureExpr, effects: &CallEffects) -> Option<PureExpr> {
    let PureExpr::Deref(inner) = lhs else {
        return None;
    };
    let PureExpr::Var(result_name, _) = inner.as_ref() else {
        return None;
    };

    effects
        .mut_ref_result_receivers
        .get(result_name)
        .cloned()
        .or_else(|| {
            effects.assumptions.iter().find_map(|assumption| {
                receiver_from_mut_ref_result_final_link(assumption, result_name)
            })
        })
}

fn translate_projected_ref_rvalue<'tcx>(
    rvalue: &Rvalue<'tcx>,
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<PureExpr> {
    let Rvalue::Ref(_, _, place) = rvalue else {
        return None;
    };
    translate_projected_ref_place(place, local_exprs)
}

fn translate_projected_ref_place<'tcx>(
    place: &Place<'tcx>,
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<PureExpr> {
    let projections = place.projection.as_ref();
    if !projections
        .iter()
        .any(|projection| matches!(projection, ProjectionElem::Deref))
        || !projections
            .iter()
            .any(|projection| matches!(projection, ProjectionElem::Field(..)))
    {
        return None;
    }

    let mut current = local_exprs.get(&place.local)?.clone();
    for projection in projections {
        match projection {
            ProjectionElem::Deref => {}
            ProjectionElem::Field(field, _) => {
                current = project_ref_field(current, usize::try_from(field.as_u32()).ok()?)?;
            }
            ProjectionElem::Downcast(_, _) => {}
            _ => return None,
        }
    }
    Some(current)
}

fn project_ref_field(current: PureExpr, field_idx: usize) -> Option<PureExpr> {
    if let PureExpr::LogicFnCall { name, args } = &current {
        if tuple_logic_fn_arity(name).is_some_and(|arity| arity == args.len()) {
            return args.get(field_idx).cloned();
        }
        if tuple_field_logic_fn_index(name).is_some() {
            return Some(PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(field_idx),
                args: vec![current],
            });
        }
    }

    if matches!(current, PureExpr::Var(..)) {
        return Some(PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(field_idx),
            args: vec![current],
        });
    }

    None
}

fn receiver_from_mut_ref_result_final_link(
    assumption: &PureExpr,
    result_name: &str,
) -> Option<PureExpr> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = assumption else {
        return None;
    };

    fn linked_receiver(expr: &PureExpr, target: &PureExpr, result_name: &str) -> Option<PureExpr> {
        if !matches!(
            expr,
            PureExpr::Final(inner)
                if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == result_name)
        ) {
            return None;
        }
        let PureExpr::View(view_inner) = target else {
            return None;
        };
        let PureExpr::Final(receiver) = view_inner.as_ref() else {
            return None;
        };
        Some(receiver.as_ref().clone())
    }

    linked_receiver(left.as_ref(), right.as_ref(), result_name)
        .or_else(|| linked_receiver(right.as_ref(), left.as_ref(), result_name))
}

fn translate_struct_aggregate_as_tuple<'tcx>(
    tcx: TyCtxt<'tcx>,
    rvalue: &Rvalue<'tcx>,
    local_exprs: &HashMap<Local, PureExpr>,
    diag: Option<&TranslationDiagContext<'_>>,
) -> Option<PureExpr> {
    let Rvalue::Aggregate(box AggregateKind::Adt(def_id, ..), operands) = rvalue else {
        return None;
    };
    if !tcx.adt_def(*def_id).is_struct() {
        return None;
    }

    let mut translated = Vec::with_capacity(operands.len());
    for operand in operands {
        translated.push(translate_operand_detailed(operand, local_exprs, diag)?);
    }
    match translated.as_slice() {
        [] => Some(PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(0),
            args: vec![],
        }),
        [single] => Some(single.clone()),
        _ => Some(PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(translated.len()),
            args: translated,
        }),
    }
}

impl<'a, 'tcx> BlockVisitor<'tcx> for PrimaryVisitor<'a, 'tcx> {
    type Result = PureExpr;

    fn visited_mut(&mut self) -> &mut HashSet<BasicBlock> {
        &mut self.visited
    }

    fn on_assign_local(
        &mut self,
        local: Local,
        rvalue: &Rvalue<'tcx>,
        body: &Body<'tcx>,
        location: Location,
    ) {
        // Per-borrow carriers (#124): a moved `&mut` local escapes the
        // expiry tracking — disarm its pending resolution fact (fail-closed).
        super::borrow_carriers::note_moved_mut_refs_in_rvalue(body, rvalue);
        if let Some(expr) = translate_projected_ref_rvalue(rvalue, &self.local_exprs) {
            self.local_exprs.insert(local, expr);
            if let Some(name) = source_name_for_local(body, local, self.ctx.arg_names) {
                self.projected_write_facts
                    .retain(|(lhs, _)| !expr_references_var_name(lhs, &name));
            }
            return;
        }

        // Whole-local assignment: update local_exprs.
        // Projected assignments must not clobber the base local. (#928)
        let diag = self.ctx.translation_diag(Some(location));
        if let Some(expr) =
            translate_struct_aggregate_as_tuple(self.tcx, rvalue, &self.local_exprs, diag.as_ref())
                .or_else(|| {
                    translate_rvalue_with_enum_variants(
                        self.tcx,
                        rvalue,
                        &self.local_exprs,
                        Some(body),
                        self.ctx.diagnostics,
                        Some(location),
                    )
                })
        {
            self.local_exprs.insert(local, expr);
            // Invalidate projected-write facts referencing the
            // reassigned local. Without this, stale facts from
            // prior field writes (e.g., `pair.1 = 10`) survive
            // whole-local overwrites (`pair = (7, 20)`) and can
            // produce vacuous verification. (#1450)
            if let Some(name) = source_name_for_local(body, local, self.ctx.arg_names) {
                self.projected_write_facts
                    .retain(|(lhs, _)| !expr_references_var_name(lhs, &name));
            }
        } else {
            // Keep the destination bound even when the RHS is too opaque to
            // translate. This preserves later reads of compiler temporaries
            // such as `_4` in named-ADT construction bodies instead of
            // dropping the local from the environment entirely.
            let sort = ty_to_expr_sort_enriched(self.tcx, body.local_decls[local].ty);
            let fallback_name = source_name_for_local(body, local, self.ctx.arg_names)
                .unwrap_or_else(|| format!("_{}", local.as_u32()));
            self.local_exprs
                .insert(local, PureExpr::Var(fallback_name, sort));
        }
    }

    fn on_assign_projected(
        &mut self,
        place: &rustc_middle::mir::Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        body: &Body<'tcx>,
        location: Location,
    ) {
        // Non-deref projected write (e.g., `x.0[0] = 5`): record
        // equality fact for injection at cutoff. (#1394)
        self.handle_projected_write(place, rvalue, body, location);
    }

    fn on_assign_deref_projected(
        &mut self,
        place: &rustc_middle::mir::Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        body: &Body<'tcx>,
        location: Location,
    ) {
        // Deref projected write (e.g., `**b = expr`): resolve the
        // deref chain through local_exprs to find the base variable,
        // then record as an equality fact. (#1277)
        self.handle_projected_write(place, rvalue, body, location);
    }

    fn check_cutoff_at_statement(&self, span: Span, location: Location) -> Option<PureExpr> {
        if cutoff_reached_at_statement(
            span,
            self.ctx.cutoff_span,
            self.ctx.cutoff_location,
            location.block,
            location.statement_index,
        ) {
            Some(self.cutoff_marker())
        } else {
            None
        }
    }

    fn check_cutoff_at_terminator(
        &self,
        span: Span,
        block: BasicBlock,
        statement_count: usize,
    ) -> Option<PureExpr> {
        if cutoff_reached_at_terminator(
            span,
            self.ctx.cutoff_span,
            self.ctx.cutoff_location,
            block,
            statement_count,
        ) {
            Some(self.cutoff_marker())
        } else {
            None
        }
    }

    fn on_return(&self, _body: &Body<'tcx>) -> Option<PureExpr> {
        self.local_exprs
            .get(&Local::from_u32(0))
            .map(normalize_return_expr)
    }

    fn on_assert(
        &mut self,
        cond: &Operand<'tcx>,
        expected: bool,
        msg: &rustc_middle::mir::AssertKind<Operand<'tcx>>,
        target: BasicBlock,
        body: &Body<'tcx>,
    ) -> block_visitor::VisitorAction<PureExpr> {
        // MIR Assert only continues to `target` on success, so the
        // translated condition is sound to assume downstream.
        let assert_fact = assert_fact_from_condition(cond, expected, msg, &self.local_exprs);

        let local_exprs = std::mem::take(&mut self.local_exprs);
        let visited = std::mem::take(&mut self.visited);
        let projected_write_facts = std::mem::take(&mut self.projected_write_facts);

        let continuation = extract_from_block_with_context(
            self.tcx,
            body,
            target,
            local_exprs,
            visited,
            self.ctx,
            self.effects,
        );
        // Propagate projected write facts across block boundary. (#1444)
        let continuation = wrap_projected_facts(projected_write_facts, continuation);
        block_visitor::VisitorAction::Done(wrap_continuation_with_assert_fact(
            assert_fact,
            continuation,
            self.effects,
        ))
    }

    fn on_switch_int(
        &mut self,
        discr: &Operand<'tcx>,
        targets: &SwitchTargets,
        body: &Body<'tcx>,
        bb: BasicBlock,
    ) -> block_visitor::VisitorAction<PureExpr> {
        // Per-borrow carriers (#124): armed expiry facts are emitted
        // branch-unconditionally at walk end, so any branch exploration
        // disarms them for the rest of the pass (fail-closed).
        super::borrow_carriers::note_branching();
        if targets.all_targets().len() < 2 {
            self.ctx.record_diag(
                "extract/primary.rs",
                ExtractionDiagKind::UnsupportedSwitchShape,
                "SwitchInt has fewer than two targets",
                Some(Location {
                    block: bb,
                    statement_index: body.basic_blocks[bb].statements.len(),
                }),
            );
            return block_visitor::VisitorAction::bail();
        }

        // When the discriminant operand can't be translated, fail
        // extraction rather than guessing a branch. (#1651)
        // The detailed translation path records the specific failure
        // reason (e.g., "missing local expression") in the diagnostic
        // sink, so no generic extractor-level message is needed.
        let term_location = Location {
            block: bb,
            statement_index: body.basic_blocks[bb].statements.len(),
        };
        let diag_ctx = self.ctx.translation_diag(Some(term_location));
        let Some(condition) =
            translate_operand_detailed(discr, &self.local_exprs, diag_ctx.as_ref())
        else {
            return block_visitor::VisitorAction::bail();
        };

        let local_exprs = std::mem::take(&mut self.local_exprs);
        let visited = std::mem::take(&mut self.visited);
        let projected_write_facts = std::mem::take(&mut self.projected_write_facts);

        // Boolean SwitchInt (#485, #497)
        let result = if operand_is_bool(discr, body) {
            handle_bool_switch_with_context(
                self.tcx,
                body,
                condition,
                targets,
                BoolSwitchState {
                    bb,
                    local_exprs,
                    visited,
                    projected_write_facts,
                },
                self.ctx,
                self.effects,
            )
        } else {
            // Integer/enum SwitchInt (#1266)
            if let Some(discr_int_ty) = operand_int_ty(discr, body) {
                handle_int_switch_with_context(
                    self.tcx,
                    body,
                    &condition,
                    targets,
                    IntSwitchState {
                        discr_int_ty,
                        local_exprs,
                        visited,
                        projected_write_facts,
                    },
                    self.ctx,
                    self.effects,
                )
            } else {
                self.ctx.record_diag(
                    "extract/primary.rs",
                    ExtractionDiagKind::FeatureGap,
                    format!("failed to classify integer SwitchInt discriminant: {discr:?}"),
                    Some(Location {
                        block: bb,
                        statement_index: body.basic_blocks[bb].statements.len(),
                    }),
                );
                None
            }
        };
        block_visitor::VisitorAction::Done(result)
    }

    fn on_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
        destination: rustc_middle::mir::Place<'tcx>,
        target: Option<BasicBlock>,
        body: &Body<'tcx>,
        bb: BasicBlock,
    ) -> block_visitor::VisitorAction<PureExpr> {
        let Some(next_bb) = target else {
            // Diverging call (target: None) — the callee never returns.
            // This is normal MIR for panic!, abort, or drop glue in cleanup
            // blocks. No value to extract; bail silently. (#2333)
            return block_visitor::VisitorAction::bail();
        };

        // Per-borrow carriers (#124): a `&mut` local moved into a call is
        // consumed — its expiry becomes the callee contract's to resolve, so
        // any caller-side pending fact is disarmed (fail-closed either way).
        super::borrow_carriers::note_call_arg_moves(body, args);

        let local_exprs = std::mem::take(&mut self.local_exprs);
        let visited = std::mem::take(&mut self.visited);
        let mut projected_write_facts = std::mem::take(&mut self.projected_write_facts);

        // Invalidate projected-write facts for places that may be modified
        // through &mut arguments to the callee. Without this, stale facts
        // (e.g., `tuple_get_0(pair) == 5`) survive calls that mutate the
        // referenced path, producing vacuous verification. (#1535)
        if !projected_write_facts.is_empty() {
            for arg in args {
                let place = match &arg.node {
                    Operand::Copy(p) | Operand::Move(p) => p,
                    // RuntimeChecks, like Constant, references no place/local.
                    Operand::Constant(_) | Operand::RuntimeChecks(_) => continue,
                };
                if place.projection.is_empty()
                    && matches!(
                        body.local_decls[place.local].ty.kind(),
                        rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
                    )
                {
                    if let Some(referent_expr) = local_exprs.get(&place.local) {
                        invalidate_overlapping_projected_write_facts(
                            &mut projected_write_facts,
                            referent_expr,
                        );
                    } else {
                        // Can't trace the mutable borrow's referent;
                        // conservatively clear all projected-write facts.
                        projected_write_facts.clear();
                        break;
                    }
                }
            }
        }

        let mut call_effects = CallEffects::new();
        let mut session = ExtractionSession::new(self.ctx.extern_specs, &mut call_effects);
        let result = handle_call_terminator(
            self.tcx,
            body,
            bb,
            func,
            args,
            destination,
            next_bb,
            local_exprs,
            visited,
            self.ctx,
            &mut session,
            &projected_write_facts,
            self.effects,
        );
        // Merge call-site assumptions/obligations into the parent
        // effects so they propagate to the backward-compatibility
        // flush in extract_return_expr_impl. Without this, specs
        // applied during handle_call_terminator (e.g., Vec::push
        // postconditions) are lost when the local call_effects is
        // dropped. (#1934)
        self.effects.assumptions.extend(call_effects.assumptions);
        self.effects.obligations.extend(call_effects.obligations);
        self.effects
            .mut_ref_result_receivers
            .extend(call_effects.mut_ref_result_receivers);
        block_visitor::VisitorAction::Done(result)
    }

    fn on_goto(&mut self, target: BasicBlock) -> block_visitor::VisitorAction<PureExpr> {
        // Goto targeting a loop header can happen with `loop {}` or
        // body-break while-loops. Only skip when the target is NOT already
        // visited (first entry, not a back-edge). Back-edges are handled
        // by the walker's cycle detection. (#2698)
        if !self.visited.contains(&target) {
            match self.ctx.find_loop_exit_for_extraction(target, self.body) {
                LoopExitResolution::Exit(exit_bb) => {
                    self.mark_loop_body_visited(target);
                    return block_visitor::VisitorAction::Continue(exit_bb);
                }
                LoopExitResolution::Infinite => {
                    self.mark_loop_body_visited(target);
                    return block_visitor::VisitorAction::bail();
                }
                LoopExitResolution::NotALoopHeader => {}
            }
        }
        block_visitor::VisitorAction::Continue(target)
    }

    fn on_false_edge(&mut self, real_target: BasicBlock) -> block_visitor::VisitorAction<PureExpr> {
        // When the extraction pipeline encounters a FalseUnwind targeting
        // a loop header, skip the entire loop body and continue from the
        // exit block. Without this, the walker enters the loop body, hits
        // the back-edge, and reports ControlFlowCycle — failing extraction
        // for any function containing a loop in its return path. (#2698)
        self.skip_loop_or_continue(real_target)
    }

    fn wrap_successor_result(&mut self, result: Option<PureExpr>) -> Option<PureExpr> {
        // Wrap projected write facts from this block around the successor's
        // result so proof_assert cutoffs in later blocks can see writes from
        // earlier blocks. (#1444)
        let facts = std::mem::take(&mut self.projected_write_facts);
        wrap_projected_facts(facts, result)
    }

    fn on_cycle(&mut self, block: BasicBlock) {
        if self.block_is_in_known_loop_body(block) {
            return;
        }
        self.ctx.record_diag(
            "extract/block_visitor.rs",
            ExtractionDiagKind::ControlFlowCycle,
            format!("revisited basic block {block:?}"),
            Some(Location {
                block,
                statement_index: 0,
            }),
        );
    }

    fn on_unsupported_statement(
        &mut self,
        kind: &rustc_middle::mir::StatementKind<'tcx>,
        location: Location,
    ) {
        // Per-borrow carriers (#124): the walk's model is incomplete —
        // disarm all pending expiry facts (fail-closed).
        super::borrow_carriers::note_unsupported();
        self.ctx.record_diag(
            "extract/block_visitor.rs",
            ExtractionDiagKind::UnsupportedStatement,
            format!("unsupported MIR statement: {kind:?}"),
            Some(location),
        );
    }

    fn on_unsupported_terminator(&mut self, kind: &TerminatorKind<'tcx>, location: Location) {
        super::borrow_carriers::note_unsupported();
        self.ctx.record_diag(
            "extract/block_visitor.rs",
            ExtractionDiagKind::UnsupportedTerminator,
            format!("unsupported MIR terminator: {kind:?}"),
            Some(location),
        );
    }
}

/// Recursively extract the return expression with `TyCtxt` for function call support.
///
/// Delegates to [`block_visitor::walk_block`] with a [`PrimaryVisitor`]
/// for statement dispatch and simple terminator routing. Complex terminators
/// (SwitchInt, Call, Assert) are handled by the visitor's callbacks, which
/// may recurse back into this function.
pub(in crate::mir_analysis) fn extract_from_block_with_context<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    local_exprs: HashMap<Local, PureExpr>,
    visited: HashSet<BasicBlock>,
    ctx: &BlockExtractionContext<'_>,
    effects: &mut CallEffects,
) -> Option<PureExpr> {
    let mut visitor = PrimaryVisitor {
        tcx,
        body,
        local_exprs,
        projected_write_facts: Vec::new(),
        visited,
        ctx,
        effects,
    };
    block_visitor::walk_block(body, bb, &mut visitor)
}

fn normalize_return_expr(expr: &PureExpr) -> PureExpr {
    match expr {
        // Strip `Deref(Var(_, MutRef(Inner)))` when the inner type is a
        // *non-reference* scalar/datatype, so the result expression names the
        // borrow itself (`Var("v", MutRef(Inner))`) instead of an unnecessary
        // `Deref` wrapper. The mut-borrow result binder then aliases
        // `result_current`/`result_final` directly to `v_current`/`v_final`.
        //
        // For nested mutable references (`Inner == MutRef(_)`, e.g.,
        // `&mut &mut u32`), the function body `*x` returns the *inner* mut ref,
        // not the outer borrow. Stripping the Deref here would lose that
        // distinction and force the result binder to treat the outer borrow as
        // the return value, causing a sort/depth conflict with the inner
        // reborrow that the postcondition references via `*result`/`^result`
        // (the `unnest` pattern, #5).
        PureExpr::Deref(inner)
            if matches!(
                inner.as_ref(),
                PureExpr::Var(_, Some(ExprSort::MutRef(nested))) if !matches!(**nested, ExprSort::MutRef(_))
            ) =>
        {
            inner.as_ref().clone()
        }
        PureExpr::LogicFnCall { name, args }
            if tuple_field_logic_fn_index(name) == Some(0)
                && args.len() == 1
                && is_scalar_return_tuple_projection_payload(&args[0]) =>
        {
            args[0].clone()
        }
        _ => expr.clone(),
    }
}

fn is_scalar_return_tuple_projection_payload(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::Int(_)
            | PureExpr::Bool(_)
            | PureExpr::Float(_)
            | PureExpr::BinOp(..)
            | PureExpr::UnOp(..)
            | PureExpr::Ite(..)
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn receiver_for_mut_ref_result_write_extracts_receiver_from_final_link() {
        let receiver = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("pair".to_string(), None)],
        };
        let lhs = PureExpr::Deref(Arc::new(PureExpr::Var("call_16".to_string(), None)));
        let mut effects = CallEffects::new();
        effects.assumptions.push(PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "call_16".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::View(Arc::new(PureExpr::Final(Arc::new(
                receiver.clone(),
            ))))),
        ));

        assert_eq!(
            receiver_for_mut_ref_result_write(&lhs, &effects),
            Some(receiver)
        );
    }

    #[test]
    fn receiver_for_mut_ref_result_write_prefers_recorded_receiver_map() {
        let receiver = PureExpr::Var("p".to_string(), None);
        let lhs = PureExpr::Deref(Arc::new(PureExpr::Var("call_16".to_string(), None)));
        let mut effects = CallEffects::new();
        effects
            .mut_ref_result_receivers
            .insert("call_16".to_string(), receiver.clone());

        assert_eq!(
            receiver_for_mut_ref_result_write(&lhs, &effects),
            Some(receiver)
        );
    }

    #[test]
    fn receiver_for_mut_ref_result_write_ignores_unrelated_assumptions() {
        let lhs = PureExpr::Deref(Arc::new(PureExpr::Var("call_16".to_string(), None)));
        let mut effects = CallEffects::new();
        effects.assumptions.push(PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "call_16".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(2)),
        ));

        assert_eq!(receiver_for_mut_ref_result_write(&lhs, &effects), None);
    }

    #[test]
    fn normalize_return_expr_strips_scalar_tuple_get_0_arithmetic_artifact() {
        let scalar_body = PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        );
        let extracted = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![scalar_body.clone()],
        };

        assert_eq!(normalize_return_expr(&extracted), scalar_body);
    }

    #[test]
    fn normalize_return_expr_preserves_named_tuple_projection() {
        let projected = PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![PureExpr::Var("pair".to_string(), None)],
        };

        assert_eq!(normalize_return_expr(&projected), projected);
    }

    /// Stripping a `Deref` from `Var(_, MutRef(Int))` (returning a non-mut-ref
    /// value through a `&mut Int`) is the simple case the normalizer was added
    /// for; keep behavior here.
    #[test]
    fn normalize_return_expr_strips_deref_for_scalar_inner_mut_ref() {
        let deref = PureExpr::Deref(Arc::new(PureExpr::Var(
            "x".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        )));
        let expected = PureExpr::Var(
            "x".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        );
        assert_eq!(normalize_return_expr(&deref), expected);
    }

    /// For nested mut refs (`&mut &mut Int`), the function body `*x` returns
    /// the inner mut ref, not the outer borrow. Stripping the outer `Deref`
    /// would lose that distinction and force the result binder to treat the
    /// outer borrow as the return value, causing a sort/depth conflict with
    /// the inner reborrow the postcondition references via `*result`/`^result`
    /// (the `unnest` pattern, #5).
    #[test]
    fn normalize_return_expr_preserves_deref_for_nested_mut_ref() {
        let inner_mutref = ExprSort::MutRef(Box::new(ExprSort::Int));
        let outer_mutref = ExprSort::MutRef(Box::new(inner_mutref));
        let deref = PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), Some(outer_mutref))));
        assert_eq!(normalize_return_expr(&deref), deref);
    }
}
