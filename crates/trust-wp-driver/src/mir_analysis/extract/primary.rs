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
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::Span;
use trust_wp_core::{
    closure::CaptureInvariant,
    formula::{
        internal::tuple_lowering::{
            tuple_field_logic_fn_index, tuple_field_logic_fn_name, tuple_logic_fn_arity,
            tuple_logic_fn_name,
        },
        BinOp, ExprSort, PureExpr,
    },
};
use trust_wp_driver::StdSpec;

use super::{
    super::{
        diagnostics::{record_extraction_diag, ExtractionDiagKind, ExtractionDiagnosticSink},
        effects::{fail_closed_marker, CallEffects, ExtractionSession},
        loops::LoopAnalysis,
        translate::{
            operand_int_ty, operand_is_bool, project_field_for_read, translate_operand_detailed,
            ty_to_expr_sort_enriched, TranslationDiagContext,
        },
    },
    assertion::{
        arithmetic_panic_obligation, assert_fact_from_condition, operator_call_obligation,
        wrap_continuation_with_assert_fact,
    },
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
        capture_const_body_obligations, expr_references_var_name,
        invalidate_overlapping_projected_write_facts, record_projected_write_fact,
        source_name_for_local, translate_projected_write_lhs, translate_rvalue_with_enum_variants,
        wrap_projected_facts,
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
    /// Lazily computed post-loop merge havoc for skipped loops (wp-s41 v2).
    pub(super) skipped_loop_merges: std::cell::OnceCell<super::loop_merges::SkippedLoopMerges>,
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

        // The resolved exit arm of the loop condition; the same edge the
        // post-loop merge havoc treats as the walked exit (loop_merges.rs).
        match super::loop_merges::loop_exit_edge(body, loop_info) {
            Some((_, exit_bb)) => LoopExitResolution::Exit(exit_bb),
            None => LoopExitResolution::Infinite,
        }
    }

    /// Post-loop merge havoc facts for this body's loops (wp-s41 v2).
    pub(super) fn skipped_loop_merges(
        &self,
        body: &Body<'_>,
    ) -> &super::loop_merges::SkippedLoopMerges {
        self.skipped_loop_merges
            .get_or_init(|| match self.loop_analysis {
                Some(analysis) => super::loop_merges::compute_skipped_loop_merges(
                    body,
                    analysis,
                    self.arg_names.len(),
                ),
                None => super::loop_merges::SkippedLoopMerges::default(),
            })
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
    /// Emit the precondition obligations of a call that never returns
    /// (`target: None`). Postconditions are irrelevant (no continuation).
    ///
    /// A callee with no resolvable spec adds nothing here: a panic entry point
    /// or a spec-less `-> !` callee is classified by `is_panic_entry_point`
    /// and its arm must be proved unreachable by the switch lanes / body-entry
    /// rule instead.
    fn push_diverging_call_preconditions(
        &mut self,
        func: &Operand<'tcx>,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
        destination: rustc_middle::mir::Place<'tcx>,
        body: &Body<'tcx>,
        bb: BasicBlock,
    ) {
        if self.ctx.cutoff_span.is_some() || self.ctx.cutoff_location.is_some() {
            // proof_assert slices: the function-level extraction owns call
            // obligations.
            return;
        }
        let tcx = self.tcx;
        let resolved = super::call_resolve_shared::resolve_call(
            tcx,
            body,
            bb,
            func,
            args,
            destination.local,
            self.ctx.user_specs,
            self.ctx.trait_specs,
            self.ctx.extern_specs,
            self.ctx.diagnostics,
            &self.local_exprs,
        );
        let spec = match resolved.kind {
            super::call_resolve_shared::ResolvedCallKind::DirectSpec(spec)
            | super::call_resolve_shared::ResolvedCallKind::ExternSpec(spec) => Some(spec),
            _ => None,
        };
        if spec.as_ref().is_none_or(|spec| spec.requires.is_empty()) {
            // No precondition reached us through call resolution. A diverging
            // call that is NOT a trusted inert spin is a panic leaf: its arm
            // is proved unreachable by the switch lanes / body-entry rule,
            // which subsumes any precondition. A trusted inert spin, however,
            // is assumed away — so if its concrete resolved callee (e.g. a
            // trait impl reached with concrete generic args) or the called
            // item carries a `requires` that resolution did not surface, fail
            // closed rather than drop it.
            if let Some(resolved_callee) =
                super::helpers::trusted_inert_spin_callee(tcx, body, func)
            {
                let has_requires = |def_id: rustc_hir::def_id::DefId| {
                    self.ctx
                        .user_specs
                        .get(&def_id)
                        .or_else(|| self.ctx.trait_specs.get(&def_id))
                        .is_some_and(|spec| !spec.requires.is_empty())
                };
                if has_requires(resolved_callee) || resolved.def_id.is_some_and(has_requires) {
                    self.effects
                        .record_injected_fail_closed_obligation("inert-spin-unsurfaced-requires");
                }
            }
            return;
        }
        let spec = spec.expect("checked non-empty requires above");
        let mut translated_args = super::call_args::translate_call_args_for_substitutions_with_tcx(
            args,
            &self.local_exprs,
            Some(body),
            Some(tcx),
        );
        let Some(def_id) = resolved.def_id else {
            // A spec with preconditions but no callee identity: fail closed.
            self.effects
                .record_injected_fail_closed_obligation("callee-identity-unknown");
            return;
        };
        let mut param_names = super::super::call_resolve::resolve_arg_names_or_warn(
            tcx,
            def_id,
            spec.param_names.as_ref(),
        );
        super::call_resolve_util::extend_call_with_const_generic_args(
            tcx,
            def_id,
            func,
            &mut translated_args,
            &mut param_names,
        );
        let param_names = (!param_names.is_empty()).then_some(param_names.as_slice());
        super::super::spec_apply::apply_preconditions_with_effects(
            &spec.requires,
            &translated_args,
            param_names,
            &mut *self.effects,
        );
    }

    /// Charge the enclosing body for the type invariants a closure's captures
    /// are granted.
    ///
    /// Building a closure is a hand-over: the closure's body is verified
    /// holding `inv(capture)` for every entry in its spec's
    /// `capture_inv_requires`, and this is the code that makes the builder pay
    /// for them, exactly as a call site pays for a callee's `inv_requires`.
    /// Without it a value the enclosing function BUILT could carry a premise
    /// stating something false into the body, and out again through the
    /// body's postcondition (D-66).
    ///
    /// The obligation is raised over the VALUE handed to the environment — the
    /// aggregate operand at the capture's own index — so a caller-built
    /// aggregate meets the same unfolding a call-site obligation does, and a
    /// capture that is the enclosing function's own parameter discharges
    /// against the premise it already holds.
    ///
    /// Fail closed: an operand that is missing or does not translate is a
    /// clause that cannot be stated, never a clause that can be skipped.
    fn charge_closure_capture_invariants(
        &mut self,
        closure_def_id: DefId,
        operands: &rustc_index::IndexSlice<rustc_abi::FieldIdx, rustc_middle::mir::Operand<'tcx>>,
        location: Location,
    ) {
        let Some(spec) = self.ctx.user_specs.get(&closure_def_id) else {
            // No table entry means no grant: `build_closure_capture_info`
            // reads the premises out of this same table.
            return;
        };
        if spec.capture_inv_requires.is_empty() {
            return;
        }
        let diag = self.ctx.translation_diag(Some(location));
        for capture_inv in &spec.capture_inv_requires {
            let translated = operands
                .get(rustc_abi::FieldIdx::from_usize(capture_inv.index()))
                .and_then(|operand| {
                    translate_operand_detailed(operand, &self.local_exprs, diag.as_ref())
                });
            match translated {
                // Reduced before the clause is built: a capture of `p.1` hands
                // over a PROJECTION of the aggregate the body wrote, and only
                // the reduced form is the constructor application the
                // obligation's unfold (D-65) can meet.
                // Reduced before the clause is built: a capture of `p.1` hands
                // over a PROJECTION of the aggregate the body wrote, and only
                // the reduced form is the constructor application the
                // obligation's unfold (D-65) can meet. A bare variable takes
                // the ENVIRONMENT SLOT's sort, which is the sort the premise
                // the closure is granted carries; an unannotated receiver
                // reaches the solver through a coercion bridge instead of
                // matching it.
                Some(value) => {
                    self.effects
                        .record_user_written_obligation(capture_inv.clause_over(
                            annotate_capture_receiver(
                                value.substitute(&HashMap::new()),
                                capture_inv,
                            ),
                        ))
                }
                None => self.effects.record_dropped_clause(
                    super::super::effects::DroppedClauseKind::Precondition,
                    format!("closure capture type invariant: {}", capture_inv.method()),
                    format!(
                        "capture {} ({}) has no translatable environment operand",
                        capture_inv.index(),
                        capture_inv.name()
                    ),
                ),
            }
        }
    }

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

    /// The walk jumps over a loop body to its exit, so every value the loop may
    /// change must stop denoting its pre-loop value (wp-s41: `let mut x = 0;
    /// while x < 5 { x += 1 } x` proved `result == 0`). Every local the loop
    /// region writes — body, break paths and in-loop return paths
    /// (`loop_merges::loop_region`), parameters whose own storage is written
    /// included — is re-bound to a fresh variable (Creusot's `invariant true`
    /// havoc; `requires` keeps constraining a parameter's entry name).
    /// Projected-write facts are dropped, and a loop that may write through a
    /// pointer disarms the pending borrow expiry facts. Paths that leave the
    /// loop other than through the resolved exit are joined by
    /// [`Self::havoc_at_loop_merge`].
    fn havoc_skipped_loop_state(&mut self, header: BasicBlock) {
        let Some(analysis) = self.ctx.loop_analysis else {
            return;
        };
        let Some(loop_info) = analysis.loops.iter().find(|li| li.header == header) else {
            return;
        };
        let region = super::loop_merges::loop_region(self.body, loop_info)
            .unwrap_or_else(|| loop_info.body_blocks.clone());
        let (written, pointer_write) =
            super::loop_merges::region_effects(self.body, self.ctx.arg_names.len(), &region);
        let mut written: Vec<Local> = written.into_iter().collect();
        written.sort();
        self.havoc_locals(&written, pointer_write, "exit");
    }

    fn havoc_locals(&mut self, locals: &[Local], pointer_write: bool, tag: &str) {
        for &local in locals {
            let index = local.as_usize();
            let sort = ty_to_expr_sort_enriched(self.tcx, self.body.local_decls[local].ty);
            let name = super::unannotated_loops::fresh_name(&format!("{tag}{index}"));
            self.local_exprs.insert(local, PureExpr::Var(name, sort));
        }
        self.projected_write_facts.clear();
        if pointer_write {
            super::borrow_carriers::note_unsupported();
        }
    }

    /// Entering a block where a path that left a skipped loop other than
    /// through its resolved exit (a `break`, an in-loop `return`) joins the
    /// walked continuation: re-bind everything either path may have changed.
    fn havoc_at_loop_merge(&mut self, block: BasicBlock) {
        let Some((locals, pointer_write)) = self
            .ctx
            .skipped_loop_merges(self.body)
            .havoc_at
            .get(&block)
            .cloned()
        else {
            return;
        };
        self.havoc_locals(&locals, pointer_write, "merge");
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
                self.havoc_skipped_loop_state(target);
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
                // A non-deref write's fact is stated over the local's SOURCE
                // name. For a parameter that name is its ENTRY-value symbol,
                // and a shadowed name aliases another local: the fact would
                // constrain the wrong value (`s.0 += 1` on `mut s` asserted
                // `s.0 == s.0 + 1`). The write itself is modelled exactly by
                // the functional update below, so dropping the fact only
                // removes a premise. (s34)
                if has_deref
                    || !projected_fact_name_is_ambiguous(body, place.local, self.ctx.arg_names)
                {
                    record_projected_write_fact(&mut self.projected_write_facts, fact_lhs, rhs);
                }
            }
        }
        if has_deref && !tracked_deref_write {
            super::borrow_carriers::note_projected_deref_write();
        }
        if !has_deref {
            self.apply_local_projected_write(place, rvalue, body, location);
        } else {
            let rd = crate::mir_analysis::reaching_defs::for_body(self.tcx, body);
            match crate::mir_analysis::governed_place::governed_place(
                self.tcx, body, &rd, place, location,
            ) {
                // A write through a borrow of a FIELD (`let r = &mut s.a; *r =
                // 7`) lands on the owner's value exactly as a direct `s.a = 7`
                // would, and the `!has_deref` guard above is what kept it out.
                // Without this the owner keeps its entry value and a
                // postcondition over it is discharged against the pre-write
                // struct.
                //
                // A whole-local target is deliberately left alone: the
                // per-borrow carrier lane already arms and commits that write,
                // and the same fact granted twice by two lanes that cannot see
                // each other is how a grant outlives the obligation that paid
                // for it.
                crate::mir_analysis::governed_place::Governed::Exact(base, path)
                    if !path.is_empty() =>
                {
                    self.apply_local_projected_write_path(
                        base,
                        Some(&path),
                        rvalue,
                        body,
                        location,
                    );
                }
                // The write lands on one of these and the body does not say
                // which, so each of them is havocked and none is told the
                // value. `None` for the path is this lane's spelling of "the
                // owner now holds something this lane cannot represent".
                crate::mir_analysis::governed_place::Governed::Candidates(candidates) => {
                    for (base, _) in candidates {
                        self.apply_local_projected_write_path(base, None, rvalue, body, location);
                    }
                }
                _ => {}
            }
        }
    }

    /// `x.f1..fk = rvalue` on a local (no deref): the local's whole value is
    /// replaced by the functional update of its current value, so later reads
    /// and moves of `x` (`_0 = move x`) see the write. A write that cannot be
    /// represented exactly (non-field projection, single-field carrier whose
    /// value representation is collapsed, unreadable current value,
    /// untranslatable right-hand side) rebinds `x` to a FRESH unconstrained
    /// symbol: never the stale pre-write value, never the source name (which
    /// for a parameter denotes its entry value). (s34)
    fn apply_local_projected_write(
        &mut self,
        place: &rustc_middle::mir::Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        body: &Body<'tcx>,
        location: Location,
    ) {
        let mut path = Vec::with_capacity(place.projection.len());
        for proj in place.projection.iter() {
            // A non-field projection is not representable as a functional
            // update; `None` takes the havoc branch rather than the stale
            // value.
            let ProjectionElem::Field(field, _) = proj else {
                self.apply_local_projected_write_path(place.local, None, rvalue, body, location);
                return;
            };
            path.push(field.as_usize());
        }
        self.apply_local_projected_write_path(place.local, Some(&path), rvalue, body, location);
    }

    /// The write-back itself, over an owner named by `(local, path)` rather
    /// than by the written place: a deref write resolves to one of these, and
    /// a direct projected write IS one. `None` names a path this lane cannot
    /// represent and havocs the owner.
    fn apply_local_projected_write_path(
        &mut self,
        local: Local,
        path: Option<&[usize]>,
        rvalue: &Rvalue<'tcx>,
        body: &Body<'tcx>,
        location: Location,
    ) {
        let local_ty = body.local_decls[local].ty;
        let updated = (|| {
            let path = path?;
            let current = self.local_exprs.get(&local)?.clone();
            let value =
                translate_struct_aggregate_as_tuple(self.tcx, rvalue, &self.local_exprs, None)
                    .or_else(|| {
                        translate_rvalue_with_enum_variants(
                            self.tcx,
                            rvalue,
                            &self.local_exprs,
                            Some(body),
                            None,
                            Some(location),
                        )
                    })?;
            local_functional_update(self.tcx, &self.local_exprs, current, local_ty, path, value)
        })();
        let expr = updated.unwrap_or_else(|| {
            PureExpr::Var(
                format!(
                    "$havoc_local_{}_{}_{}",
                    local.as_u32(),
                    location.block.as_u32(),
                    location.statement_index
                ),
                ty_to_expr_sort_enriched(self.tcx, local_ty),
            )
        });
        self.local_exprs.insert(local, expr);
    }
}

/// Whether a non-deref projected-write fact over `local`'s source name would
/// name a different value: a parameter (its name is the entry-value symbol)
/// or a name shared with another local. (s34)
fn projected_fact_name_is_ambiguous(body: &Body<'_>, local: Local, arg_names: &[String]) -> bool {
    let Some(name) = source_name_for_local(body, local, arg_names) else {
        return false;
    };
    if (1..=body.arg_count).contains(&local.as_usize()) {
        return true;
    }
    body.local_decls.indices().any(|other| {
        other != local && source_name_for_local(body, other, arg_names).as_deref() == Some(&name)
    })
}

/// Functional update of `current` (a value of type `ty`) at field `path` with
/// `value`: `tupleN(get_0(cur), .., upd(get_i(cur), rest), .., get_{N-1}(cur))`,
/// every `get_j` computed exactly as a place read would. `None` when a step is
/// not a record of arity >= 2 (aggregates of arity 1 collapse to their field,
/// so no single representation is shared by reads and writes) or a field of
/// the current value is unreadable. (s34)
pub(super) fn local_functional_update<'tcx>(
    tcx: TyCtxt<'tcx>,
    locals: &HashMap<Local, PureExpr>,
    current: PureExpr,
    ty: Ty<'tcx>,
    path: &[usize],
    value: PureExpr,
) -> Option<PureExpr> {
    let Some((&idx, rest)) = path.split_first() else {
        return Some(value);
    };
    let field_tys: Vec<Ty<'tcx>> = match ty.kind() {
        TyKind::Tuple(fields) => fields.iter().collect(),
        TyKind::Adt(adt_def, substs) if adt_def.is_struct() && !adt_def.is_box() => adt_def
            .non_enum_variant()
            .fields
            .iter()
            .map(|field| field.ty(tcx, *substs).skip_norm_wip())
            .collect(),
        _ => return None,
    };
    if field_tys.len() < 2 || idx >= field_tys.len() {
        return None;
    }
    let mut value = Some(value);
    let mut args = Vec::with_capacity(field_tys.len());
    for (j, field_ty) in field_tys.iter().enumerate() {
        let child = project_field_for_read(current.clone(), j, locals)?;
        if j == idx {
            args.push(local_functional_update(
                tcx,
                locals,
                child,
                *field_ty,
                rest,
                value.take()?,
            )?);
        } else {
            args.push(child);
        }
    }
    Some(PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(args.len()),
        args,
    })
}

/// Whether any assignment of the return place in `body` trips the return sink
/// ([`return_value_reads_stale_store`]) through a store outside `loop_blocks`.
///
/// A function with an annotated loop has its obligations rebuilt from
/// block-scoped walks (`parsing/extraction.rs`), which never see this
/// statement-level sink; the `false` the primary walk pushed for it was
/// dropped, and the loop lane's function-level continuation proved a
/// postcondition over the pre-store value (loop_post_return_mut_borrow_write.rs).
/// The same predicate, over the same statements, carries it there. A store in
/// a loop body is the loop lane's own: its body walk states it and the value
/// returned after the loop is read from the loop's exit state, so such a store
/// alone owes no marker, and a refutation over it stands
/// (closure_param_loop_write_ensures_stale_entry_fact).
pub(crate) fn body_returns_a_stale_store_read<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    loop_blocks: &HashSet<rustc_middle::mir::BasicBlock>,
) -> bool {
    body.basic_blocks.iter_enumerated().any(|(block, data)| {
        data.statements
            .iter()
            .enumerate()
            .any(|(statement_index, stmt)| match &stmt.kind {
                rustc_middle::mir::StatementKind::Assign((place, rvalue))
                    if place.local == rustc_middle::mir::RETURN_PLACE =>
                {
                    return_value_reads_stale_store(
                        tcx,
                        body,
                        rvalue,
                        Location {
                            block,
                            statement_index,
                        },
                        loop_blocks,
                    )
                }
                _ => false,
            })
    })
}

/// Does the value assigned to the return place read, through a reference or
/// from a borrowed local, memory that a store through that reference's alias
/// class may have changed before this point — while the return type carries
/// no reference at all (so the assignment is a read of the pointee, not a
/// handback of the borrow)?
fn return_value_reads_stale_store<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    rvalue: &Rvalue<'tcx>,
    location: Location,
    lane_stated_blocks: &HashSet<rustc_middle::mir::BasicBlock>,
) -> bool {
    let return_ty = body.local_decls[rustc_middle::mir::RETURN_PLACE].ty;
    let may_carry_reference = return_ty.walk().any(|arg| match arg.kind() {
        rustc_middle::ty::GenericArgKind::Lifetime(_) => true,
        rustc_middle::ty::GenericArgKind::Type(ty) => {
            ty.is_ref()
                || ty.is_raw_ptr()
                || ty.is_box()
                || matches!(
                    ty.kind(),
                    TyKind::Param(_)
                        | TyKind::Dynamic(..)
                        | TyKind::Alias(..)
                        | TyKind::Closure(..)
                )
        }
        rustc_middle::ty::GenericArgKind::Const(_) => false,
    });
    if may_carry_reference {
        return false;
    }
    struct Reads<'tcx>(Vec<Place<'tcx>>);
    impl<'tcx> rustc_middle::mir::visit::Visitor<'tcx> for Reads<'tcx> {
        fn visit_place(
            &mut self,
            place: &Place<'tcx>,
            _context: rustc_middle::mir::visit::PlaceContext,
            _location: Location,
        ) {
            self.0.push(*place);
        }
    }
    let mut reads = Reads(Vec::new());
    rustc_middle::mir::visit::Visitor::visit_rvalue(&mut reads, rvalue, location);
    if reads.0.is_empty() {
        return false;
    }
    let mut staleness =
        crate::mir_analysis::deref_store_staleness::DerefStoreStaleness::new(Some(tcx), body)
            .excluding_stores_in(lane_stated_blocks);
    reads.0.into_iter().any(|place| {
        let read_ty = place.ty(&body.local_decls, tcx).ty;
        let reads_through_deref = place
            .projection
            .iter()
            .any(|elem| matches!(elem, ProjectionElem::Deref));
        // A read THROUGH a reference can be redirected by a store into a
        // pointer slot (`*tt = &mut y`) as well as overwritten by a value
        // store, so every store in the class counts. A read of a value local
        // is changed only by a store that writes its type of memory: the
        // pointer-slot store above leaves `x` exactly as it was, and the
        // handback lane already speaks correctly about where `t` points.
        let counts = |store: &Place<'tcx>| -> bool {
            reads_through_deref || store.ty(&body.local_decls, tcx).ty == read_ty
        };
        staleness.operand_may_read_stale_from(&Operand::Copy(place), location, &counts)
    })
}

/// Put a capture receiver in the spelling the closure's own premise uses.
///
/// Two adjustments, both about meeting the premise rather than being bridged
/// past it. A bare variable takes the environment SLOT's sort: the value
/// handed over IS the slot, and an unannotated `Var` reaches the solver
/// through a sort coercion the premise never meets. And a nested closure built
/// inside a closure BODY reads its own capture as the enclosing environment's
/// projection `tuple_get_N(self)`, which denotes the very slot the enclosing
/// closure holds `inv(self.N)` about — the two spellings are one term, and
/// only the projected one is what the premise is written in.
pub(super) fn annotate_capture_receiver(
    value: PureExpr,
    capture_inv: &CaptureInvariant,
) -> PureExpr {
    let sort = Some(capture_inv.sort().clone());
    match value {
        PureExpr::Var(name, None) => PureExpr::Var(name, sort),
        PureExpr::LogicFnCall { ref name, ref args } => {
            let is_self_env = matches!(args.as_slice(), [PureExpr::Var(base, _)] if base == "self");
            match tuple_field_logic_fn_index(name) {
                Some(field) if is_self_env => PureExpr::Var(format!("self.{field}"), sort),
                _ => value,
            }
        }
        other => other,
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
    // A bounds check's `&raw const (fake) *p` reads only `p`'s length, so it
    // denotes what `&*p` does and takes the same translation: the check and a
    // `p.len()` guard over one captured slice read one term.
    let (Rvalue::Ref(_, _, place)
    | Rvalue::RawPtr(rustc_middle::mir::RawPtrKind::FakeForPtrMetadata, place)) = rvalue
    else {
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

/// The placeholder for the value an assignment the walk cannot translate
/// stores into `local`: one symbol per assignment site, or one per value when
/// `untranslated_value_key` names the value the right-hand side computes.
/// Both name the body (`untranslated_body_tag`): locals, blocks and parameters
/// are numbered per body, and a closure or promoted body walked into its
/// host's VC must not share a symbol with the host.
fn untranslated_assignment_symbol<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    local: Local,
    rvalue: &Rvalue<'tcx>,
    location: Location,
    sort: Option<ExprSort>,
) -> PureExpr {
    let name = untranslated_value_key(tcx, body, rvalue).unwrap_or_else(|| {
        format!(
            "$untranslated_{}_{}_{}_{}",
            untranslated_body_tag(body),
            local.as_u32(),
            location.block.as_u32(),
            location.statement_index
        )
    });
    PureExpr::Var(name, sort)
}

/// The body an untranslated symbol belongs to: its item's index in this
/// crate, and its promoted index when it is a promoted constant's body.
fn untranslated_body_tag(body: &Body<'_>) -> String {
    let item = body.source.def_id().index.as_u32();
    match body.source.promoted {
        Some(promoted) => format!("d{item}p{}", promoted.as_u32()),
        None => format!("d{item}"),
    }
}

/// A name for the VALUE an untranslated right-hand side computes, when that
/// value is fixed for the whole execution: an integer-typed cast of a
/// parameter, read directly or through temporaries that only copy it
/// (`_3 = copy _1; _2 = move _3 as usize`), where the operand and every local
/// it depends on is never reassigned nor written behind the walk's back
/// (`switch_discr_is_value_stable`, flow-insensitive). A cast is a function of
/// its operand's value alone, and such a parameter holds its entry value at
/// every read, so every site that casts it the same way computes the same
/// value (`let a = p as usize; .. let a = p as usize;`). The key names the
/// parameter by its index, never by a source name a shadowing binding could
/// share, and carries the cast's kind and target type.
fn untranslated_value_key<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> Option<String> {
    let Rvalue::Cast(kind, operand, target) = rvalue else {
        return None;
    };
    let read = match operand {
        Operand::Copy(place) | Operand::Move(place) => place.as_local()?,
        Operand::Constant(_) | Operand::RuntimeChecks(_) => return None,
    };
    if !target.is_integral()
        || !super::helpers::switch_discr_is_value_stable(tcx, body, operand, true)
    {
        return None;
    }
    let param = parameter_copied_into(body, read)?;
    Some(format!(
        "$untranslated_{}_cast_{kind:?}_{target}_of_arg{}",
        untranslated_body_tag(body),
        param.as_u32()
    ))
}

/// The parameter `local` is, or copies through a chain of temporaries each
/// defined once by a plain copy or move of the next (the flow-insensitive
/// stability test the caller runs refuses a second definition).
fn parameter_copied_into(body: &Body<'_>, mut local: Local) -> Option<Local> {
    let is_param = |local: Local| local.as_usize() >= 1 && local.as_usize() <= body.arg_count;
    for _ in 0..body.local_decls.len() {
        if is_param(local) {
            return Some(local);
        }
        let mut sources = body.basic_blocks.iter().flat_map(|data| {
            data.statements.iter().filter_map(move |statement| {
                let rustc_middle::mir::StatementKind::Assign((place, rvalue)) = &statement.kind
                else {
                    return None;
                };
                (place.local == local).then_some((place, rvalue))
            })
        });
        let (place, rvalue) = sources.next()?;
        if sources.next().is_some() || !place.projection.is_empty() {
            return None;
        }
        let Rvalue::Use(Operand::Copy(source) | Operand::Move(source), _) = rvalue else {
            return None;
        };
        local = source.as_local()?;
    }
    None
}

pub(super) fn translate_struct_aggregate_as_tuple<'tcx>(
    tcx: TyCtxt<'tcx>,
    rvalue: &Rvalue<'tcx>,
    local_exprs: &HashMap<Local, PureExpr>,
    diag: Option<&TranslationDiagContext<'_>>,
) -> Option<PureExpr> {
    let Rvalue::Aggregate(AggregateKind::Adt(def_id, ..), operands) = rvalue else {
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
        if let Rvalue::Aggregate(AggregateKind::Closure(closure_def_id, _), operands) = rvalue {
            self.charge_closure_capture_invariants(*closure_def_id, operands, location);
        }
        if local == rustc_middle::mir::RETURN_PLACE
            && return_value_reads_stale_store(self.tcx, body, rvalue, location, &HashSet::new())
        {
            // prophecy-store, return sink: a store through a local `&mut`
            // borrow (`let r = &mut x; *r = 7;`) leaves both `x` and `*r`
            // bound to the pointee's ENTRY value in this lane, so a
            // postcondition over a returned `x` or `*r` would be checked
            // against the pre-store value. The call-precondition sink of the
            // same read already fails closed; the return sink must too.
            // Only a reference-free return value is a READ of the pointee —
            // returning the borrow itself is the handback lane's business
            // and is left alone. SOUND: an obligation `false` removes an
            // accept path and nothing else.
            self.effects
                .obligations
                .push(fail_closed_marker("prophecy-store-return-sink"));
        }
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
        let (translated, const_body_obligations) = capture_const_body_obligations(|| {
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
        });
        // Inline-const bodies expanded here owe their arithmetic panic
        // obligations at this program point.
        self.effects.obligations.extend(const_body_obligations);
        if let Some(expr) = translated {
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
            //
            // The symbol names this ASSIGNMENT, or the value it computes
            // when that value is fixed for the execution, never the local or
            // its source name: a shadowed binding, a binding in a sibling
            // block and a local named like a parameter share a source name,
            // and a reassigned local keeps its index, so a name-keyed symbol
            // would make a fact about one value (`!(a == 5)` from an early
            // return) a fact about another. One execution of this loop-free
            // walk runs an assignment at most once, so the site is exact.
            let sort = ty_to_expr_sort_enriched(self.tcx, body.local_decls[local].ty);
            // D-143: a clause-free body that binds an opaque value keeps the
            // panic cap. A site symbol removes the sharing that entry names,
            // but the cap stays until a decision lifts it.
            super::panic_site_coverage::record_opaque_binding();
            self.local_exprs.insert(
                local,
                untranslated_assignment_symbol(self.tcx, body, local, rvalue, location, sort),
            );
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
        // A skipped loop returns from a path that never joins the walked
        // continuation: the returned value is unknown here (wp-s41 v2).
        if self.ctx.skipped_loop_merges(self.body).unmerged_return {
            let sort =
                ty_to_expr_sort_enriched(self.tcx, self.body.local_decls[Local::from_u32(0)].ty);
            return Some(PureExpr::Var(
                super::unannotated_loops::fresh_name("return"),
                sort,
            ));
        }
        self.local_exprs
            .get(&Local::from_u32(0))
            .map(normalize_return_expr)
    }

    fn on_drop_place(&mut self, place: &rustc_middle::mir::Place<'tcx>, body: &Body<'tcx>) {
        // A drop whose glue runs an unchecked user `Drop::drop` is a panic site.
        if let Some(obligation) =
            super::assertion::drop_glue_obligation(self.tcx, body, place, self.ctx.user_specs)
        {
            self.effects.obligations.push(obligation);
        }
        // D-140: glue that may write changes whatever the dropped value
        // reaches by reference flow.
        if let Some(changed) =
            super::drop_glue_writes::locals_changed_by_drop(self.tcx, body, place)
        {
            let mut changed: Vec<Local> = changed.into_iter().collect();
            changed.sort();
            self.havoc_locals(&changed, true, "drop");
        }
    }

    fn on_block_enter(&mut self, block: BasicBlock) {
        self.havoc_at_loop_merge(block);
    }

    fn on_assert(
        &mut self,
        cond: &Operand<'tcx>,
        expected: bool,
        msg: &rustc_middle::mir::AssertKind<Operand<'tcx>>,
        target: BasicBlock,
        body: &Body<'tcx>,
    ) -> block_visitor::VisitorAction<PureExpr> {
        // Machine-integer arithmetic panic sites owe a proof obligation at
        // this program point (Creusot's program-function precondition for
        // `add`/`sub`/`mul`/`neg`/`div`/`rem`). Branch guards are applied by
        // the enclosing switch's obligation snapshot.
        // Only where this walk's values are exact (no CFG cycle, no write
        // through a borrow or projection); otherwise the region walks state
        // these obligations with conservative re-binding.
        let exact = super::loop_body::primary_arithmetic_is_exact(self.tcx, body);
        if exact {
            if let Some(obligation) =
                arithmetic_panic_obligation(self.tcx, cond, expected, msg, &self.local_exprs, body)
            {
                self.effects.obligations.push(obligation);
                super::loop_body::record_charged_assert_site(body, msg);
            }
        }
        // MIR Assert only continues to `target` on success, so the
        // translated condition is sound to assume downstream.
        let mut assert_fact = assert_fact_from_condition(cond, expected, msg, &self.local_exprs);
        // Built-in index bounds check: a path-guarded side obligation
        // (enclosing switches guard it via `guard_branch_obligations`). It is
        // stated on every walk; it is RECORDED as charged only where the
        // arithmetic sites are, because only there are this walk's values
        // exact — elsewhere the region walks state it again, conservatively,
        // and their record is the one that counts.
        if let Some(obligation) = super::assertion::bounds_check_obligation(
            self.tcx,
            cond,
            expected,
            msg,
            &self.local_exprs,
            body,
            false,
        ) {
            self.effects.obligations.push(obligation);
            if exact {
                super::loop_body::record_charged_assert_site(body, msg);
            }
        }
        // An assert on a path that can only DIVERGE (e.g. an arm ending in a
        // trusted inert spin) has no continuation to carry its check: the arm
        // is assumed unreachable for the RETURNING path, but the check still
        // runs first. Emit it as an obligation (enclosing switches guard it via
        // `guard_branch_obligations`) and do not assume it — with no
        // continuation the fact would be pushed as an unguarded premise, making
        // the obligation circular.
        if self.ctx.cutoff_span.is_none()
            && self.ctx.cutoff_location.is_none()
            && super::helpers::block_must_diverge(body, target, &mut HashSet::new())
        {
            self.effects
                .obligations
                .push(super::assertion::diverging_path_assert_obligation(
                    self.tcx,
                    body,
                    cond,
                    expected,
                    msg,
                    &self.local_exprs,
                    false,
                ));
            assert_fact = None;
        }

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
                        bb,
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
        // A call that may drop values whose glue runs an unchecked user
        // `Drop::drop` is a panic site (`Vec::<D>::clear`).
        if let Some(obligation) =
            super::assertion::call_type_obligation(self.tcx, body, bb, func, self.ctx.user_specs)
        {
            self.effects.obligations.push(obligation);
        }
        let Some(next_bb) = target else {
            // Diverging call (target: None) — the callee never returns.
            // This is normal MIR for panic!, abort, or drop glue in cleanup
            // blocks. No value to extract. (#2333)
            //
            // The CONTINUATION is unreachable, but the call itself still
            // happens: its precondition is an obligation exactly as for a
            // returning call (Creusot). Without this, `if x <= 0 { die(x) }`
            // with `die: requires(x > 0) -> !` dropped `die`'s precondition.
            self.push_diverging_call_preconditions(func, args, destination, body, bb);
            return block_visitor::VisitorAction::bail();
        };

        // A core operator-trait call on primitive integers (`&u8 + u8`,
        // `u8 += &u8`, ...) panics exactly as the primitive operation does, so
        // it owes the same obligation (see `operator_call_obligation`).
        if super::loop_body::primary_arithmetic_is_exact(self.tcx, body) {
            if let Some(obligation) = operator_call_obligation(
                self.tcx,
                func,
                args,
                destination.ty(&body.local_decls, self.tcx).ty,
                &self.local_exprs,
                body,
            ) {
                self.effects.obligations.push(obligation);
            }
        }

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

        // Flow-sensitive premises (wp(call) = pre && (post ==> Q)): the
        // continuation's effects are recorded into `self.effects` BEFORE this
        // call's own effects are merged below, so the flat lists do not
        // follow program order. Remember what precedes the call.
        let earlier_obligations_guard =
            crate::mir_analysis::effects::conjoin_obligations(&self.effects.obligations);
        let continuation_assumptions_before = self.effects.assumptions.len();
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
        let mut own_assumptions = call_effects.assumptions;
        // prophecy-store: an argument read through a reference after a store
        // through that reference (or an alias) is translated as the pointee's
        // ENTRY value (`Deref(Var(p))` = `p_current`), so the callee's
        // preconditions would be discharged against a stale value. Fail
        // closed: the obligations of this call become `false`.
        let mut call_obligations = call_effects.obligations;
        // wp-s81 v2: the written-`false` count travels with the obligations it
        // describes. `call_effects` is per-call and is dropped here, so a
        // callee's own `#[requires(false)]` would otherwise be indistinguishable
        // from an injected marker by the time the verdict gate looks.
        let mut call_user_written_false = call_effects.user_written_false_obligations;
        if !call_obligations.is_empty() {
            let call_location = Location {
                block: bb,
                statement_index: body.basic_blocks[bb].statements.len(),
            };
            let mut staleness =
                crate::mir_analysis::deref_store_staleness::DerefStoreStaleness::new(
                    Some(self.tcx),
                    body,
                );
            if args
                .iter()
                .any(|arg| staleness.operand_may_read_stale(&arg.node, call_location))
            {
                call_obligations = vec![fail_closed_marker("prophecy-store-call-arg")];
                // The written clauses were DROPPED and replaced by a marker;
                // what remains is trust-wp's, not the user's.
                call_user_written_false = 0;
            }
        }
        // An obligation is proved only from facts established at its own
        // program point: every assumption recorded by the continuation (later
        // calls' postconditions) is guarded by this call's obligations, and
        // this call's own postconditions (already guarded by its own
        // preconditions) by every obligation recorded before the call (a
        // bounds check, an earlier panic arm). `let x = v[0]; nonempty(v);`
        // no longer proves the index from `nonempty`'s `v@.len() > 0`.
        // SOUND: guarding a premise only removes derivations.
        let own_obligations_guard =
            crate::mir_analysis::effects::conjoin_obligations(&call_obligations);
        crate::mir_analysis::effects::guard_assumptions(
            &mut self.effects.assumptions[continuation_assumptions_before..],
            own_obligations_guard.as_ref(),
        );
        crate::mir_analysis::effects::guard_assumptions(
            &mut own_assumptions,
            earlier_obligations_guard.as_ref(),
        );
        self.effects.assumptions.extend(own_assumptions);
        self.effects.obligations.extend(call_obligations);
        self.effects.user_written_false_obligations += call_user_written_false;
        self.effects
            .returning_path_facts
            .extend(call_effects.returning_path_facts);
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
                    self.havoc_skipped_loop_state(target);
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
    let mut local_exprs = local_exprs;
    super::loop_body::rebind_interior_mutable_locals_at_effect_target(
        tcx,
        body,
        bb,
        &mut local_exprs,
    );
    // D-140: a call handed a value whose drop glue may write, by move or by
    // lending access to it, may run that glue; what the value reaches is
    // re-bound on the return edge.
    let handed_off = super::drop_glue_writes::locals_changed_by_call_handoff_into(tcx, body, bb);
    if !handed_off.is_empty() {
        let mut handed_off: Vec<Local> = handed_off.into_iter().collect();
        handed_off.sort();
        for local in handed_off {
            let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
            let name =
                super::unannotated_loops::fresh_name(&format!("handoff{}", local.as_usize()));
            local_exprs.insert(local, PureExpr::Var(name, sort));
        }
        super::borrow_carriers::note_unsupported();
    }
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
