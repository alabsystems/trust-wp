// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! [`BlockVisitor`] implementation for the substitution extraction pipeline.
//!
//! The [`SubstitutionVisitor`] implements the proof-assert substitution
//! extraction using the shared visitor trait from
//! [`crate::mir_analysis::extract::block_visitor`]. Uses the generic
//! [`crate::mir_analysis::extract::block_visitor::walk_block`] with cutoff
//! detection via `check_cutoff_at_*` callbacks. (#2066, Phases 3b+4)

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, Body, Local, Location, Operand, Place, ProjectionElem, Rvalue,
    },
    ty::TyCtxt,
};
use rustc_span::Span;
use trust_wp_core::formula::{internal::tuple_lowering::tuple_logic_fn_arity, ExprSort, PureExpr};

use super::{
    super::{
        super::{
            call_resolve::extract_call_def_id,
            translate::{operand_is_bool, translate_operand, ty_to_expr_sort_enriched},
        },
        block_visitor::{BlockVisitor, VisitorAction},
        borrow_carriers::{expr_is_ground_constant_tree, per_borrow_carrier_expr},
        call_resolve_util::is_box_new_call_path,
        closure::{
            advance_mut_ref_deref_state_for_positions, call_mutates_closure_state,
            call_mutates_via_contract, first_call_arg_is_mut_ref, mut_ref_local_for_operand,
            propagate_mutating_receiver_state_with_captures,
            propagate_mutating_ref_arg_states_for_positions,
            resolved_call_mutating_ref_arg_positions,
        },
        cutoff_reached_at_statement, cutoff_reached_at_terminator,
        helpers::{
            expr_contains_final, source_name_for_local, translate_rvalue_with_enum_variants,
        },
        NameSubstitutions,
    },
    branch_merge::{
        merge_bool_switchint_substitutions, merge_switchint_substitutions, BoolBranchTargets,
    },
    call_resolution::{call_result_expr_for_substitutions, resolve_ref_to_named_local},
    name_bindings::{build_name_substitution_sorts, build_name_substitutions},
    state::block_can_reach_substitution_cutoff,
    SubstitutionCutoff, SubstitutionExtractionContext, SubstitutionState,
};

/// Visitor for the substitution extraction pipeline (Pipeline 3).
///
/// Implements [`BlockVisitor`] to use the shared visitor trait callbacks,
/// eliminating the duplicated statement dispatch from the previous
/// `extract_substitutions_from_block` function. (#2066, Phase 3b)
///
/// Stores a `body` reference so that `check_cutoff_at_statement` and
/// `check_cutoff_at_terminator` can call `build_substitutions(body)`
/// without a custom walker. (#2066, Phase 4)
pub(super) struct SubstitutionVisitor<'a, 'tcx> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) body: &'a Body<'tcx>,
    pub(super) local_exprs: HashMap<Local, PureExpr>,
    pub(super) deref_exprs: HashMap<Local, PureExpr>,
    pub(super) borrow_of: HashMap<Local, Local>,
    pub(super) name_updates: HashMap<String, PureExpr>,
    pub(super) visited: HashSet<BasicBlock>,
    pub(super) cutoff: SubstitutionCutoff,
    pub(super) arg_names: &'a [String],
    pub(super) ctx: &'a SubstitutionExtractionContext<'a, 'tcx>,
    pub(super) saw_cycle: bool,
    pub(super) saw_unsupported: bool,
    /// Closure-environment aggregates seen by THIS visitor: closure local ->
    /// per-field `(capture borrow local, borrow root local)` pairs, the edge
    /// SNAPSHOTTED at aggregate-record time — `StorageDead(<borrow>)` right
    /// after the aggregate erases it from `borrow_of` before the consuming
    /// call is reached. Visitor-local by design: branch exploration
    /// (`on_switch_int`) re-creates visitors without it, so the
    /// closure-capture carrier lane simply stays on the legacy path across
    /// branches (fail-closed). (#closure-capture-carriers)
    pub(super) closure_env_captures: HashMap<Local, Vec<Option<(Local, Local)>>>,
    /// Whole-local move/copy edges (`_5 = move _2`), flow-sensitive (the walk
    /// visits statements in execution order, so last-wins is exact). Used to
    /// resolve a consumed call argument back to the closure aggregate it
    /// copies. (#closure-capture-carriers)
    pub(super) closure_copy_of: HashMap<Local, Local>,
}

impl<'a, 'tcx> SubstitutionVisitor<'a, 'tcx> {
    /// Build the substitution result at the current cutoff point.
    pub(super) fn build_substitutions(&self, body: &Body<'tcx>) -> NameSubstitutions {
        NameSubstitutions::new(
            build_name_substitutions(
                body,
                self.arg_names,
                self.ctx.closure_capture_names.as_deref(),
                &self.local_exprs,
                &self.deref_exprs,
                &self.borrow_of,
                &self.name_updates,
            ),
            build_name_substitution_sorts(self.tcx, body, self.arg_names, &self.local_exprs),
        )
    }

    /// Closure-capture carrier lane (#closure-capture-carriers), Phase A for
    /// the substitution pipeline: rebind the ground-constant-rooted by-`&mut`
    /// capture fields of `closure_local`'s environment to the deterministic
    /// per-borrow MutRef carriers (`per_borrow_carrier_expr`, keyed on the
    /// capture borrow local — the SAME key the primary pipeline mints on, so
    /// goal-side substitutions and assumption-side contract instantiations
    /// meet on one carrier). Returns the `(chain root, carrier)` pairs whose
    /// roots Phase B advances to `Final(<carrier>)` after the capture-state
    /// propagation. Every capture that does not match the exact defect shape
    /// (whole-local `&mut` capture borrow of a ground-constant-valued root,
    /// environment tracked as a matching-arity tuple) keeps the legacy lane
    /// (fail-closed at the encoder).
    fn rebind_closure_capture_carriers(
        &mut self,
        body: &Body<'tcx>,
        closure_local: Local,
    ) -> (Vec<(Local, PureExpr)>, Vec<Local>) {
        let mut advanced = Vec::new();
        // The consumed argument may be a whole-local move/copy of the
        // aggregate (`_5 = move _2`): resolve back to the recorded aggregate,
        // keeping the chain so every alias is rebound consistently.
        let mut env_locals = vec![closure_local];
        let mut seen: HashSet<Local> = HashSet::new();
        let captures = loop {
            let current = *env_locals.last().expect("chain is non-empty");
            if let Some(captures) = self.closure_env_captures.get(&current) {
                break captures.clone();
            }
            if !seen.insert(current) {
                return (advanced, Vec::new()); // cycle — fail closed
            }
            match self.closure_copy_of.get(&current) {
                Some(&source) => env_locals.push(source),
                None => return (advanced, Vec::new()),
            }
        };
        let Some(PureExpr::LogicFnCall { name, args }) =
            self.local_exprs.get(&closure_local).cloned()
        else {
            return (advanced, Vec::new());
        };
        if tuple_logic_fn_arity(&name) != Some(args.len()) || args.len() != captures.len() {
            return (advanced, Vec::new());
        }
        let mut new_args = args.clone();
        let mut minted_any = false;
        for (idx, capture) in captures.iter().enumerate() {
            let Some((borrow_local, root)) = *capture else {
                continue;
            };
            // The defect shape: the capture borrow roots in a local whose
            // tracked value is a ground-constant tree (no carrier identity),
            // and the environment field is either that constant itself or the
            // root's named identity (`Var("x")` from the #746 identity lane).
            let root_is_ground = self
                .local_exprs
                .get(&root)
                .is_some_and(expr_is_ground_constant_tree);
            if !root_is_ground {
                continue;
            }
            let field_matches = match &args[idx] {
                expr if expr_is_ground_constant_tree(expr) => true,
                PureExpr::Var(field_name, _) => {
                    source_name_for_local(body, root, self.arg_names).as_deref()
                        == Some(field_name.as_str())
                }
                _ => false,
            };
            if !field_matches {
                continue;
            }
            let Some(carrier) =
                per_borrow_carrier_expr(self.tcx, body, self.arg_names, borrow_local)
            else {
                continue; // not a `&mut`-typed capture borrow — legacy lane
            };
            new_args[idx] = carrier.clone();
            self.local_exprs.insert(borrow_local, carrier.clone());
            advanced.push((root, carrier));
            minted_any = true;
        }
        if minted_any {
            let rebound_env = PureExpr::LogicFnCall {
                name,
                args: new_args,
            };
            // Rebind the consumed argument local, the aggregate local, and
            // every copy in between, so no alias of the environment keeps the
            // stale pre-carrier fields (the capture post-state propagation
            // reads the environment through these bindings).
            for env_local in &env_locals {
                self.local_exprs.insert(*env_local, rebound_env.clone());
            }
            (advanced, env_locals)
        } else {
            (advanced, Vec::new())
        }
    }

    fn apply_seq_ghost_mutation(
        &mut self,
        body: &Body<'tcx>,
        func: &Operand<'tcx>,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
    ) {
        let Some(def_id) = extract_call_def_id(func) else {
            return;
        };
        let method = match self.tcx.def_path_str(def_id) {
            path if path.ends_with("::push_back_ghost") => "push_back",
            path if path.ends_with("::push_front_ghost") => "push_front",
            _ => return,
        };
        if args.len() != 2 {
            return;
        }

        let Some(receiver_expr) = args
            .first()
            .and_then(|arg| translate_operand(&arg.node, &self.local_exprs))
        else {
            return;
        };
        let Some(receiver_name) = receiver_base_name(&receiver_expr) else {
            return;
        };
        let Some(value_expr) = args
            .get(1)
            .and_then(|arg| translate_operand(&arg.node, &self.local_exprs))
        else {
            return;
        };

        let updated = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var(receiver_name.clone(), Some(ExprSort::Seq))),
            method: method.to_string(),
            args: vec![value_expr],
        };

        let mut updated_local_binding = false;
        let locals: Vec<Local> = self.local_exprs.keys().copied().collect();
        for local in locals {
            if source_name_for_local(body, local, self.arg_names).as_deref() == Some(&receiver_name)
            {
                self.local_exprs.insert(local, updated.clone());
                updated_local_binding = true;
            }
        }
        if !updated_local_binding {
            self.name_updates.insert(receiver_name, updated);
        }
    }
}

fn receiver_base_name(expr: &PureExpr) -> Option<String> {
    match expr {
        PureExpr::Var(name, _) => Some(name.clone()),
        PureExpr::Final(inner) | PureExpr::Deref(inner) | PureExpr::View(inner) => {
            receiver_base_name(inner)
        }
        _ => None,
    }
}

impl<'a, 'tcx> BlockVisitor<'tcx> for SubstitutionVisitor<'a, 'tcx> {
    type Result = NameSubstitutions;

    fn visited_mut(&mut self) -> &mut HashSet<BasicBlock> {
        &mut self.visited
    }

    fn on_cycle(&mut self, _block: BasicBlock) {
        self.saw_cycle = true;
    }

    fn on_assign_local(
        &mut self,
        local: Local,
        rvalue: &Rvalue<'tcx>,
        body: &Body<'tcx>,
        location: Location,
    ) {
        let span = body.basic_blocks[location.block].statements[location.statement_index]
            .source_info
            .span;
        if !self.effect_is_in_region(span) {
            return;
        }
        // Record whole-local copies for the closure-capture carrier lane
        // (#closure-capture-carriers): a consumed call argument is often a
        // move of the aggregate local (`_5 = move _2`).
        if let Rvalue::Use(Operand::Move(src) | Operand::Copy(src), _) = rvalue {
            if src.projection.is_empty() {
                self.closure_copy_of.insert(local, src.local);
            }
        }
        // Record closure-environment aggregates for the capture carrier lane
        // (#closure-capture-carriers). A REASSIGNED closure local is ambiguous
        // — record an empty field list so the arity check at the call site
        // drops it back to the legacy lane (fail-closed).
        if let Rvalue::Aggregate(box AggregateKind::Closure(..), operands) = rvalue {
            let fields: Vec<Option<(Local, Local)>> =
                if self.closure_env_captures.contains_key(&local) {
                    Vec::new()
                } else {
                    operands
                        .iter()
                        .map(|op| match op {
                            Operand::Move(place) | Operand::Copy(place)
                                if place.projection.is_empty() =>
                            {
                                // Snapshot the borrow edge NOW: StorageDead of the
                                // moved-out borrow local erases it before the
                                // consuming call is visited.
                                self.borrow_of
                                    .get(&place.local)
                                    .map(|&root| (place.local, root))
                            }
                            _ => None,
                        })
                        .collect()
                };
            self.closure_env_captures.insert(local, fields);
        }
        // Mutable reference identity tracking (#746): when a mutable
        // reference is created to a source-named local, preserve
        // variable identity through reference chains.
        if let Some(ref_expr) =
            resolve_ref_to_named_local(rvalue, body, self.arg_names, &self.local_exprs, self.tcx)
        {
            self.local_exprs.insert(local, ref_expr);
            // Record borrow chain for both direct borrows and reborrows.
            // Direct: `_2 = &mut _1` (empty projection) tracks _2 → _1.
            // Reborrow: `_3 = &mut (*_2)` (Deref projection) tracks _3 → _2.
            // Both forms are needed so the borrow chain traversal in the
            // Call handler can advance base locals to Final(). (#1581)
            self.record_borrow_chain(local, rvalue);
            return;
        }

        if let Some(expr) = translate_rvalue_with_enum_variants(
            self.tcx,
            rvalue,
            &self.local_exprs,
            Some(body),
            None,
            None,
        ) {
            // Track reborrow chains: _2 = &mut (*_1) means _2 borrows _1.
            // Only record pure Deref reborrows (projection == [Deref]).
            // Field-through-deref reborrows like `_2 = &mut (*_1).field`
            // have projection.len() > 1; recording them would
            // over-approximate deref propagation (#900).
            // (For whole-local assignments, the place has empty projection,
            // but the rvalue may still be a Ref — record the borrow chain.)
            if let Rvalue::Ref(_, _, ref_place) = rvalue {
                if ref_place.projection.len() == 1
                    && matches!(ref_place.projection.first(), Some(ProjectionElem::Deref))
                {
                    self.borrow_of.insert(local, ref_place.local);
                }
            }
            self.local_exprs.insert(local, expr);
        }
    }

    fn on_assign_projected(
        &mut self,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        body: &Body<'tcx>,
        location: Location,
    ) {
        let span = body.basic_blocks[location.block].statements[location.statement_index]
            .source_info
            .span;
        if !self.effect_is_in_region(span) {
            return;
        }
        // Non-deref projected writes (e.g., `_N.field = ...`).
        // Translation must succeed (matching the original guard), but the
        // translated expression is not stored — only the symbolic identity
        // reset below matters for projected writes.
        if translate_rvalue_with_enum_variants(
            self.tcx,
            rvalue,
            &self.local_exprs,
            Some(body),
            None,
            None,
        )
        .is_none()
        {
            return;
        }

        // Track reborrow chains for non-deref projected rvalues.
        if let Rvalue::Ref(_, _, ref_place) = rvalue {
            if ref_place.projection.len() == 1
                && matches!(ref_place.projection.first(), Some(ProjectionElem::Deref))
            {
                self.borrow_of.insert(place.local, ref_place.local);
            }
        }

        // After a projected write (`x.f = ...`), any previously
        // concrete whole-value expression for `x` is stale. Keep a
        // symbolic identity mapping so name substitutions do not
        // inject contradictory stale equalities. (#1500)
        if let Some(name) = source_name_for_local(body, place.local, self.arg_names) {
            let sort = ty_to_expr_sort_enriched(self.tcx, body.local_decls[place.local].ty);
            self.local_exprs
                .insert(place.local, PureExpr::Var(name, sort));
        } else if let Some(existing) = self.local_exprs.get(&place.local) {
            // Fallback for anonymous intermediates (e.g., deref_mut borrow
            // carriers in ghost closure captures): if the local currently
            // holds a compound expression (not a Var), reset it to a fresh
            // symbolic variable so that name-substitution builds don't
            // propagate the stale pre-mutation value. Without this, ghost
            // tuple mutations like `p.0 = 4` where `p` is accessed through
            // a capture intermediate collapse to constant equalities like
            // `(2 == 4)` instead of staying symbolic. (#2533)
            if !matches!(existing, PureExpr::Var(..)) {
                let sort = ty_to_expr_sort_enriched(self.tcx, body.local_decls[place.local].ty);
                let synthetic_name = format!("_local_{}", place.local.as_u32());
                self.local_exprs
                    .insert(place.local, PureExpr::Var(synthetic_name, sort));
            }
        }
    }

    fn on_assign_deref_projected(
        &mut self,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        body: &Body<'tcx>,
        location: Location,
    ) {
        let span = body.basic_blocks[location.block].statements[location.statement_index]
            .source_info
            .span;
        if !self.effect_is_in_region(span) {
            return;
        }
        let Some(expr) = translate_rvalue_with_enum_variants(
            self.tcx,
            rvalue,
            &self.local_exprs,
            Some(body),
            None,
            None,
        ) else {
            return;
        };

        if place.projection.len() == 1 {
            // Single deref write: `(*_N) = expr` (#746 AC1)
            self.handle_single_deref_write(place, &expr, body);
        } else if place.projection.len() == 2
            && matches!(
                (place.projection.first(), place.projection.get(1)),
                (Some(ProjectionElem::Deref), Some(ProjectionElem::Deref))
            )
        {
            // Double-deref write: `(**g2) = expr` through a Ghost<&mut T>
            // or &mut &mut T parameter. The outer deref reaches the inner
            // reference, the inner deref reaches the pointee. Record as a
            // deref substitution on the base variable. (#2671)
            self.handle_double_deref_write(place, &expr, body);
        } else {
            // Projected deref writes: `*p.field = ...`
            self.handle_projected_deref_write(place, &expr);
        }
    }

    fn check_cutoff_at_statement(&self, span: Span, location: Location) -> Option<Self::Result> {
        if cutoff_reached_at_statement(
            span,
            self.cutoff.stop_span,
            self.cutoff.stop_location,
            location.block,
            location.statement_index,
        ) {
            Some(self.build_substitutions(self.body))
        } else {
            None
        }
    }

    fn on_storage_dead(&mut self, local: Local, body: &Body<'tcx>, location: Location) {
        self.handle_storage_dead(local, body, location);
    }

    fn check_cutoff_at_terminator(
        &self,
        span: Span,
        block: BasicBlock,
        statement_count: usize,
    ) -> Option<Self::Result> {
        if cutoff_reached_at_terminator(
            span,
            self.cutoff.stop_span,
            self.cutoff.stop_location,
            block,
            statement_count,
        ) {
            Some(self.build_substitutions(self.body))
        } else {
            None
        }
    }

    fn on_return(&self, _body: &Body<'tcx>) -> Option<Self::Result> {
        // Substitution pipeline produces None at Return — substitutions
        // are only meaningful at cutoff points, not at function return.
        None
    }

    fn on_assert(
        &mut self,
        _cond: &Operand<'tcx>,
        _expected: bool,
        _msg: &rustc_middle::mir::AssertKind<Operand<'tcx>>,
        target: BasicBlock,
        _body: &Body<'tcx>,
    ) -> VisitorAction<Self::Result> {
        // Substitution pipeline treats Assert like Goto — just continue
        // to the target block. The assert condition is irrelevant for
        // name-to-expression substitution maps.
        VisitorAction::Continue(target)
    }

    fn on_switch_int(
        &mut self,
        discr: &Operand<'tcx>,
        targets: &rustc_middle::mir::SwitchTargets,
        body: &Body<'tcx>,
        _bb: BasicBlock,
    ) -> VisitorAction<Self::Result> {
        // Take owned state for recursive branch exploration.
        let local_exprs = std::mem::take(&mut self.local_exprs);
        let deref_exprs = std::mem::take(&mut self.deref_exprs);
        let borrow_of = std::mem::take(&mut self.borrow_of);
        let name_updates = std::mem::take(&mut self.name_updates);
        let visited = std::mem::take(&mut self.visited);

        let st = SubstitutionState {
            local_exprs,
            deref_exprs,
            borrow_of,
            name_updates,
            visited,
        };

        let result = if operand_is_bool(discr, body) {
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
                None
            } else {
                let branches = BoolBranchTargets {
                    then_bb,
                    else_bb,
                    then_reaches: block_can_reach_substitution_cutoff(body, then_bb, &self.cutoff),
                    else_reaches: block_can_reach_substitution_cutoff(body, else_bb, &self.cutoff),
                };
                merge_bool_switchint_substitutions(
                    body,
                    discr,
                    &branches,
                    &st,
                    self.cutoff,
                    self.arg_names,
                    self.ctx,
                )
            }
        } else {
            merge_switchint_substitutions(
                body,
                discr,
                targets,
                &st,
                self.cutoff,
                self.arg_names,
                self.ctx,
            )
        };
        VisitorAction::Done(result)
    }

    fn on_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
        destination: Place<'tcx>,
        target: Option<BasicBlock>,
        body: &Body<'tcx>,
        bb: BasicBlock,
    ) -> VisitorAction<Self::Result> {
        let Some(next_bb) = target else {
            return VisitorAction::bail();
        };
        let terminator_span = body.basic_blocks[bb].terminator().source_info.span;
        if !self.effect_is_in_region(terminator_span) {
            return VisitorAction::Continue(next_bb);
        }

        let mut call_result = call_result_expr_for_substitutions(
            self.ctx,
            body,
            bb,
            &self.local_exprs,
            func,
            args,
            destination.local,
        );
        // Box::new identity override (#2318): when Box::new has an extern spec
        // (ensures: *result == value), the ExternSpec path creates an opaque
        // result variable (call_N) instead of passing through the argument's
        // variable identity. This breaks closure capture chains: the closure
        // env stores Var("call_N") instead of Var("x"), so after FnOnce::call_once,
        // propagate_mutating_receiver_state_with_captures tries to advance
        // "call_N" instead of "x", leaving x at its initial value.
        //
        // Fix: override the opaque result with the argument expression for
        // Box::new calls, and propagate the borrow chain so writes through
        // the Box still alias the original mutable reference.
        if args.len() == 1 {
            if let Some(def_id) = extract_call_def_id(func) {
                let path = self.tcx.def_path_str(def_id);
                if is_box_new_call_path(&path) {
                    if let Some(arg_expr) = translate_operand(&args[0].node, &self.local_exprs) {
                        call_result = arg_expr;
                        // Propagate borrow chain: if the argument local borrows
                        // a source variable, the Box destination should inherit
                        // that chain so the borrow-chain advancement after
                        // FnOnce::call_once can trace back to the original local.
                        if let Operand::Move(place) | Operand::Copy(place) = &args[0].node {
                            if place.projection.is_empty() {
                                let arg_local = place.local;
                                if let Some(&base) = self.borrow_of.get(&arg_local) {
                                    self.borrow_of.insert(destination.local, base);
                                }
                            }
                        }
                    }
                }
            }
        }
        // Per-borrow prophecy carriers, closure-capture lane
        // (#closure-capture-carriers), Phase A — BEFORE the receiver
        // translation below: a state-mutating call consuming a closure whose
        // by-`&mut` captures root in ground-constant locals gets those
        // environment fields rebound to the deterministic per-borrow MutRef
        // carriers, so the capture post-state (`Final(<field>)`) becomes a
        // real prophecy instead of the self-referential `^x` / `^<constant>`.
        let closure_state_mutating = call_mutates_closure_state(self.tcx, func)
            || call_mutates_via_contract(
                self.tcx,
                func,
                self.ctx.user_specs,
                self.ctx.trait_specs,
                self.ctx.extern_specs,
            );
        let mut closure_capture_roots: Vec<(Local, PureExpr)> = Vec::new();
        let mut consumed_env_locals: Vec<Local> = Vec::new();
        if closure_state_mutating {
            for arg in args {
                let (Operand::Move(place) | Operand::Copy(place)) = &arg.node else {
                    continue;
                };
                if !place.projection.is_empty()
                    || !matches!(
                        body.local_decls[place.local].ty.kind(),
                        rustc_middle::ty::TyKind::Closure(..)
                    )
                {
                    continue;
                }
                let (advanced, env_locals) =
                    self.rebind_closure_capture_carriers(body, place.local);
                closure_capture_roots.extend(advanced);
                if matches!(&arg.node, Operand::Move(_)) {
                    consumed_env_locals.extend(env_locals);
                }
            }
        }
        let pre_call_self = args
            .first()
            .and_then(|arg| translate_operand(&arg.node, &self.local_exprs));
        let first_arg_mut_ref = first_call_arg_is_mut_ref(body, args);
        let mutating_ref_positions = resolved_call_mutating_ref_arg_positions(
            self.tcx,
            body,
            bb,
            func,
            args,
            destination.local,
            self.ctx.user_specs,
            self.ctx.trait_specs,
            self.ctx.extern_specs,
            &self.local_exprs,
        );
        propagate_mutating_ref_arg_states_for_positions(
            &mut self.local_exprs,
            body,
            self.arg_names,
            args,
            &mutating_ref_positions,
            None,
            Some(&mut self.name_updates),
        );
        if !first_arg_mut_ref && closure_state_mutating {
            if let Some(ref self_expr) = pre_call_self {
                propagate_mutating_receiver_state_with_captures(
                    &mut self.local_exprs,
                    body,
                    self.arg_names,
                    self_expr,
                    Some(&mut self.name_updates),
                );
            }
        }
        // Closure-capture lane (#closure-capture-carriers), Phase B — AFTER
        // the capture-state propagation: advance each capture borrow's chain
        // root to the borrow's prophecy `Final(<carrier>)`, mirroring the
        // `&mut`-argument chain advancement below (#1581/#124). The consumed
        // capture borrow itself gets no caller-side expiry fact (RustHorn:
        // the callee contract is the sole authority on its prophecy).
        for (root, carrier) in closure_capture_roots {
            if let Some(root_expr) = self.local_exprs.get(&root) {
                if !expr_contains_final(root_expr) {
                    self.local_exprs
                        .insert(root, PureExpr::Final(Arc::new(carrier)));
                }
            }
        }
        // A MOVED environment is dead after the call: drop its bindings
        // (mirroring `handle_storage_dead`) so no name-level fact
        // `clos == tupleN(..^carrier..)` is materialized for it. That fact is
        // information-free here — the callee contract instantiation already
        // owns the environment — and it is MIS-SORTED at the encoder (the
        // receiver-identity lane declares the closure var at its structural
        // ClosureEnv datatype sort, so the tuple side degrades to a fresh
        // coerced constant inside the ClosureEnv congruence class, which the
        // solver's DT model builder refuses fail-closed, degrading the whole
        // obligation to Unknown).
        for env_local in consumed_env_locals {
            self.local_exprs.remove(&env_local);
        }
        // Advance base locals through borrow chains for &mut args (#1581).
        //
        // Per-borrow prophecy carriers (#124): when the base's tracked value
        // has NO variable identity (a ground-constant tree — the locally-
        // rooted borrow shape), wrapping it as `Final(<its own value>)` mints
        // a prophecy over a constant (no carrier — the closed `^<constant>`
        // false accept, now refused fail-closed at the encoder) and CONFLATES
        // distinct borrows (every base wraps its own value, so `^r` and
        // `^r1` collapse onto one shape). Advance such a base to
        // `Final(<carrier of the local that borrows it>)` instead — the
        // prophecy of the borrow that actually governs the base's next
        // value, keyed on the borrow LOCAL. Var-identity bases (the
        // `&mut`-parameter lane) keep the existing advancement unchanged.
        for arg in mutating_ref_positions
            .iter()
            .filter_map(|idx| args.get(*idx))
        {
            if let Some(ref_local) = mut_ref_local_for_operand(body, &arg.node) {
                let mut current = ref_local;
                while let Some(&base) = self.borrow_of.get(&current) {
                    if let Some(base_expr) = self.local_exprs.get(&base).cloned() {
                        if !expr_contains_final(&base_expr) {
                            let advanced = if expr_is_ground_constant_tree(&base_expr) {
                                per_borrow_carrier_expr(self.tcx, body, self.arg_names, current)
                                    .map_or_else(
                                        // No MutRef carrier resolvable: keep
                                        // the legacy shape, which the encoder
                                        // refuses fail-closed.
                                        || PureExpr::Final(Arc::new(base_expr.clone())),
                                        |carrier| PureExpr::Final(Arc::new(carrier)),
                                    )
                            } else {
                                PureExpr::Final(Arc::new(base_expr))
                            };
                            self.local_exprs.insert(base, advanced);
                        }
                    }
                    current = base;
                }
            }
        }
        // Advance deref state for `&mut` args after a call (#1277).
        advance_mut_ref_deref_state_for_positions(
            body,
            args,
            &mutating_ref_positions,
            &self.local_exprs,
            &mut self.deref_exprs,
        );
        self.apply_seq_ghost_mutation(body, func, args);
        // DerefMut::deref_mut borrow chain propagation (#2691): when a
        // `deref_mut` call is detected, connect the destination local to
        // the first argument's local via `borrow_of`. This way, subsequent
        // single-deref writes like `*destination = value` propagate through
        // the borrow chain back to the source variable (e.g., `g2`).
        // Without this, `**g2 = 1` inside ghost blocks (which rustc
        // decomposes into `deref_mut(g2)` + `*result = 1`) would fail to
        // produce the `*g2 → Int(1)` substitution needed for postcondition
        // matching.
        if let Some(def_id) = extract_call_def_id(func) {
            let path = self.tcx.def_path_str(def_id);
            if path.ends_with("::deref_mut") || path.ends_with("::deref") {
                if let Some(first_arg) = args.first() {
                    if let Some(arg_local) = mut_ref_local_for_operand(body, &first_arg.node) {
                        self.borrow_of.insert(destination.local, arg_local);
                    }
                }
            }
        }
        self.local_exprs.insert(destination.local, call_result);
        VisitorAction::Continue(next_bb)
    }

    fn on_unsupported_statement(
        &mut self,
        _kind: &rustc_middle::mir::StatementKind<'tcx>,
        _location: Location,
    ) {
        self.saw_unsupported = true;
    }

    fn on_unsupported_terminator(
        &mut self,
        _kind: &rustc_middle::mir::TerminatorKind<'tcx>,
        _location: Location,
    ) {
        self.saw_unsupported = true;
    }
}
