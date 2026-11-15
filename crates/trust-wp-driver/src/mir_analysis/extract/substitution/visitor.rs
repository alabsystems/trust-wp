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
    call_resolution::{
        call_result_expr_for_substitutions, is_mut_ref_reborrow_place,
        is_trust_wp_std_snapshot_capture, nonfinal_reborrow_carrier, resolve_ref_to_named_local,
    },
    name_bindings::{
        build_name_substitution_sorts, build_name_substitutions, snapshot_frozen_name_values,
    },
    state::block_can_reach_substitution_cutoff,
    SubstitutionCutoff, SubstitutionExtractionContext, SubstitutionState,
};
use crate::mir_analysis::{deref_store_staleness::CurrentState, governed_place::Governed};

/// Whether two expressions are the same variable, whatever sort each
/// carries.
fn same_var(a: &PureExpr, b: &PureExpr) -> bool {
    matches!((a, b), (PureExpr::Var(x, _), PureExpr::Var(y, _)) if x == y)
}

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
    /// The place a borrow chain ends at: follow `borrow_of` from `local` to
    /// the first local with no recorded borrow (`local` itself when it has
    /// none). `None` when any `&mut` link on the way — `local` included —
    /// escapes by reference somewhere in the body: a link whose own address
    /// is taken (`let rr = &mut r; *rr = &mut y;`) can be redirected to a
    /// place this chain never saw, so the chain would speak for the wrong
    /// place. A cycle is cut rather than trusted.
    fn unescaped_borrow_chain_root(&self, body: &Body<'tcx>, local: Local) -> Option<Local> {
        let mut seen = HashSet::new();
        let mut current = local;
        loop {
            if !seen.insert(current) {
                return None;
            }
            let Some(&origin) = self.borrow_of.get(&current) else {
                return Some(current);
            };
            if local_is_mut_ref(body, current) && local_escapes_by_reference(body, current) {
                return None;
            }
            current = origin;
        }
    }

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

    /// D-140: re-bind every local a hand-off may change to a fresh symbol and
    /// forget what this walk recorded about its pointee, so no binding read
    /// before glue that may write is identified with one read after it.
    fn rebind_handed_off(&mut self, body: &Body<'tcx>, changed: HashSet<Local>) {
        let mut changed: Vec<Local> = changed.into_iter().collect();
        changed.sort();
        for local in changed {
            let sort = ty_to_expr_sort_enriched(self.tcx, body.local_decls[local].ty);
            self.local_exprs.insert(
                local,
                PureExpr::Var(
                    super::super::unannotated_loops::fresh_name(&format!(
                        "handoff{}",
                        local.as_usize()
                    )),
                    sort,
                ),
            );
            self.deref_exprs.remove(&local);
            if let Some(name) = source_name_for_local(body, local, self.arg_names) {
                self.name_updates.remove(&format!("*{name}"));
                self.name_updates.remove(&name);
            }
        }
    }

    /// Whether `local` is a parameter of a function item (not a closure,
    /// whose arguments are its environment and its tupled parameters).
    fn is_fn_item_param(&self, local: Local) -> bool {
        (1..=self.body.arg_count).contains(&local.as_usize())
            && !self.tcx.is_closure_like(self.body.source.def_id())
    }

    /// The fresh symbol a parameter is re-bound to by a write at `location`
    /// whose value this walk cannot represent (D-241).
    fn fresh_param_write_symbol(&self, local: Local, location: Location) -> PureExpr {
        PureExpr::Var(
            format!(
                "$param_write_{}_{}_{}",
                local.as_u32(),
                location.block.as_u32(),
                location.statement_index
            ),
            ty_to_expr_sort_enriched(self.tcx, self.body.local_decls[local].ty),
        )
    }

    /// Translate `rvalue` as it reads at `location` (D-185).
    ///
    /// A read through a dereference whose memory no write reaches before
    /// `location` reads the entry value, which is what the plain translation
    /// spells (`Deref(Var x)`). A read of memory a write may have changed takes
    /// the value this walk recorded for it -- only a whole-pointee read `*x`
    /// whose every preceding write is a store `*x = v` through `x` itself, the
    /// writes [`Self::handle_single_deref_write`] records -- and otherwise a
    /// fresh symbol: spelling it `Deref(Var x)` named the entry value, so `let
    /// v = *x` after `*x = 5` bound `v` to the value the write replaced.
    pub(super) fn translate_current_rvalue(
        &self,
        rvalue: &Rvalue<'tcx>,
        body: &Body<'tcx>,
        location: Location,
    ) -> Option<PureExpr> {
        let entry = translate_rvalue_with_enum_variants(
            self.tcx,
            rvalue,
            &self.local_exprs,
            Some(body),
            None,
            None,
        );
        let Some(reads) = self.ctx.written_deref_reads.get(&location) else {
            return entry;
        };
        // The plain translation spells each read `*x` as `Deref(<x's
        // binding>)`, the entry pointee. A recorded read replaces exactly
        // that term with the value the stores left.
        let mut recorded: Vec<(PureExpr, PureExpr)> = Vec::new();
        for (place, state) in reads {
            let pointee = (*state == CurrentState::DirectPointeeStores
                && place.projection.len() == 1)
                .then(|| self.deref_exprs.get(&place.local))
                .flatten();
            let binding = self.local_exprs.get(&place.local);
            match (pointee, binding) {
                (Some(pointee), Some(PureExpr::Var(..))) => {
                    recorded.push((binding.cloned()?, pointee.clone()));
                }
                _ => return Some(self.written_read_symbol(rvalue, body, location)),
            }
        }
        // A recorded read the translation does not spell as that term was
        // spelled some other way, which still names the entry value.
        let mut replaced = vec![false; recorded.len()];
        let current = entry.map(|expr| {
            expr.rewrite_bottom_up(|node| {
                if let PureExpr::Deref(inner) = &node {
                    for (at, (binding, pointee)) in recorded.iter().enumerate() {
                        if same_var(inner, binding) {
                            replaced[at] = true;
                            return pointee.clone();
                        }
                    }
                }
                node
            })
        });
        match current {
            Some(current) if replaced.iter().all(|done| *done) => Some(current),
            _ => Some(self.written_read_symbol(rvalue, body, location)),
        }
    }

    /// A fresh symbol for a value read from memory whose current value this
    /// walk does not know (D-185).
    fn written_read_symbol(
        &self,
        rvalue: &Rvalue<'tcx>,
        body: &Body<'tcx>,
        location: Location,
    ) -> PureExpr {
        let ty = rvalue.ty(&body.local_decls, self.tcx);
        PureExpr::Var(
            format!(
                "$written_read_{}_{}",
                location.block.as_u32(),
                location.statement_index
            ),
            ty_to_expr_sort_enriched(self.tcx, ty),
        )
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

/// The functional update of a parameter's `current` value (of type `ty`) at
/// the field `path` with `value`, spelled the way this walk spells a value of
/// that type built whole (D-241): a struct of two or more fields as its
/// constructor (`P(get_0(cur), value)`, as `translate_rvalue_typed` spells
/// `P { a, b }`), a tuple of two or more fields as `tupleN(..)`. `None` for any
/// other step (an enum, a single-field struct, which this walk collapses to its
/// field, an unreadable field); the caller then binds a fresh symbol.
fn param_field_update<'tcx>(
    tcx: TyCtxt<'tcx>,
    locals: &HashMap<Local, PureExpr>,
    current: PureExpr,
    ty: rustc_middle::ty::Ty<'tcx>,
    path: &[usize],
    value: PureExpr,
) -> Option<PureExpr> {
    use rustc_middle::ty::TyKind;

    let Some((&index, rest)) = path.split_first() else {
        return Some(value);
    };
    let (constructor, field_tys): (String, Vec<rustc_middle::ty::Ty<'tcx>>) = match ty.kind() {
        TyKind::Tuple(fields) => (
            trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(fields.len()),
            fields.iter().collect(),
        ),
        TyKind::Adt(adt_def, args) if adt_def.is_struct() && !adt_def.is_box() => (
            tcx.item_name(adt_def.did()).to_string(),
            adt_def
                .non_enum_variant()
                .fields
                .iter()
                .map(|field| field.ty(tcx, *args).skip_norm_wip())
                .collect(),
        ),
        _ => return None,
    };
    if field_tys.len() < 2 || index >= field_tys.len() {
        return None;
    }
    let mut value = Some(value);
    let mut args = Vec::with_capacity(field_tys.len());
    for (field, field_ty) in field_tys.iter().enumerate() {
        let child =
            super::super::super::translate::project_field_for_read(current.clone(), field, locals)?;
        if field == index {
            args.push(param_field_update(
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
        name: constructor,
        args,
    })
}

impl<'a, 'tcx> BlockVisitor<'tcx> for SubstitutionVisitor<'a, 'tcx> {
    type Result = NameSubstitutions;

    fn visited_mut(&mut self) -> &mut HashSet<BasicBlock> {
        &mut self.visited
    }

    fn on_cycle(&mut self, _block: BasicBlock) {
        self.saw_cycle = true;
    }

    /// Entering the header of a loop the cutoff lies in: every local the loop
    /// may change holds the value a back edge carried in, not the value it had
    /// before the loop, so it is re-bound to its loop-head symbol and what the
    /// walk recorded about its pointee and its name is forgotten (D-187). The
    /// loop's invariants and condition are stated about the same symbols.
    fn on_block_enter(&mut self, block: BasicBlock) {
        let Some(locals) = self.ctx.loop_head_rebinds.get(&block) else {
            return;
        };
        for &local in locals {
            let sort = ty_to_expr_sort_enriched(self.tcx, self.body.local_decls[local].ty);
            self.local_exprs.insert(
                local,
                PureExpr::Var(
                    super::super::loop_merges::loop_head_symbol(block, local),
                    sort,
                ),
            );
            self.deref_exprs.remove(&local);
            self.borrow_of.remove(&local);
            if let Some(name) = source_name_for_local(self.body, local, self.arg_names) {
                self.name_updates.remove(&format!("*{name}"));
                self.name_updates.remove(&name);
            }
        }
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
        // A whole-local assignment replaces whatever borrow the local held: an
        // edge recorded for an earlier value would attribute a later write
        // through the local to a place it no longer points at. The handlers
        // below re-record the edge the new value warrants, if any.
        self.borrow_of.remove(&local);
        self.retire_recorded_writes_to(local, body);
        // Record whole-local copies for the closure-capture carrier lane
        // (#closure-capture-carriers): a consumed call argument is often a
        // move of the aggregate local (`_5 = move _2`).
        if let Rvalue::Use(Operand::Move(src) | Operand::Copy(src), _) = rvalue {
            if src.projection.is_empty() {
                self.closure_copy_of.insert(local, src.local);
            }
        }
        // A whole-local move of a `&mut` borrow hands the SAME pointee to the
        // new local — `let r2 = r;`, or the temporary a borrow-returning call
        // filled being moved into its `let` — so a write through the new
        // local is a write to the place the moved borrow governed. Without
        // this edge the write stays on the new local and the borrowed place
        // keeps its entry value (a false accept, not an `unknown`). The edge
        // targets the chain ROOT, resolved now: the moved-from local and the
        // temporaries between it and the root reach `StorageDead` before the
        // write and their edges are erased with them. Recorded only for a
        // local the body assigns exactly once — a borrow local reassigned on
        // some path governs a different place on each path, and an edge that
        // speaks for the wrong one would turn the write into a false fact
        // about an untouched place. (moved-borrow write)
        if let Rvalue::Use(Operand::Move(src), _) = rvalue {
            if src.projection.is_empty()
                && src.local != local
                && local_is_mut_ref(body, local)
                && local_assigned_exactly_once(body, local)
                && !local_escapes_by_reference(body, local)
            {
                if let Some(root) = self.unescaped_borrow_chain_root(body, src.local) {
                    if root != local {
                        tracing::debug!("moved-borrow edge: {:?} -> {:?}", local, root);
                        self.borrow_of.insert(local, root);
                    }
                }
            }
        }
        // Record closure-environment aggregates for the capture carrier lane
        // (#closure-capture-carriers). A REASSIGNED closure local is ambiguous
        // — record an empty field list so the arity check at the call site
        // drops it back to the legacy lane (fail-closed).
        if let Rvalue::Aggregate(AggregateKind::Closure(..), operands) = rvalue {
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
        // Reborrow finality (Creusot `NotFinalPlaces`): a `&mut` reborrow
        // through a `&mut` deref that is NOT final gets a fresh id and no final
        // link (`borrow_mut`). Identifying it with the reborrowed place's
        // carrier (below) would credit whole-borrow equalities Creusot cannot
        // prove (should_fail/final_borrows). Bind a fresh per-site carrier.
        if let Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Mut { .. }, ref_place) = rvalue {
            if is_mut_ref_reborrow_place(self.tcx, body, ref_place)
                && !self.ctx.final_reborrow_sites.contains(&location)
            {
                self.local_exprs.insert(
                    local,
                    nonfinal_reborrow_carrier(self.tcx, body, local, location),
                );
                self.record_borrow_chain(local, rvalue);
                return;
            }
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

        if let Some(expr) = self.translate_current_rvalue(rvalue, body, location) {
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
        } else if self.is_fn_item_param(local) {
            // A parameter keeps no binding a write replaced: a stale one
            // would be read as its value at the assertion, and its own name
            // is its ENTRY value (D-241).
            let fresh = self.fresh_param_write_symbol(local, location);
            self.local_exprs.insert(local, fresh);
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
        // A direct write to one field still retires a write-back recorded
        // for the WHOLE owner: that value states the sibling's pre-write
        // value too, and the symbolic reset below only reaches `local_exprs`.
        // Before the translation guard, because a write whose value this
        // pass cannot translate is still a write.
        self.retire_recorded_writes_to(place.local, body);
        // A PARAMETER's own name is its ENTRY value, which its `#[requires]`
        // and type invariant constrain, so the identity reset below would
        // read the field just written at its entry value (D-241,
        // proof_assert_after_param_field_write_keeps_entry_requires.rs). A
        // parameter the `proof_assert` lane names apart from its entry value
        // is re-bound to the functional update of its current value, or a
        // fresh symbol where that cannot be built or the value cannot be
        // translated: never its own name, and never the stale pre-write
        // value. Any other parameter keeps the reset: the lane reads a copy of
        // its entry value taken before the store at its binding at the
        // assertion, and the update would hand that copy the stored value
        // (D-140 and D-241 withdraw its entry facts instead). A closure's
        // arguments are its environment and its tupled parameters, which keep
        // the reset.
        if self.is_fn_item_param(place.local) && self.ctx.renamable_params.contains(&place.local) {
            let value = self.translate_current_rvalue(rvalue, body, location);
            let ty = body.local_decls[place.local].ty;
            let path: Option<Vec<usize>> = place
                .projection
                .iter()
                .map(|elem| match elem {
                    ProjectionElem::Field(field, _) => Some(field.as_usize()),
                    _ => None,
                })
                .collect();
            let updated = value.and_then(|value| {
                let path = path?;
                let current = self.local_exprs.get(&place.local).cloned()?;
                param_field_update(self.tcx, &self.local_exprs, current, ty, &path, value)
            });
            let binding =
                updated.unwrap_or_else(|| self.fresh_param_write_symbol(place.local, location));
            self.local_exprs.insert(place.local, binding);
            return;
        }
        // Non-deref projected writes (e.g., `_N.field = ...`).
        // Translation must succeed (matching the original guard).
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
                let synthetic_name = format!("$local_{}", place.local.as_u32());
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
        let Some(expr) = self.translate_current_rvalue(rvalue, body, location) else {
            return;
        };

        // The generalized write-back. The owner place is resolved from the
        // MIR, not from the edge map, so a severed chain, a borrow of a field
        // and a borrow carried inside an aggregate all reach their owner. It
        // refuses whenever it is not exact, which leaves every shape it
        // declines to the handlers below exactly as before.
        let rd = crate::mir_analysis::reaching_defs::for_body(self.tcx, body);
        let governed = crate::mir_analysis::governed_place::governed_place(
            self.tcx, body, &rd, place, location,
        );
        tracing::debug!("governed write-back for {:?}: {:?}", place, governed);
        match governed {
            Governed::Exact(base, path) => {
                self.apply_governed_deref_write(base, &path, &expr, body, location);
            }
            Governed::Candidates(candidates) => {
                // The write lands on one of these and the body does not say
                // which. Every one of them loses whatever any lane recorded
                // for it, and none of them is told what it now holds: picking
                // one would be the guess this resolver exists to refuse, and
                // leaving one un-invalidated is the same false accept with a
                // new mechanism. The legacy handlers are SKIPPED rather than
                // merely preceded — the edge map's entry for this borrow is
                // per-branch state that would re-credit whichever target the
                // walk saw last.
                self.invalidate_governed_candidates(&candidates, body, location);
                self.borrow_of.remove(&place.local);
                return;
            }
            Governed::Unknown => {}
        }

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

    fn on_drop_place(&mut self, place: &Place<'tcx>, body: &Body<'tcx>) {
        if let Some(changed) =
            super::super::drop_glue_writes::locals_changed_by_drop(self.tcx, body, place)
        {
            self.rebind_handed_off(body, changed);
        }
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
        // A `snapshot!` freezes the value its argument has NOW; the capture
        // spec reads the argument by name, which every later reader takes for
        // the name's binding at the assertion (D-241).
        if extract_call_def_id(func).is_some_and(|def_id| {
            crate::provenance::is_spec_library_item(self.tcx, def_id)
                && is_trust_wp_std_snapshot_capture(self.tcx, def_id)
        }) {
            let frozen = snapshot_frozen_name_values(body, self.arg_names, &self.local_exprs);
            if !frozen.is_empty() {
                call_result = call_result.substitute_no_tuple_beta(&frozen);
            }
        }
        // An argument read through memory a write may have changed (D-185)
        // was translated as the entry value: the result is not known.
        let call_location = Location {
            block: bb,
            statement_index: body.basic_blocks[bb].statements.len(),
        };
        let reads_written_memory = self.ctx.written_deref_reads.contains_key(&call_location);
        if reads_written_memory {
            call_result = PureExpr::Var(
                format!("$written_read_call_{}", bb.as_u32()),
                ty_to_expr_sort_enriched(self.tcx, destination.ty(&body.local_decls, self.tcx).ty),
            );
        }
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
        if args.len() == 1 && !reads_written_memory {
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
                    args.first().map(|arg| &arg.node),
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
                        // A ghost cell IS its payload in the encoding, so the
                        // borrow `deref_mut` hands back governs the cell's
                        // whole value: aim the edge at the cell itself, not at
                        // the `&mut cell` temporary. That temporary reaches
                        // `StorageDead` right after the call when the result
                        // is bound by a `let` (`let r = g.deref_mut(); *r = 7`),
                        // and an edge into a dead local is erased before the
                        // write — which left `g` at its entry value while `*r`
                        // was 7. Only for ghost-like receivers: a user
                        // `DerefMut` may hand back one FIELD, and an edge to
                        // its whole receiver would rebind the wrong value.
                        // Durable only for a destination the body assigns
                        // once and never takes the address of: a result local
                        // reassigned on another path (`if c { t = h.deref_mut() }`)
                        // governs a different cell there, and an edge that
                        // outlives the statement would carry this cell's
                        // write onto that path as a fact — a false accept.
                        let receiver_ty = first_arg.node.ty(&body.local_decls, self.tcx);
                        let target = if crate::ghost::type_helpers::is_ghost_like_type(
                            self.tcx,
                            receiver_ty,
                        ) && local_assigned_exactly_once(body, destination.local)
                            && !local_escapes_by_reference(body, destination.local)
                        {
                            self.unescaped_borrow_chain_root(body, arg_local)
                                .unwrap_or(arg_local)
                        } else {
                            arg_local
                        };
                        tracing::debug!(
                            "deref_mut edge: {:?} -> {:?} (arg {:?}, once={}, escapes={})",
                            destination.local,
                            target,
                            arg_local,
                            local_assigned_exactly_once(body, destination.local),
                            local_escapes_by_reference(body, destination.local)
                        );
                        self.borrow_of.insert(destination.local, target);
                    }
                }
            }
        }
        self.local_exprs.insert(destination.local, call_result);
        if let Some(changed) = super::super::drop_glue_writes::locals_changed_by_call(
            self.tcx,
            body,
            bb,
            func,
            args,
            &destination,
        ) {
            self.rebind_handed_off(body, changed);
        }
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

/// Is `local` typed `&mut T`?
pub(super) fn local_is_mut_ref(body: &Body<'_>, local: Local) -> bool {
    matches!(
        body.local_decls[local].ty.kind(),
        rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
    )
}

/// Is the VALUE of `local` written exactly once anywhere in the body — one
/// whole-local assignment or call destination, or one write to a
/// sub-place of the local itself? A write behind a deref (`(*local) = v`)
/// changes the pointee, not the local, and does not count. A local written
/// more than once may hold a different value on each path through a branch,
/// so a body-wide count (not the walk's own view of one path) is what makes
/// a fact recorded about it valid on every path.
pub(super) fn local_assigned_exactly_once(body: &Body<'_>, local: Local) -> bool {
    let writes_local = |place: &rustc_middle::mir::Place<'_>| {
        place.local == local && !matches!(place.projection.first(), Some(ProjectionElem::Deref))
    };
    let mut writes = 0usize;
    for bb_data in body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            match &stmt.kind {
                rustc_middle::mir::StatementKind::Assign((dst, _)) if writes_local(dst) => {
                    writes += 1;
                }
                rustc_middle::mir::StatementKind::SetDiscriminant { place, .. }
                    if writes_local(place) =>
                {
                    writes += 1;
                }
                _ => {}
            }
        }
        if let Some(terminator) = &bb_data.terminator {
            match &terminator.kind {
                rustc_middle::mir::TerminatorKind::Call { destination, .. }
                    if writes_local(destination) =>
                {
                    writes += 1;
                }
                rustc_middle::mir::TerminatorKind::Yield { resume_arg, .. }
                    if writes_local(resume_arg) =>
                {
                    writes += 1;
                }
                rustc_middle::mir::TerminatorKind::InlineAsm { .. } => return false,
                _ => {}
            }
        }
    }
    writes == 1
}

/// Does any statement in the body take `local`'s own address (`&mut local`,
/// `&raw local`) or capture it into a closure by value? Either lets the
/// borrow the local holds be replaced through a path the walk does not see.
pub(super) fn local_escapes_by_reference(body: &Body<'_>, local: Local) -> bool {
    body.basic_blocks.iter().any(|bb_data| {
        bb_data.statements.iter().any(|stmt| match &stmt.kind {
            rustc_middle::mir::StatementKind::Assign((_, rvalue)) => {
                super::super::reborrow_handback::rvalue_lets_local_escape(rvalue, local)
            }
            _ => false,
        })
    })
}
