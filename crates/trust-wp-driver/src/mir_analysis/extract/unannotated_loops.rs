// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call-precondition and panic-arm obligations inside loops that carry NO
//! `#[invariant]` / `#[variant]`.
//!
//! Without an invariant no loop VC exists, so neither the per-loop obligation
//! groups (`loop_body.rs`) nor the loop-invariant dispatch run, and the primary
//! extractor SKIPS every loop body (`skip_loop_or_continue`) and carries
//! pre-loop values past the loop. Every obligation reached only through a loop
//! header — the body, `break` paths, code after an inner loop, and code after
//! the loop — was therefore silently dropped (`#[requires(false)] fn never()`
//! called in a `while` verified).
//!
//! Creusot gives an invariant-less loop the implicit `invariant true`: the body
//! is checked from a state in which every place the loop may write is
//! arbitrary. This walker implements exactly that over-approximation:
//!
//! * a PATH-SENSITIVE walk from the function entry (pre-loop values and path
//!   conditions are exact on each path);
//! * on entering a loop header, every local the loop may write (direct, through
//!   a projection, as a call destination, `&mut`/raw-pointer borrowed anywhere
//!   in the body) is re-bound to a FRESH variable, range-guarded by its machine
//!   integer type (a literal consequence of the Rust type);
//! * reaching a header already entered on the path stops the path (the havoc
//!   state at the header subsumes every later iteration);
//! * writes through a projection or `&mut`-carrying call arguments re-bind the
//!   affected locals to fresh variables; untranslatable assignments UNBIND the
//!   local (reads then become fresh fallback arguments, never stale values);
//! * obligations are emitted only at sites reachable from a loop header (the
//!   primary extractor owns the exact pre-loop region), wrapped as
//!   `path_conditions ==> obligation`; a path condition whose switch operand is
//!   not value-stable is dropped (weaker premise), a stale call argument makes
//!   the obligation `false`, a call whose callee this extractor cannot pin
//!   down to a single `DefId` — a fn pointer, a `dyn` vtable, any indirect
//!   call — and a call through a generic `Fn*` bound (whose goal this walker
//!   cannot state) are `false`, and a walk that exceeds its budget or meets a
//!   cycle not closed by a known header emits `false`;
//! * a `Drop` terminator and a call whose callee INSTANTIATION carries an
//!   unchecked user `Drop::drop` or exposes interior mutability emit their
//!   own obligations (`drop_glue_obligation` / `call_type_obligation`),
//!   independently of whether the callee resolves.
//!
//! Every choice only ever removes accept paths.

use std::{
    cell::Cell,
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        BasicBlock, Body, BorrowKind, Local, Location, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind,
    },
    ty::{Mutability, Ty, TyCtxt, TyKind},
};
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr, UnOp};
use trust_wp_driver::StdSpec;

use super::{
    super::{
        call_resolve::{arg_names_for_def_id, resolve_trait_method_def_id, ufcs_path_for_call},
        deref_store_staleness::DerefStoreStaleness,
        effects::{fail_closed_marker, CallEffects},
        loops::{detect_loops, LoopAnalysis},
        spec_apply::{
            apply_postconditions_with_effects, collect_precondition_obligations, TranslatedArg,
        },
        translate::ty_to_expr_sort_enriched,
    },
    call_resolve_util::{classify_loop_call_target, LoopCallTarget},
    helpers::{
        block_diverges_via_panic, switch_discr_is_value_stable, translate_rvalue_with_enum_variants,
    },
    loop_body::switch_branch_conditions,
    translate_call_args_for_substitutions_with_tcx,
};
use crate::trait_credit::{lookup_user_or_trait_spec, GrantSite};

/// Prefix of every fresh variable minted by this walker.
pub(crate) const UNANNOTATED_LOOP_HAVOC_PREFIX: &str = "__trust_wp_uloop_havoc_";

/// Upper bound on block visits over all paths; beyond it the walk fails closed.
const WALK_BUDGET: usize = 20_000;

thread_local! {
    static HAVOC_GENERATION: Cell<u64> = const { Cell::new(0) };
}

pub(super) fn fresh_name(tag: &str) -> String {
    let generation = HAVOC_GENERATION.with(|g| {
        let next = g.get().wrapping_add(1);
        g.set(next);
        next
    });
    format!("{UNANNOTATED_LOOP_HAVOC_PREFIX}{tag}_{generation}")
}

#[derive(Clone)]
struct PathState {
    local_exprs: HashMap<Local, PureExpr>,
    visited: HashSet<BasicBlock>,
    entered_headers: HashSet<BasicBlock>,
    path_conditions: Vec<PureExpr>,
}

struct Walker<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    user_specs: &'a HashMap<DefId, StdSpec>,
    trait_specs: &'a HashMap<DefId, StdSpec>,
    extern_specs: &'a HashMap<String, StdSpec>,
    analysis: LoopAnalysis,
    written_by_header: HashMap<BasicBlock, HashSet<Local>>,
    /// Locals whose storage can change without a direct assignment.
    pointer_mutable: HashSet<Local>,
    /// Blocks reachable from some loop header: the region this walker owns.
    region: HashSet<BasicBlock>,
    staleness: DerefStoreStaleness<'a, 'tcx>,
    budget: usize,
    exhausted: bool,
    obligations: Vec<PureExpr>,
}

/// Collect the obligations of every call precondition and panic arm reachable
/// through a loop header, for a function whose loops carry no invariant.
/// Returns an empty vector when the body has no loop.
pub(crate) fn collect_unannotated_loop_obligations<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
) -> Vec<PureExpr> {
    let analysis = detect_loops(body);
    if !analysis.has_loops {
        return Vec::new();
    }
    let pointer_mutable = pointer_mutable_locals(body);
    let written_by_header = analysis
        .loops
        .iter()
        .map(|info| {
            let mut written = locals_written_in_blocks(body, &info.body_blocks);
            written.extend(pointer_mutable.iter().copied());
            (info.header, written)
        })
        .collect();
    let mut region = HashSet::new();
    let mut worklist: Vec<BasicBlock> = analysis.loops.iter().map(|l| l.header).collect();
    while let Some(bb) = worklist.pop() {
        if region.insert(bb) {
            worklist.extend(body.basic_blocks[bb].terminator().successors());
        }
    }

    let mut local_exprs = HashMap::new();
    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        if local.as_usize() >= body.local_decls.len() {
            break;
        }
        let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
        local_exprs.insert(local, PureExpr::Var(name.clone(), sort));
    }
    let mut walker = Walker {
        tcx,
        body,
        user_specs,
        trait_specs,
        extern_specs,
        analysis,
        written_by_header,
        pointer_mutable,
        region,
        staleness: DerefStoreStaleness::new(Some(tcx), body),
        budget: WALK_BUDGET,
        exhausted: false,
        obligations: Vec::new(),
    };
    let state = PathState {
        local_exprs,
        visited: HashSet::new(),
        entered_headers: HashSet::new(),
        path_conditions: Vec::new(),
    };
    walker.walk(BasicBlock::from_u32(0), state);
    if walker.exhausted {
        walker
            .obligations
            .push(fail_closed_marker("unannotated-loop-exhausted"));
    }
    walker.obligations
}

impl<'tcx> Walker<'_, 'tcx> {
    fn is_header(&self, bb: BasicBlock) -> bool {
        self.analysis.loops.iter().any(|l| l.header == bb)
    }

    fn emit(&mut self, state: &PathState, obligation: PureExpr) {
        let guarded = wrap_with_guard(&state.path_conditions, obligation);
        if !self.obligations.contains(&guarded) {
            self.obligations.push(guarded);
        }
    }

    /// Re-bind `local` to a fresh variable; a machine-integer range fact for
    /// it joins the path conditions.
    fn havoc(&self, state: &mut PathState, local: Local) {
        let ty = self.body.local_decls[local].ty;
        let sort = ty_to_expr_sort_enriched(self.tcx, ty);
        let var = PureExpr::Var(fresh_name(&local.as_u32().to_string()), sort);
        if let Some(fact) = machine_int_range_fact(self.tcx, ty, &var) {
            state.path_conditions.push(fact);
        }
        state.local_exprs.insert(local, var);
    }

    fn havoc_pointer_reachable(&self, state: &mut PathState) {
        let mut locals: Vec<Local> = self.pointer_mutable.iter().copied().collect();
        for (local, decl) in self.body.local_decls.iter_enumerated() {
            if ty_holds_mutable_pointer(decl.ty) {
                locals.push(local);
            }
        }
        locals.sort();
        locals.dedup();
        for local in locals {
            self.havoc(state, local);
        }
    }

    fn walk(&mut self, bb: BasicBlock, mut state: PathState) {
        if self.exhausted {
            return;
        }
        if self.budget == 0 {
            self.exhausted = true;
            return;
        }
        self.budget -= 1;

        if self.is_header(bb) {
            if !state.entered_headers.insert(bb) {
                // Back edge: the havoc state at the first entry subsumes it.
                return;
            }
            let mut written: Vec<Local> = self.written_by_header[&bb].iter().copied().collect();
            written.sort();
            for local in written {
                self.havoc(&mut state, local);
            }
        } else if !state.visited.insert(bb) {
            // A cycle not closed by a detected header: fail closed.
            if self.region.contains(&bb) {
                self.emit(&state, fail_closed_marker("unannotated-loop-cycle"));
            }
            return;
        }

        let body = self.body;
        let bb_data = &body.basic_blocks[bb];
        for stmt in &bb_data.statements {
            match &stmt.kind {
                StatementKind::Assign((place, rvalue)) => {
                    if place.projection.is_empty() {
                        match translate_rvalue_with_enum_variants(
                            self.tcx,
                            rvalue,
                            &state.local_exprs,
                            Some(body),
                            None,
                            None,
                        ) {
                            Some(expr) => {
                                state.local_exprs.insert(place.local, expr);
                            }
                            None => {
                                state.local_exprs.remove(&place.local);
                            }
                        }
                    } else if place
                        .projection
                        .iter()
                        .any(|p| matches!(p, ProjectionElem::Deref))
                    {
                        self.havoc(&mut state, place.local);
                        self.havoc_pointer_reachable(&mut state);
                    } else {
                        self.havoc(&mut state, place.local);
                    }
                    if let Rvalue::Ref(_, BorrowKind::Mut { .. }, borrowed)
                    | Rvalue::RawPtr(_, borrowed) = rvalue
                    {
                        self.havoc(&mut state, borrowed.local);
                    }
                }
                StatementKind::SetDiscriminant {
                    place: deref!(place),
                    ..
                } => {
                    self.havoc(&mut state, place.local);
                }
                _ => {}
            }
        }

        let terminator = bb_data.terminator();
        let term_location = Location {
            block: bb,
            statement_index: bb_data.statements.len(),
        };
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                self.visit_call(bb, func, args, *destination, term_location, &mut state);
                if let Some(next) = target {
                    self.walk(*next, state);
                }
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let stable = switch_discr_is_value_stable(self.tcx, body, discr, false)
                    && !self.staleness.operand_may_read_stale(discr, term_location);
                let conditions = if stable {
                    switch_branch_conditions(discr, targets, &state.local_exprs, body, None)
                        .unwrap_or_default()
                } else {
                    HashMap::new()
                };
                for target in targets.all_targets() {
                    if self.region.contains(&bb)
                        && block_diverges_via_panic(self.tcx, body, *target)
                    {
                        let unreachable = conditions
                            .get(target)
                            .map(|c| PureExpr::UnOp(UnOp::Not, Arc::new(c.clone())))
                            .unwrap_or_else(|| {
                                fail_closed_marker("unannotated-loop-switch-no-cond")
                            });
                        self.emit(&state, unreachable);
                    }
                    let mut branch = state.clone();
                    if let Some(cond) = conditions.get(target) {
                        branch.path_conditions.push(cond.clone());
                    }
                    self.walk(*target, branch);
                }
            }
            TerminatorKind::Goto { target, .. } => {
                self.walk(*target, state);
            }
            TerminatorKind::Drop { place, target, .. } => {
                if self.region.contains(&bb) {
                    if let Some(obligation) = super::assertion::drop_glue_obligation(
                        self.tcx,
                        body,
                        place,
                        self.user_specs,
                    ) {
                        self.emit(&state, obligation);
                    }
                }
                self.walk(*target, state);
            }
            TerminatorKind::Assert { target, .. } => {
                // Arithmetic/bounds side conditions are owned by the overflow
                // lane; nothing is ASSUMED here (a weaker premise is sound).
                self.walk(*target, state);
            }
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => {
                self.walk(*real_target, state);
            }
            TerminatorKind::Return
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Unreachable => {}
            _ => {
                // Unknown control flow inside the owned region: fail closed.
                if self.region.contains(&bb) {
                    self.emit(&state, fail_closed_marker("unannotated-loop-unknown-cf"));
                }
            }
        }
    }

    fn visit_call(
        &mut self,
        bb: BasicBlock,
        func: &Operand<'tcx>,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
        destination: Place<'tcx>,
        location: Location,
        state: &mut PathState,
    ) {
        let tcx = self.tcx;
        let body = self.body;
        let in_region = self.region.contains(&bb);
        let mut result_binding: Option<PureExpr> = None;
        // The obligations the callee's INSTANTIATION owes —
        // an unchecked user `Drop::drop` in a type argument, a generic callee
        // instantiated at an interior-mutable type — are owed wherever that
        // callee's contract could be credited, so this gate runs on the raw
        // terminator and resolves the target itself.
        if in_region {
            if let Some(obligation) =
                super::assertion::call_type_obligation(tcx, body, bb, func, self.user_specs)
            {
                self.emit(state, obligation);
            }
        }
        // The callee's identity decides what ELSE this site owes. The
        // decision is SHARED with the annotated lane (`loop_body.rs`) so the
        // two cannot drift (D-36): a target this extractor cannot pin down
        // carries an unknown precondition, and an unknown precondition is
        // OWED here — it is never dropped because the callee operand is not
        // an `FnDef` constant. Hanging the handler below off
        // `extract_call_def_id` alone would let a call through a fn pointer,
        // a `dyn` vtable or any reassigned local inside an unannotated loop
        // owe nothing at all, and a violated precondition would verify. A generic
        // `Fn*`-bound call classifies as `GenericFnTrait` and is refused by
        // the same arm (its `precondition_F f args` goal is unstatable here).
        let target = classify_loop_call_target(tcx, body, bb, func);
        if in_region && !matches!(target, LoopCallTarget::Resolved(_)) {
            self.emit(
                state,
                fail_closed_marker("unannotated-loop-call-unresolved"),
            );
        }
        if let LoopCallTarget::Resolved(def_id) = target {
            let mut translated_args = translate_call_args_for_substitutions_with_tcx(
                args,
                &state.local_exprs,
                Some(body),
                Some(tcx),
            );
            // A fallback argument is an unknown value: give each its own fresh
            // variable instead of the shared positional `argN` placeholder.
            for arg in &mut translated_args {
                if arg.is_fallback {
                    let sort = match &arg.expr {
                        PureExpr::Var(_, sort) => sort.clone(),
                        _ => None,
                    };
                    *arg = TranslatedArg::fallback(PureExpr::Var(fresh_name("arg"), sort));
                }
            }
            let (spec, from_user_or_trait_table) = self.lookup_spec(def_id, func);
            if let Some(spec) = spec {
                let param_names =
                    arg_names_for_def_id(tcx, def_id).or_else(|| spec.param_names.clone());
                if in_region {
                    let mut pre = CallEffects::new();
                    collect_precondition_obligations(
                        &spec.requires,
                        &translated_args,
                        param_names.as_deref(),
                        &mut pre,
                    );
                    // A refused grant is owed UNGUARDED, as an exhausted walk
                    // is: whatever path reaches the call, the grant it cannot
                    // state is owed.
                    if from_user_or_trait_table
                        && super::call_spec::charge_callee_invariant_grant(
                            tcx,
                            body,
                            func,
                            def_id,
                            (self.user_specs, self.trait_specs),
                            &translated_args,
                            &mut pre,
                        )
                        .is_err()
                        && !self.obligations.contains(&PureExpr::Bool(false))
                    {
                        self.obligations.push(PureExpr::Bool(false));
                    }
                    if !pre.obligations.is_empty()
                        && args
                            .iter()
                            .any(|arg| self.staleness.operand_may_read_stale(&arg.node, location))
                    {
                        pre.obligations = vec![fail_closed_marker("unannotated-loop-stale-arg")];
                    }
                    for ob in pre.obligations {
                        self.emit(state, ob);
                    }
                }
                if !spec.ensures.is_empty() && destination.projection.is_empty() {
                    let result_var = PureExpr::Var(
                        fresh_name("call"),
                        ty_to_expr_sort_enriched(tcx, body.local_decls[destination.local].ty),
                    );
                    let mut post = CallEffects::new();
                    let modeled = apply_postconditions_with_effects(
                        &spec.ensures,
                        &crate::mir_analysis::call_signature(
                            tcx,
                            def_id,
                            param_names.as_deref(),
                            Some(crate::mir_analysis::CallSite { body, func }),
                        ),
                        &result_var,
                        &translated_args,
                        param_names.as_deref(),
                        &mut post,
                        false,
                    );
                    if in_region {
                        for ob in post.obligations {
                            self.emit(state, ob);
                        }
                    }
                    result_binding = Some(modeled);
                }
            }
        }
        // The callee may write through any `&mut`/raw pointer it receives.
        if args
            .iter()
            .any(|arg| operand_may_carry_mutable_pointer(body, &arg.node))
        {
            self.havoc_pointer_reachable(state);
        }
        if destination.projection.is_empty() {
            match result_binding {
                Some(expr) => {
                    state.local_exprs.insert(destination.local, expr);
                }
                None => self.havoc(state, destination.local),
            }
        } else {
            self.havoc(state, destination.local);
            self.havoc_pointer_reachable(state);
        }
    }

    /// The spec this call is stated with, and whether it came from the user
    /// or trait table — the only specs whose callee holds an invariant grant.
    fn lookup_spec(&self, def_id: DefId, func: &Operand<'tcx>) -> (Option<StdSpec>, bool) {
        let tcx = self.tcx;
        let extern_opt = (!self.extern_specs.is_empty()).then_some(self.extern_specs);
        // Spec provenance: path-keyed tables describe library items only, and a
        // builtin contract describes this call only when the code that runs is
        // library code (a local impl of a std trait, or an unresolved generic
        // impl, gets at most the opaque per-impl predicates).
        let admission = crate::provenance::builtin_spec_admission_for_operand(
            tcx,
            func,
            Some(self.body.source.def_id()),
        );
        let site = GrantSite {
            tcx,
            body: self.body,
            func,
        };
        let user_or_trait_spec =
            lookup_user_or_trait_spec(self.user_specs, self.trait_specs, def_id, site);
        let from_user_or_trait_table = user_or_trait_spec.is_some();
        let spec = user_or_trait_spec
            .cloned()
            .or_else(|| {
                ufcs_path_for_call(tcx, func).and_then(|ufcs_path| {
                    crate::provenance::lookup_spec_for_def(
                        tcx,
                        def_id,
                        admission,
                        extern_opt,
                        &ufcs_path,
                        crate::provenance::CallSite::of_operand(
                            func,
                            Some(self.body.source.def_id()),
                        ),
                    )
                })
            })
            .or_else(|| {
                crate::provenance::lookup_spec_for_def(
                    tcx,
                    def_id,
                    admission,
                    extern_opt,
                    &tcx.def_path_str(def_id),
                    crate::provenance::CallSite::of_operand(func, Some(self.body.source.def_id())),
                )
            })
            .or_else(|| {
                let trait_method_id = resolve_trait_method_def_id(tcx, def_id)?;
                crate::provenance::lookup_spec_for_def(
                    tcx,
                    trait_method_id,
                    admission,
                    extern_opt,
                    &tcx.def_path_str(trait_method_id),
                    crate::provenance::CallSite::of_operand(func, Some(self.body.source.def_id())),
                )
            });
        (spec, from_user_or_trait_table)
    }
}

fn wrap_with_guard(path_conditions: &[PureExpr], obligation: PureExpr) -> PureExpr {
    match path_conditions
        .iter()
        .cloned()
        .reduce(|acc, cond| PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(cond)))
    {
        Some(guard) => PureExpr::BinOp(Arc::new(guard), BinOp::Implies, Arc::new(obligation)),
        None => obligation,
    }
}

/// `lo <= var && var <= hi` for a machine integer type whose bounds fit `i64`
/// (only `0 <= var` for wider unsigned types).
fn machine_int_range_fact<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    var: &PureExpr,
) -> Option<PureExpr> {
    if !matches!(var, PureExpr::Var(_, Some(ExprSort::Int))) {
        return None;
    }
    let pointer_bits = tcx.data_layout.pointer_size().bits();
    let le = |a: PureExpr, b: PureExpr| PureExpr::BinOp(Arc::new(a), BinOp::Le, Arc::new(b));
    let and = |a: PureExpr, b: PureExpr| PureExpr::BinOp(Arc::new(a), BinOp::And, Arc::new(b));
    match ty.kind() {
        TyKind::Int(int_ty) => {
            let bits = int_ty.bit_width().unwrap_or(pointer_bits);
            if bits > 64 {
                return None;
            }
            let hi: i64 = if bits == 64 {
                i64::MAX
            } else {
                (1i64 << (bits - 1)) - 1
            };
            let lo: i64 = if bits == 64 {
                i64::MIN
            } else {
                -(1i64 << (bits - 1))
            };
            Some(and(
                le(PureExpr::Int(lo), var.clone()),
                le(var.clone(), PureExpr::Int(hi)),
            ))
        }
        TyKind::Uint(uint_ty) => {
            let bits = uint_ty.bit_width().unwrap_or(pointer_bits);
            let lower = le(PureExpr::Int(0), var.clone());
            if bits >= 63 {
                return Some(lower);
            }
            Some(and(
                lower,
                le(var.clone(), PureExpr::Int((1i64 << bits) - 1)),
            ))
        }
        _ => None,
    }
}

fn ty_holds_mutable_pointer(ty: Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        TyKind::Ref(_, _, Mutability::Mut) | TyKind::RawPtr(_, Mutability::Mut)
    )
}

pub(super) fn operand_may_carry_mutable_pointer<'tcx>(
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> bool {
    let (Operand::Copy(place) | Operand::Move(place)) = operand else {
        return false;
    };
    let mut ty = body.local_decls[place.local].ty;
    for elem in place.projection {
        ty = match elem {
            ProjectionElem::Field(_, field_ty) => field_ty,
            ProjectionElem::Deref => match ty.builtin_deref(true) {
                Some(inner) => inner,
                None => return true,
            },
            _ => return true,
        };
    }
    // A by-value aggregate may carry a `&mut` inside it (closures, structs):
    // only plain scalars and shared references to scalars are excluded.
    !matches!(
        ty.kind(),
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_)
    ) && !matches!(ty.kind(), TyKind::Ref(_, inner, Mutability::Not)
        if matches!(inner.kind(), TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_)))
}

/// Locals whose storage can change without a direct assignment: mutably or
/// raw-pointer borrowed anywhere, or of `&mut` / `*mut` type.
fn pointer_mutable_locals(body: &Body<'_>) -> HashSet<Local> {
    let mut locals = HashSet::new();
    for (local, decl) in body.local_decls.iter_enumerated() {
        if ty_holds_mutable_pointer(decl.ty) {
            locals.insert(local);
        }
    }
    for bb_data in body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            if let StatementKind::Assign((_, rvalue)) = &stmt.kind {
                if let Rvalue::Ref(_, BorrowKind::Mut { .. }, place) | Rvalue::RawPtr(_, place) =
                    rvalue
                {
                    locals.insert(place.local);
                }
            }
        }
    }
    locals
}

/// Locals written (directly, through a projection, or as a call destination)
/// by the given blocks.
fn locals_written_in_blocks(body: &Body<'_>, blocks: &HashSet<BasicBlock>) -> HashSet<Local> {
    let mut written = HashSet::new();
    for &bb in blocks {
        let bb_data = &body.basic_blocks[bb];
        for stmt in &bb_data.statements {
            match &stmt.kind {
                StatementKind::Assign((place, _))
                | StatementKind::SetDiscriminant {
                    place: deref!(place),
                    ..
                } => {
                    written.insert(place.local);
                }
                _ => {}
            }
        }
        if let TerminatorKind::Call { destination, .. } = &bb_data.terminator().kind {
            written.insert(destination.local);
        }
    }
    written
}
