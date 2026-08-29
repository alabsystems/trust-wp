// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop body extraction support — call obligation collection and recursive call
//! argument extraction.
//!
//! This module handles two independent MIR analyses for loop verification:
//!
//! 1. **Call obligation collection** ([`collect_loop_body_call_obligations`]):
//!    Walks loop body blocks to find function calls and collect their
//!    precondition obligations, wrapped with path condition guards.
//!
//! 2. **Recursive call extraction** ([`extract_recursive_call_args`]):
//!    Walks the full CFG to find self-recursive calls and extract their
//!    arguments for variant decrease verification.
//!
//! Both analyses have their own CFG walkers and are independent from the
//! main `extract_from_block_with_context` extraction path.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, StatementKind, TerminatorKind},
    ty::TyCtxt,
};
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr, UnOp};
use trust_wp_driver::{lookup_spec_with_extern, StdSpec};

use super::{
    super::{
        call_resolve::{
            arg_names_for_def_id, extract_call_def_id, resolve_trait_method_def_id,
            ufcs_path_for_call,
        },
        effects::CallEffects,
        spec_apply::{apply_postconditions_with_effects, collect_precondition_obligations},
        translate::{translate_operand, translate_typed_field_place, ty_to_expr_sort_enriched},
    },
    call_args::call_result_symbol,
    helpers::translate_rvalue_with_enum_variants,
    translate_call_args_for_substitutions_with_tcx,
};

mod recursive_calls;
mod switch_conditions;

pub(crate) use recursive_calls::{extract_recursive_call_args, RecursiveCallSite};
use switch_conditions::switch_branch_conditions;

/// Read-only context for loop body obligation collection.
///
/// Bundles the spec lookup maps and loop body block sets that are
/// threaded unchanged through every recursive call of
/// [`collect_guarded_obligations`], keeping argument counts below
/// clippy's `too_many_arguments` threshold. (#2657)
pub(crate) struct LoopBodySpecContext<'a> {
    pub(crate) user_specs: &'a HashMap<DefId, StdSpec>,
    pub(crate) trait_specs: &'a HashMap<DefId, StdSpec>,
    pub(crate) extern_specs: &'a HashMap<String, StdSpec>,
    pub(crate) body_blocks: &'a HashSet<BasicBlock>,
    /// Blocks whose assignments should force debug-name restoration.
    ///
    /// For nested loops this includes enclosing loop bodies as well as the
    /// current loop. A value assigned by an outer loop but read by an inner
    /// loop is loop-carried, so call obligations must use the symbolic debug
    /// name constrained by invariants rather than the pre-loop initializer.
    pub(crate) name_restore_blocks: Option<&'a HashSet<BasicBlock>>,
}

/// Mutable per-branch state for loop body obligation collection.
///
/// Bundles the three owned collections that are cloned at each
/// `SwitchInt` branch point during [`collect_guarded_obligations`]
/// traversal. (#2657)
#[derive(Clone)]
struct ObligationWalkState {
    local_exprs: HashMap<Local, PureExpr>,
    visited: HashSet<BasicBlock>,
    path_conditions: Vec<PureExpr>,
}

/// Collect call-site precondition obligations from loop body blocks.
///
/// Walks the given set of loop body blocks, finds `Call` terminators, looks up
/// specs, and returns substituted precondition obligations. Unlike
/// `extract_return_expr_with_context` (which bails at `FalseUnwind` loop
/// headers), this function specifically targets in-loop call sites.
///
/// These obligations should be verified under `requires ∧ invariants ∧ loop_condition`,
/// since they only execute when the loop condition is true.
///
/// # Arguments
/// * `tcx` - Type context for resolving function paths
/// * `body` - The MIR body containing the loop
/// * `arg_names` - Function argument names for symbolic representation
/// * `body_blocks` - Set of basic blocks that constitute the loop body
/// * `user_specs` - User-defined function specs
/// * `trait_specs` - Trait method specs
pub(crate) fn collect_loop_body_call_obligations<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    header: BasicBlock,
    spec_ctx: &LoopBodySpecContext<'_>,
) -> Vec<PureExpr> {
    let body_blocks = spec_ctx.body_blocks;
    // Build local_exprs from arguments and debug info (same as extract_loop_body).
    let mut local_exprs: HashMap<Local, PureExpr> = HashMap::new();
    let param_locals: HashSet<Local> = (0..arg_names.len())
        .map(|i| Local::from_usize(i + 1))
        .collect();

    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
        local_exprs.insert(local, PureExpr::Var(name.clone(), sort));
    }

    // Seed with debug info variable names for symbolic resolution.
    for var_debug in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &var_debug.value {
            if place.projection.is_empty() && !param_locals.contains(&place.local) {
                let name = var_debug.name.to_string();
                let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[place.local].ty);
                local_exprs.insert(place.local, PureExpr::Var(name, sort));
            }
        }
    }

    // Also resolve pre-loop temporaries by walking from bb0 to the loop,
    // so that argument expressions used at call sites resolve correctly.
    //
    // After the walk, restore debug-info Var names for locals that are
    // assigned inside the loop body. These are loop-modified variables
    // (e.g., `door` in `door += pass`) whose pre-loop value (e.g., `pass`)
    // is NOT the in-loop value. The invariant constrains the symbolic name
    // (`door@`), so the obligation must use the same symbolic name.
    let mut visited: HashSet<BasicBlock> = HashSet::new();
    let mut worklist = vec![BasicBlock::from_u32(0)];
    while let Some(bb) = worklist.pop() {
        if body_blocks.contains(&bb) || !visited.insert(bb) {
            continue;
        }
        let bb_data = &body.basic_blocks[bb];
        for stmt in &bb_data.statements {
            if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                if place.projection.is_empty() {
                    if let Some(expr) = translate_rvalue_with_enum_variants(
                        tcx,
                        rvalue,
                        &local_exprs,
                        Some(body),
                        None,
                        None,
                    )
                    .or_else(|| translate_loop_assignment_fallback(tcx, body, rvalue, &local_exprs))
                    {
                        local_exprs.insert(place.local, expr);
                    }
                }
            }
        }
        for succ in bb_data.terminator().successors() {
            worklist.push(succ);
        }
    }

    // Collect locals assigned inside the loop body blocks, plus any enclosing
    // loop body blocks supplied by the caller.
    let mut body_assigned_locals: HashSet<Local> = HashSet::new();
    let name_restore_blocks = spec_ctx.name_restore_blocks.unwrap_or(body_blocks);
    for &bb in name_restore_blocks {
        for stmt in &body.basic_blocks[bb].statements {
            if let StatementKind::Assign(box (place, _)) = &stmt.kind {
                if place.projection.is_empty() {
                    body_assigned_locals.insert(place.local);
                }
            }
        }
    }

    // Restore debug-info names for loop-body-modified locals.
    // The pre-loop walk may have resolved them through pre-loop assignments
    // (e.g., `door = pass`), but inside the loop, these variables are modified
    // by the loop body and constrained by invariants. Using the pre-loop
    // resolved value would produce incorrect obligations.
    for var_debug in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &var_debug.value {
            if place.projection.is_empty()
                && !param_locals.contains(&place.local)
                && body_assigned_locals.contains(&place.local)
            {
                let name = var_debug.name.to_string();
                let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[place.local].ty);
                local_exprs.insert(place.local, PureExpr::Var(name, sort));
            }
        }
    }

    let mut obligations = Vec::new();

    // Walk the CFG from the loop header, tracking path conditions at SwitchInt
    // terminators so that guarded calls get wrapped as `guard ==> obligation`.
    // This prevents false "incomplete" results for calls under conditionals
    // (e.g., `if i < v.len() { v[i] = 0; }` where the guard provides the
    // precondition). (#1295)
    let state = ObligationWalkState {
        local_exprs,
        visited: HashSet::new(),
        path_conditions: Vec::new(),
    };
    collect_guarded_obligations(tcx, body, header, state, &spec_ctx, &mut obligations);

    obligations
}

fn translate_loop_assignment_fallback<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    rvalue: &rustc_middle::mir::Rvalue<'tcx>,
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<PureExpr> {
    match rvalue {
        rustc_middle::mir::Rvalue::Ref(_, _, place)
        | rustc_middle::mir::Rvalue::CopyForDeref(place) => {
            translate_typed_field_place(tcx, body, place, local_exprs)
        }
        _ => None,
    }
}

/// Walk the CFG within a loop body, accumulating path conditions at branch
/// points and wrapping call-site precondition obligations with their guards.
///
/// At each `SwitchInt` terminator, each successor gets the current
/// path conditions extended with the branch predicate. When a `Call`
/// terminator is reached, any non-empty path conditions are folded into
/// an implication: `(guard₁ ∧ guard₂ ∧ …) ==> obligation`.
fn collect_guarded_obligations<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    mut state: ObligationWalkState,
    spec_ctx: &LoopBodySpecContext<'_>,
    obligations: &mut Vec<PureExpr>,
) {
    // Only visit blocks within the loop body, and avoid revisiting.
    if !spec_ctx.body_blocks.contains(&bb) || !state.visited.insert(bb) {
        return;
    }

    let bb_data = &body.basic_blocks[bb];

    // Resolve assignments in this block so call-site arguments translate.
    for stmt in &bb_data.statements {
        if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
            if place.projection.is_empty() {
                if let Some(expr) = translate_rvalue_with_enum_variants(
                    tcx,
                    rvalue,
                    &state.local_exprs,
                    Some(body),
                    None,
                    None,
                )
                .or_else(|| {
                    translate_loop_assignment_fallback(tcx, body, rvalue, &state.local_exprs)
                }) {
                    state.local_exprs.insert(place.local, expr);
                }
            }
        }
    }

    let Some(ref terminator) = bb_data.terminator else {
        return;
    };

    match &terminator.kind {
        TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } => {
            if let Some(def_id) = extract_call_def_id(func) {
                let translated_args = translate_call_args_for_substitutions_with_tcx(
                    args,
                    &state.local_exprs,
                    Some(body),
                    Some(tcx),
                );

                let hir_param_names = arg_names_for_def_id(tcx, def_id);

                // Look up spec: user_specs -> trait_specs -> UFCS -> plain path
                // -> trait method fallback (#352)
                // Phase C (#963): uses explicit extern_specs instead of EXTERN_SPECS thread-local.
                // UFCS step added for parity with resolve_call (#2062).
                let extern_opt = if spec_ctx.extern_specs.is_empty() {
                    None
                } else {
                    Some(spec_ctx.extern_specs)
                };
                let user_or_trait_spec = spec_ctx
                    .user_specs
                    .get(&def_id)
                    .or_else(|| spec_ctx.trait_specs.get(&def_id))
                    .cloned();
                let record_path_postconditions = def_id.is_local() || user_or_trait_spec.is_some();
                let spec = user_or_trait_spec
                    .or_else(|| {
                        ufcs_path_for_call(tcx, func)
                            .and_then(|ufcs_path| lookup_spec_with_extern(extern_opt, &ufcs_path))
                    })
                    .or_else(|| {
                        let path = tcx.def_path_str(def_id);
                        lookup_spec_with_extern(extern_opt, &path)
                    })
                    .or_else(|| {
                        let trait_method_id = resolve_trait_method_def_id(tcx, def_id)?;
                        let trait_path = tcx.def_path_str(trait_method_id);
                        lookup_spec_with_extern(extern_opt, &trait_path)
                    });

                if let Some(spec) = spec {
                    let param_names = hir_param_names.or_else(|| spec.param_names.clone());
                    // Collect raw obligations into CallEffects, then wrap
                    // each with path conditions before adding to the final
                    // obligation set.
                    let mut call_effects = CallEffects::new();
                    collect_precondition_obligations(
                        &spec.requires,
                        &translated_args,
                        param_names.as_deref(),
                        &mut call_effects,
                    );
                    for ob in call_effects.obligations.drain(..) {
                        obligations.push(wrap_with_guard(&state.path_conditions, ob));
                    }

                    if !spec.ensures.is_empty() {
                        let result_var = state
                            .local_exprs
                            .get(&destination.local)
                            .cloned()
                            .unwrap_or_else(|| call_result_symbol(body, destination.local, tcx));
                        let mut post_effects = CallEffects::new();
                        // Always model the call result from spec ensures so
                        // subsequent in-loop `SwitchInt` translations can
                        // resolve the call destination to its symbolic
                        // expression (e.g., `_call_X` → `view(v).len()`).
                        // Without this binding, branch conditions like
                        // `i < v.len()` cannot translate at the SwitchInt and
                        // the call obligation `i < v.view().len()` loses its
                        // guard. Predicate-style postcondition assumptions
                        // (the path-condition append below) remain gated by
                        // `record_path_postconditions` to avoid noisy
                        // extern-spec ensures pollution. (wave 18B/B3)
                        let modeled_result = apply_postconditions_with_effects(
                            &spec.ensures,
                            &result_var,
                            &translated_args,
                            param_names.as_deref(),
                            &mut post_effects,
                            record_path_postconditions,
                        );
                        for ob in post_effects.obligations.drain(..) {
                            obligations.push(wrap_with_guard(&state.path_conditions, ob));
                        }
                        if destination.projection.is_empty() {
                            state.local_exprs.insert(destination.local, modeled_result);
                        } else {
                            state.local_exprs.remove(&destination.local);
                        }
                        // FACT A (#recursive-unfolder co-requisite): for a
                        // variant-preserving `Option` adapter — a spec that
                        // ensures BOTH `self.is_some() => result.is_some()` and
                        // `self.is_none() => result.is_none()` (as_ref/as_mut/
                        // as_deref/as_deref_mut) — link the result's Some-ness to
                        // the receiver's, so a subsequent `.unwrap()` precondition
                        // `is_some(result)` can be discharged from `is_some(*self)`
                        // (which the recursive-fn unfolder derives via
                        // `¬is_some(l.1) => len(l)==1`). The Option-sorted result
                        // cannot ride `append_result_guarded_postconditions`
                        // (Bool-sort gate), and the extern spec disables
                        // `record_path_postconditions`, so we push the link
                        // directly. SOUND: `is_some(result)==is_some(*self)` is a
                        // literal consequence of the two spec ensures. Env-gated
                        // during rollout alongside the unfolder.
                        if std::env::var_os("TRUST_WP_OFFLOOP").is_some() {
                            // Some-preserving: `self.is_some() ==> result.is_some()`.
                            // None-preserving: `self.is_none() ==> result.is_none()`
                            // or the equivalent `self.is_none() ==> result == None`.
                            let preserves_variant = spec.ensures.iter().any(|e| {
                                e.contains("self.is_some()") && e.contains("result.is_some()")
                            }) && spec.ensures.iter().any(|e| {
                                e.contains("self.is_none()")
                                    && (e.contains("result.is_none()")
                                        || e.contains("result == None"))
                            });
                            if let Some(p) = std::env::var_os("TRUST_WP_FACTA_DBG") {
                                use std::io::Write as _;
                                if let Ok(mut f) = std::fs::OpenOptions::new()
                                    .create(true)
                                    .append(true)
                                    .open(p)
                                {
                                    let _ = writeln!(
                                        f,
                                        "[factA] preserves={preserves_variant} ensures={:?} arg0={:?}",
                                        spec.ensures,
                                        translated_args
                                            .first()
                                            .map(|a| (a.is_fallback, format!("{:.120?}", a.expr)))
                                    );
                                }
                            }
                            if preserves_variant {
                                if let Some(self_expr) = translated_args
                                    .first()
                                    .filter(|a| !a.is_fallback)
                                    .map(|a| a.expr.clone())
                                {
                                    let is_some = |e: PureExpr| PureExpr::MethodCall {
                                        receiver: Arc::new(e),
                                        method: "is_some".to_string(),
                                        args: Vec::new(),
                                    };
                                    let link = PureExpr::BinOp(
                                        Arc::new(is_some(result_var.clone())),
                                        trust_wp_core::formula::BinOp::Eq,
                                        Arc::new(is_some(self_expr)),
                                    );
                                    if !state.path_conditions.contains(&link) {
                                        state.path_conditions.push(link);
                                    }
                                }
                            }
                        }
                        if record_path_postconditions {
                            let path_relevant_assumptions = post_effects
                                .assumptions
                                .into_iter()
                                .filter(|assumption| {
                                    postcondition_assumption_is_loop_path_relevant(
                                        assumption,
                                        &result_var,
                                    )
                                })
                                .collect();
                            append_result_guarded_postconditions(
                                &mut state.path_conditions,
                                &result_var,
                                path_relevant_assumptions,
                            );
                        }
                    }
                }
            }
            // Continue to the call's return target.
            if let Some(target_bb) = target {
                collect_guarded_obligations(tcx, body, *target_bb, state, spec_ctx, obligations);
            }
        }
        TerminatorKind::SwitchInt { discr, targets } => {
            let branch_conditions =
                switch_branch_conditions(discr, targets, &state.local_exprs, body, None)
                    .unwrap_or_default();

            for target_bb in targets.all_targets() {
                let mut branch_state = state.clone();
                if let Some(cond) = branch_conditions.get(target_bb) {
                    branch_state.path_conditions.push(cond.clone());
                }
                collect_guarded_obligations(
                    tcx,
                    body,
                    *target_bb,
                    branch_state,
                    spec_ctx,
                    obligations,
                );
            }
        }
        TerminatorKind::Goto { target } | TerminatorKind::Drop { target, .. } => {
            collect_guarded_obligations(tcx, body, *target, state, spec_ctx, obligations);
        }
        TerminatorKind::Assert {
            cond,
            expected,
            target,
            ..
        } => {
            if let Some(cond_expr) = translate_operand(cond, &state.local_exprs) {
                let asserted_cond = if *expected {
                    cond_expr
                } else {
                    PureExpr::UnOp(UnOp::Not, Arc::new(cond_expr))
                };
                state.path_conditions.push(asserted_cond);
            }
            collect_guarded_obligations(tcx, body, *target, state, spec_ctx, obligations);
        }
        TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } => {
            collect_guarded_obligations(tcx, body, *real_target, state, spec_ctx, obligations);
        }
        // Return, Resume, Unreachable, etc. — no successors to follow.
        _ => {}
    }
}

fn append_result_guarded_postconditions(
    path_conditions: &mut Vec<PureExpr>,
    result_var: &PureExpr,
    assumptions: Vec<PureExpr>,
) {
    let PureExpr::Var(result_name, Some(ExprSort::Bool)) = result_var else {
        return;
    };

    for assumption in assumptions {
        if assumption.free_vars().contains(result_name) && !path_conditions.contains(&assumption) {
            path_conditions.push(assumption);
        }
    }
}

/// Wrap an obligation with path condition guards using implication.
///
/// If no guards are active, the obligation is returned unchanged.
/// With guards, returns `(g₁ ∧ g₂ ∧ …) ==> obligation` so that
/// the verification only checks the obligation in states where the
/// guards hold.
fn wrap_with_guard(path_conditions: &[PureExpr], obligation: PureExpr) -> PureExpr {
    if path_conditions.is_empty() {
        return obligation;
    }
    let guard = path_conditions
        .iter()
        .cloned()
        .reduce(|acc, cond| PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(cond)))
        .expect("invariant: path_conditions is non-empty (checked above)");
    PureExpr::BinOp(Arc::new(guard), BinOp::Implies, Arc::new(obligation))
}

fn postcondition_assumption_is_loop_path_relevant(
    assumption: &PureExpr,
    result_var: &PureExpr,
) -> bool {
    expr_contains_expr(assumption, result_var) && !expr_mentions_iterator_state(assumption)
}

fn expr_contains_expr(expr: &PureExpr, needle: &PureExpr) -> bool {
    if expr == needle {
        return true;
    }

    match expr {
        PureExpr::BinOp(lhs, _, rhs) => {
            expr_contains_expr(lhs, needle) || expr_contains_expr(rhs, needle)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_contains_expr(inner, needle),
        PureExpr::Let { value, body, .. } => {
            expr_contains_expr(value, needle) || expr_contains_expr(body, needle)
        }
        PureExpr::LetAssume { assumption, body } => {
            expr_contains_expr(assumption, needle) || expr_contains_expr(body, needle)
        }
        PureExpr::LetObligation { obligation, body } => {
            expr_contains_expr(obligation, needle) || expr_contains_expr(body, needle)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_contains_expr(cond, needle)
                || expr_contains_expr(then_expr, needle)
                || expr_contains_expr(else_expr, needle)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            expr_contains_expr(body, needle)
                || triggers
                    .iter()
                    .flatten()
                    .any(|trigger| expr_contains_expr(trigger, needle))
        }
        PureExpr::LogicFnCall { args, .. } => {
            args.iter().any(|arg| expr_contains_expr(arg, needle))
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_contains_expr(receiver, needle)
                || args.iter().any(|arg| expr_contains_expr(arg, needle))
        }
        PureExpr::Closure { body, .. } => expr_contains_expr(body, needle),
        _ => false,
    }
}

fn expr_mentions_iterator_state(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(name, _) => {
            name.contains("iter_current") || name.starts_with("__trust_wp_for_iter_")
        }
        PureExpr::BinOp(lhs, _, rhs) => {
            expr_mentions_iterator_state(lhs) || expr_mentions_iterator_state(rhs)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_mentions_iterator_state(inner),
        PureExpr::Let { value, body, .. } => {
            expr_mentions_iterator_state(value) || expr_mentions_iterator_state(body)
        }
        PureExpr::LetAssume { assumption, body } => {
            expr_mentions_iterator_state(assumption) || expr_mentions_iterator_state(body)
        }
        PureExpr::LetObligation { obligation, body } => {
            expr_mentions_iterator_state(obligation) || expr_mentions_iterator_state(body)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_mentions_iterator_state(cond)
                || expr_mentions_iterator_state(then_expr)
                || expr_mentions_iterator_state(else_expr)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            expr_mentions_iterator_state(body)
                || triggers.iter().flatten().any(expr_mentions_iterator_state)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(expr_mentions_iterator_state),
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_mentions_iterator_state(receiver) || args.iter().any(expr_mentions_iterator_state)
        }
        PureExpr::Closure { body, .. } => expr_mentions_iterator_state(body),
        _ => false,
    }
}
