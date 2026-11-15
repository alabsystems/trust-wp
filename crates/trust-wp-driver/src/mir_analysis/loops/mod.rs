// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop analysis for MIR.
//!
//! Detects loops via DFS-based back edge detection, and extracts
//! loop body expressions for invariant checking.

mod body_effects;
mod changed_places;
mod condition;
mod detection;
mod for_loop_iter;
mod for_range;
mod post_loop;
pub(crate) use post_loop::find_post_loop_exit_block;
mod pre_loop_extract;
mod pre_loop_resolve;
mod stale_pointee_params;
mod write_sites;

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use body_effects::extract_body_effects;
pub(crate) use body_effects::DroppedPremise;
use changed_places::{extract_changed_places, extract_modified_vars};
pub(crate) use changed_places::{
    ChangedPlaces, ChangedPlacesTree, ForLoopGhostState, LoopBodyExpr,
};
use condition::{find_body_break_condition, whilelet_condition};
pub(crate) use detection::{detect_loops, LoopAnalysis, LoopInfo};
use for_loop_iter::{
    extract_for_loop_ghost_state, for_loop_discriminant_condition,
    recover_for_loop_iterable_source_local, synthesize_for_loop_produced_effect,
};
use for_range::synthesize_for_range_condition;
use post_loop::{
    extract_post_loop_deref_final_values, extract_post_loop_deref_writes, extract_post_loop_return,
    locals_written_in, mutably_lent_locals,
};
use pre_loop_extract::extract_pre_loop_assignments;
pub(crate) use pre_loop_extract::{
    every_return_passes_through, names_rewritten_after_exit_before_later_loop, prior_loop_blocks,
    UnresolvedPreLoopCall,
};
pub(crate) use pre_loop_resolve::resolve_pre_loop_calls;
use pre_loop_resolve::{
    resolve_pre_loop_call_facts_for_local_names_with_spec_ctx,
    resolve_pre_loop_call_facts_with_spec_ctx, resolve_pre_loop_call_locals_with_spec_ctx,
};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Body, Local, StatementKind, TerminatorKind};
pub(crate) use stale_pointee_params::{
    name_invalidated_args, params_invalidated_by_loops, params_invalidated_by_loops_at_exits,
    InvalidatedEntryNames,
};
use tracing::debug;
use trust_wp_core::formula::{BinOp, PureExpr, UnOp};
use trust_wp_driver::StdSpec;
pub(crate) use write_sites::{ty_may_carry_write_capability, WriteSites};

use super::{
    call_resolve::{extract_call_def_id, resolve_trait_method_def_id},
    translate::{
        operand_is_bool, translate_operand, translate_rvalue, translate_rvalue_typed,
        translate_typed_field_place, ty_to_expr_sort, ty_to_expr_sort_enriched,
    },
};

/// Context for resolving call-site specs during loop body effect extraction.
///
/// When provided, `BodyExtractionCtx` can look up callee postconditions at
/// Call terminators and model the destination as a constrained expression
/// instead of havocing it. This enables verification of loops that call
/// specced functions (e.g., `v.len()`, `x.abs()`). (#1463)
///
/// Phase C (#963): `extern_specs` added to replace direct `EXTERN_SPECS`
/// thread-local access in `body_effects.rs` and `pre_loop_resolve.rs`.
#[derive(Clone, Copy)]
pub(crate) struct CallSpecContext<'specs, 'tcx> {
    pub(crate) tcx: rustc_middle::ty::TyCtxt<'tcx>,
    pub(crate) user_specs: &'specs HashMap<DefId, StdSpec>,
    pub(crate) trait_specs: &'specs HashMap<DefId, StdSpec>,
    pub(crate) extern_specs: &'specs HashMap<String, StdSpec>,
}

/// Extract loop body expression with invariant checking support.
///
/// For a simple while loop like:
/// ```text
/// while (condition) { body; }
/// ```
///
/// This extracts:
/// - The loop condition expression
/// - The loop body effect on modified variables
///
/// # Arguments
/// * `body` - The MIR function body
/// * `arg_names` - Parameter names for variable mapping
/// * `loop_info` - Information about a detected loop
///
/// # Returns
///
/// A `LoopBodyExpr` with the condition and body expressions.
#[allow(clippy::too_many_lines)]
pub(crate) fn extract_loop_body<'tcx>(
    body: &Body<'tcx>,
    arg_names: &[String],
    loop_info: &LoopInfo,
    all_loops: Option<&[LoopInfo]>,
    call_spec_ctx: Option<&CallSpecContext<'_, 'tcx>>,
) -> LoopBodyExpr {
    // Compute predecessor map once for all condition extraction functions (#2103)
    let preds = detection::predecessor_map(body);

    // Build initial variable mapping: local -> arg name
    let mut local_exprs: HashMap<Local, PureExpr> = HashMap::new();
    let mut local_to_name: HashMap<Local, String> = HashMap::new();
    let param_locals: HashSet<Local> = (0..arg_names.len())
        .map(|i| Local::from_usize(i + 1))
        .collect();

    // Use enriched sort when TyCtxt is available (carries ADT/FMap sort info
    // across the driver→encoder boundary). (#994 Phase 2)
    let sort_for_local = |local: Local| -> Option<trust_wp_core::formula::ExprSort> {
        match call_spec_ctx {
            Some(ctx) => ty_to_expr_sort_enriched(ctx.tcx, body.local_decls[local].ty),
            None => ty_to_expr_sort(body.local_decls[local].ty),
        }
    };

    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        let sort = sort_for_local(local);
        local_exprs.insert(local, PureExpr::Var(name.clone(), sort));
        local_to_name.insert(local, name.clone());
    }

    // Add local variable names from debug info (e.g., `let mut i = 0`).
    // Seed both local_to_name and local_exprs with symbolic Var(name) entries
    // so that condition extraction produces symbolic expressions like `i < n`
    // rather than concrete values like `0 < n`.
    for var_debug in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &var_debug.value {
            if place.projection.is_empty() && !param_locals.contains(&place.local) {
                let name = var_debug.name.to_string();
                local_to_name.insert(place.local, name.clone());
                let sort = sort_for_local(place.local);
                local_exprs.insert(place.local, PureExpr::Var(name, sort));
            }
        }
    }

    populate_pre_loop_temps(body, loop_info, &local_to_name, &mut local_exprs);

    // Find the condition block. In MIR, while-loops lower to:
    //   bb_header: falseUnwind -> [real: bb_cond, unwind: bb_cleanup]
    //   bb_cond: _tmp = Lt(i, n); switchInt(_tmp) -> [0: exit, otherwise: body]
    // The header may be the condition block directly (SwitchInt terminator),
    // or it may be a FalseUnwind trampoline that points to the condition block.
    let header_data = &body.basic_blocks[loop_info.header];
    let mut for_loop_option_local: Option<Local> = None;
    let cond_block = match &header_data.terminator().kind {
        TerminatorKind::SwitchInt { .. } => loop_info.header,
        TerminatorKind::FalseUnwind { real_target, .. } => *real_target,
        // For-loop pattern: header is Call(Iterator::next) -> switch_bb.
        // The SwitchInt on the Option discriminant (Some vs None) is in the
        // successor block, not the header itself. (#1295)
        //
        // Also capture the Call destination as the Option local so
        // for_loop_discriminant_condition can classify switch targets by
        // whether they extract the loop variable. (#1581)
        TerminatorKind::Call {
            target: Some(switch_bb),
            destination,
            ..
        } => {
            if destination.projection.is_empty() {
                let dest_name = format!("$iter_result_{}", destination.local.as_u32());
                let sort = sort_for_local(destination.local);
                local_exprs
                    .entry(destination.local)
                    .or_insert_with(|| PureExpr::Var(dest_name, sort));
                for_loop_option_local = Some(destination.local);
            }
            *switch_bb
        }
        TerminatorKind::Goto { target, .. } => *target,
        _ => loop_info.header, // Fallback: try header itself
    };

    if let Some(ctx) = call_spec_ctx {
        resolve_condition_predecessor_call_results(ctx, body, cond_block, &preds, &mut local_exprs);
    }

    // Process the condition block's statements to resolve temporaries.
    // MIR copies locals into temporaries before comparing:
    //   _6 = copy _2 (i); _7 = copy _1 (n); _5 = Lt(move _6, move _7)
    // We must resolve these before examining the SwitchInt discriminant.
    //
    // For for-loops, the chain is: FalseUnwind -> Call(Iterator::next) -> SwitchInt.
    // When cond_block is a Call (not SwitchInt), follow one more hop. (#1295)
    let cond_data = &body.basic_blocks[cond_block];
    for stmt in &cond_data.statements {
        if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
            if place.projection.is_empty() {
                let expr = call_spec_ctx
                    .and_then(|ctx| {
                        translate_loop_assignment_rvalue(ctx, body, rvalue, &local_exprs)
                    })
                    .or_else(|| translate_rvalue(rvalue, &local_exprs, Some(body)));
                if let Some(expr) = expr {
                    local_exprs.insert(place.local, expr);
                }
            }
        }
    }
    // What the callee's contract says about a value the condition reads from
    // a call on the header path, and why it cannot be said when it cannot.
    let mut condition_facts: Vec<PureExpr> = Vec::new();
    let mut condition_unstated: Option<String> = None;
    let mut call_hop_switch: Option<BasicBlock> = None;
    let (cond_block, cond_data) = match &cond_data.terminator().kind {
        TerminatorKind::Call {
            func,
            args,
            target: Some(switch_bb),
            destination,
            ..
        } => {
            // Register the Call destination in local_exprs so that
            // `discriminant(dest)` in the switch block resolves correctly.
            // The actual value doesn't matter for discriminant comparison --
            // we just need a placeholder so translate_place succeeds. (#1295)
            if destination.projection.is_empty() {
                let dest_name = format!("$iter_result_{}", destination.local.as_u32());
                let sort = sort_for_local(destination.local);
                let stated = call_spec_ctx.and_then(|ctx| {
                    state_condition_call(
                        ctx,
                        body,
                        loop_info,
                        &local_to_name,
                        cond_block,
                        func,
                        args,
                        &local_exprs,
                    )
                });
                match stated {
                    Some(ConditionCallPremise::Stated { value, facts }) => {
                        local_exprs.insert(destination.local, value);
                        condition_facts = facts;
                    }
                    Some(ConditionCallPremise::Unstated(reason)) => {
                        // The condition reads a value the program determines and
                        // no premise constrains, so no model of a VC assuming it
                        // is a run of the program.
                        let resolved = call_spec_ctx.and_then(|ctx| {
                            resolve_loop_condition_call_result(ctx, func, args, &local_exprs)
                        });
                        local_exprs.insert(
                            destination.local,
                            resolved.unwrap_or_else(|| PureExpr::Var(dest_name, sort)),
                        );
                        condition_unstated = Some(reason);
                    }
                    None => {
                        let resolved = call_spec_ctx.and_then(|ctx| {
                            resolve_loop_condition_call_result(ctx, func, args, &local_exprs)
                        });
                        local_exprs.entry(destination.local).or_insert_with(|| {
                            resolved.unwrap_or_else(|| PureExpr::Var(dest_name, sort))
                        });
                    }
                }
                for_loop_option_local = Some(destination.local);
            }
            call_hop_switch = Some(*switch_bb);
            let next_data = &body.basic_blocks[*switch_bb];
            // Process the switch block's statements too
            for stmt in &next_data.statements {
                if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
                    if place.projection.is_empty() {
                        let expr = call_spec_ctx
                            .and_then(|ctx| {
                                translate_loop_assignment_rvalue(ctx, body, rvalue, &local_exprs)
                            })
                            .or_else(|| translate_rvalue(rvalue, &local_exprs, Some(body)));
                        if let Some(expr) = expr {
                            local_exprs.insert(place.local, expr);
                        }
                    }
                }
            }
            (*switch_bb, next_data)
        }
        _ => (cond_block, cond_data),
    };

    // Extract condition from the condition block's SwitchInt terminator.
    //
    // For `while (i < n)`, the discriminant is Bool -- use it directly.
    // For `while let Some(_) = b`, the discriminant is an Int (enum discriminant).
    // In that case, determine which SwitchInt value exits the loop and create
    // a boolean comparison `discriminant != exit_value`. (#352)
    let condition = match &cond_data.terminator().kind {
        TerminatorKind::SwitchInt { discr, targets } => {
            if targets.all_targets().len() < 2 {
                None
            } else if operand_is_bool(discr, body) {
                let otherwise_is_body = loop_info.body_blocks.contains(&targets.otherwise());
                let has_exit_edge = !otherwise_is_body
                    || targets
                        .iter()
                        .any(|(_, t)| !loop_info.body_blocks.contains(&t));
                if has_exit_edge {
                    translate_operand(discr, &local_exprs).map(|cond| {
                        if otherwise_is_body {
                            cond
                        } else {
                            PureExpr::UnOp(UnOp::Not, Arc::new(cond))
                        }
                    })
                } else {
                    None
                }
            } else {
                // For for-range loops, prefer the synthesized range condition
                // (`produced.len() < end - start`) over the raw discriminant
                // condition. This must run even when the MIR loop header is the
                // `SwitchInt` block itself; in that shape `for_loop_option_local`
                // is absent but range synthesis can still recover the preceding
                // `Iterator::next` call through the predecessor chain. (#1934, #2171)
                synthesize_for_range_condition(
                    body,
                    loop_info,
                    &local_exprs,
                    &local_to_name,
                    &preds,
                )
                .or_else(|| {
                    for_loop_option_local.and_then(|option_local| {
                        for_loop_discriminant_condition(
                            discr,
                            targets,
                            body,
                            &local_exprs,
                            option_local,
                            &local_to_name,
                        )
                    })
                })
                .or_else(|| whilelet_condition(discr, targets, body, &local_exprs, loop_info))
            }
        }
        _ => None,
    };
    // Track whether the condition was extracted from a body-break pattern.
    // `condition_switch` names the `SwitchInt` block whose in-body arm
    // establishes the condition (header switch / body-break switch); `None`
    // when no single switch does (synthesized for-range condition).
    let (mut condition, condition_is_body_break, condition_switch) = if condition.is_some() {
        (condition, false, Some(cond_block)) // Priority 1: header condition
    } else if let Some((break_bb, body_cond)) =
        find_body_break_condition(body, loop_info, &local_exprs, all_loops)
    {
        (Some(body_cond), true, Some(break_bb)) // Priority 2: body-break condition
    } else if let Some(range_cond) =
        synthesize_for_range_condition(body, loop_info, &local_exprs, &local_to_name, &preds)
    {
        (Some(range_cond), false, None) // Priority 3: for-range (header-like)
    } else {
        (None, false, None)
    };
    // Only a condition read at the switch the call feeds reads its value.
    if condition.is_none() || condition_is_body_break || condition_switch != call_hop_switch {
        condition_unstated = None;
    }

    let mut modified_vars = extract_modified_vars(body, loop_info, &local_to_name);
    let mut changed_places = extract_changed_places(body, loop_info, &local_to_name);
    let body_effect_local_exprs = {
        let mut exprs = local_exprs.clone();
        let modified_set: HashSet<&str> = modified_vars.iter().map(String::as_str).collect();
        for (local, name) in &local_to_name {
            if modified_set.contains(name.as_str()) {
                let sort = sort_for_local(*local);
                exprs.insert(*local, PureExpr::Var(name.clone(), sort));
            }
        }
        exprs
    };

    // Compute inner (nested) loops: loops whose header is inside this loop's
    // body but is not this loop's own header.
    let inner_loops: Vec<(BasicBlock, HashSet<BasicBlock>)> = all_loops
        .unwrap_or(&[])
        .iter()
        .filter(|other| {
            other.header != loop_info.header && loop_info.body_blocks.contains(&other.header)
        })
        .map(|other| (other.header, other.body_blocks.clone()))
        .collect();

    // Extract body effects by symbolic execution of the loop body
    let mut body_fx = extract_body_effects(
        body,
        &loop_info.body_blocks,
        loop_info.header,
        &body_effect_local_exprs,
        &local_to_name,
        inner_loops,
        call_spec_ctx.copied(),
    );

    // For Creusot-style for-loops, synthesize `produced` progression.
    if let Some((produced_name, produced_effect)) =
        synthesize_for_loop_produced_effect(body, loop_info, &local_to_name, call_spec_ctx.copied())
    {
        body_fx
            .effects
            .entry(produced_name.clone())
            .or_insert(produced_effect);
        if !modified_vars.iter().any(|name| name == &produced_name) {
            modified_vars.push(produced_name);
        }
    }

    let (
        mut pre_loop_assignments,
        unresolved_pre_loop_calls,
        pre_loop_written_params,
        ref_source_locals,
    ) = extract_pre_loop_assignments(body, arg_names, loop_info, call_spec_ctx.map(|c| c.tcx));
    pre_loop_extract::drop_bindings_rewritten_by_enclosing_loops(
        body,
        loop_info,
        all_loops,
        &local_to_name,
        &mut pre_loop_assignments,
    );
    // A call whose result or reads depend on the path to the header states
    // its facts for one path only (D-243).
    let set_on_one_path = pre_loop_extract::drop_bindings_set_on_one_path(
        body,
        loop_info,
        &local_to_name,
        &mut pre_loop_assignments,
    );
    let unresolved_pre_loop_calls: Vec<_> = unresolved_pre_loop_calls
        .into_iter()
        .filter(|call| {
            !set_on_one_path.contains(&call.dest_local)
                && call
                    .receiver_local
                    .is_none_or(|local| !set_on_one_path.contains(&local))
                && call
                    .arg_locals
                    .iter()
                    .flatten()
                    .all(|local| !set_on_one_path.contains(local))
        })
        .collect();

    // prophecy-store: names whose value/pointee a store through a reference
    // (outside this loop's body) may have changed before loop entry.
    let pre_loop_deref_stored_names: HashSet<String> = {
        let mut staleness = crate::mir_analysis::deref_store_staleness::DerefStoreStaleness::new(
            call_spec_ctx.map(|c| c.tcx),
            body,
        );
        let header = rustc_middle::mir::Location {
            block: loop_info.header,
            statement_index: 0,
        };
        let mut named: Vec<(Local, String)> = arg_names
            .iter()
            .enumerate()
            .map(|(i, name)| (Local::from_usize(i + 1), name.clone()))
            .collect();
        for debug in &body.var_debug_info {
            if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &debug.value {
                if place.projection.is_empty() {
                    named.push((place.local, debug.name.to_string()));
                }
            }
        }
        named
            .into_iter()
            .filter(|(local, _)| {
                local.as_usize() < body.local_decls.len()
                    && staleness.store_outside_reaches(*local, header, &loop_info.body_blocks)
            })
            .map(|(_, name)| name)
            .collect()
    };

    let mut for_loop_local_exprs = local_exprs.clone();
    let mut pre_loop_init_facts = Vec::new();
    let mut synthetic_iter_source_names: HashMap<Local, String> = HashMap::new();
    if let Some(spec_ctx) = call_spec_ctx {
        // NOTE: resolve_pre_loop_calls_with_spec_ctx (named bindings) was planned in
        // W2's [INCOMPLETE] 3cf70490 but never defined. Removed to unbreak build.
        // The _locals_ variant below handles Local-keyed resolution.
        let resolved_pre_loop_locals = resolve_pre_loop_call_locals_with_spec_ctx(
            spec_ctx,
            &unresolved_pre_loop_calls,
            &ref_source_locals,
        );
        for (local, expr) in resolved_pre_loop_locals {
            for_loop_local_exprs.insert(local, expr);
        }
        pre_loop_init_facts = resolve_pre_loop_call_facts_with_spec_ctx(
            spec_ctx,
            &unresolved_pre_loop_calls,
            &ref_source_locals,
        );
        if let Some(source_local) = recover_for_loop_iterable_source_local(body, loop_info, &preds)
        {
            if unresolved_pre_loop_calls
                .iter()
                .any(|call| call.dest_local == source_local && call.arg_exprs.is_empty())
            {
                let name = format!("$for_iter_source_{}", loop_info.header.as_u32());
                let sort = sort_for_local(source_local);
                for_loop_local_exprs.insert(source_local, PureExpr::Var(name.clone(), sort));
                synthetic_iter_source_names.insert(source_local, name);
            }
        }
        let synthetic_source_facts = resolve_pre_loop_call_facts_for_local_names_with_spec_ctx(
            spec_ctx,
            &unresolved_pre_loop_calls,
            &ref_source_locals,
            &synthetic_iter_source_names,
        );
        for fact in synthetic_source_facts {
            if !pre_loop_init_facts.contains(&fact) {
                pre_loop_init_facts.push(fact);
            }
        }
        populate_pre_loop_temps(body, loop_info, &local_to_name, &mut for_loop_local_exprs);
    }

    let for_loop_state = extract_for_loop_ghost_state(
        body,
        loop_info,
        &local_to_name,
        &for_loop_local_exprs,
        call_spec_ctx.copied(),
        &preds,
    );
    if let Some(state) = &for_loop_state {
        if let PureExpr::Var(iter_state_name, _) = &state.iter_state {
            body_fx
                .effects
                .entry(iter_state_name.clone())
                .or_insert_with(|| state.iter_state_next.clone());
        } else {
            // Defensive: iter_state should always be a Var from
            // extract_for_loop_ghost_state, but skip gracefully if not
            // to avoid panicking during loop extraction. (#2687)
            debug!(
                "trust-wp: warning: for-loop iterator state is not a variable ({:?}), \
                 skipping iter_state_next effect",
                state.iter_state
            );
        }
    }
    if condition
        .as_ref()
        .is_some_and(is_two_variant_discriminant_tautology)
    {
        if let Some(state) = &for_loop_state {
            condition = range_loop_condition_fallback(state).or(condition);
        }
    }

    // Ensure variables with deref or double-deref body effects are included
    // in modified_vars. (#1295)
    {
        let modified_set: std::collections::HashSet<String> =
            modified_vars.iter().cloned().collect();
        let extra_vars: Vec<String> = body_fx
            .effects
            .keys()
            .chain(body_fx.deref_effects.keys())
            .chain(body_fx.double_deref_effects.keys())
            .filter(|var| !modified_set.contains(var.as_str()))
            .cloned()
            .collect();
        for var in &extra_vars {
            if body_fx.deref_effects.contains_key(var) {
                changed_places
                    .0
                    .entry(var.clone())
                    .and_modify(|t| {
                        t.merge(&ChangedPlacesTree::Deref(Box::new(
                            ChangedPlacesTree::Changed,
                        )));
                    })
                    .or_insert_with(|| {
                        ChangedPlacesTree::Deref(Box::new(ChangedPlacesTree::Changed))
                    });
            } else if body_fx.double_deref_effects.contains_key(var) {
                changed_places
                    .0
                    .entry(var.clone())
                    .and_modify(|t| {
                        t.merge(&ChangedPlacesTree::Deref(Box::new(
                            ChangedPlacesTree::Deref(Box::new(ChangedPlacesTree::Changed)),
                        )));
                    })
                    .or_insert_with(|| {
                        ChangedPlacesTree::Deref(Box::new(ChangedPlacesTree::Deref(Box::new(
                            ChangedPlacesTree::Changed,
                        ))))
                    });
            } else {
                changed_places
                    .0
                    .entry(var.clone())
                    .or_insert(ChangedPlacesTree::Changed);
            }
        }
        modified_vars.extend(extra_vars);
    }

    // Build post-loop local_exprs for return expression extraction (#1709).
    //
    // After the loop, modified variables hold their post-loop (symbolic) values,
    // not their pre-loop concrete values. Without this restoration,
    // `extract_post_loop_return` resolves post-loop references like
    // `Ghost::new(y)` using the pre-loop `local_exprs[y] = Int(0)` instead of
    // `Var("y")`, causing the function-level postcondition to see an
    // unconstrained `result_current = 0` counterexample.
    //
    // A local some loan points at may have been written through that loan
    // before the loop, a write the pre-loop value does not see; it has a value
    // at the exit only as the loop-exit name of a local the loop changes.
    let post_loop_local_exprs = {
        let mut exprs = local_exprs.clone();
        let modified_set: std::collections::HashSet<&str> =
            modified_vars.iter().map(|s| s.as_str()).collect();
        let mut loop_exit_named = HashSet::new();
        for (local, name) in &local_to_name {
            if modified_set.contains(name.as_str()) {
                let sort = sort_for_local(*local);
                exprs.insert(*local, PureExpr::Var(name.clone(), sort));
                loop_exit_named.insert(*local);
            }
        }
        for lent in mutably_lent_locals(call_spec_ctx.map(|ctx| ctx.tcx), body) {
            if !loop_exit_named.contains(&lent) {
                exprs.remove(&lent);
            }
        }
        // A local the loop writes under a name the loop VC does not constrain
        // holds, at the exit, a value its pre-loop one does not describe.
        for written in locals_written_in(body, &loop_info.body_blocks) {
            if !loop_exit_named.contains(&written) {
                exprs.remove(&written);
            }
        }
        exprs
    };
    let return_expr = extract_post_loop_return(
        call_spec_ctx.map(|ctx| ctx.tcx),
        body,
        cond_block,
        loop_info,
        &post_loop_local_exprs,
    );
    let post_loop_deref_writes =
        extract_post_loop_deref_writes(body, cond_block, loop_info, &local_to_name);
    let post_loop_deref_final_values = extract_post_loop_deref_final_values(
        body,
        cond_block,
        loop_info,
        &local_to_name,
        &local_exprs,
    );

    // A for-loop's `Iterator::next` step is stated by the loop's own
    // structural facts (`produces`), not by the call's contract.
    let dropped_premises: Vec<DroppedPremise> = body_fx
        .dropped_premises
        .into_iter()
        .filter(|premise| !(premise.iterator_step && for_loop_state.is_some()))
        .collect();

    // Named `&mut`-borrow → backing-local name map (`bor_k → k`), restricted to
    // pairs where both ends are named user locals. (cc/fmap layer d)
    let borrow_backing_names: HashMap<String, String> = ref_source_locals
        .iter()
        .filter_map(|(borrow_local, backing_local)| {
            let borrow_name = local_to_name.get(borrow_local)?;
            let backing_name = local_to_name.get(backing_local)?;
            Some((borrow_name.clone(), backing_name.clone()))
        })
        .collect();

    LoopBodyExpr {
        condition,
        condition_is_body_break,
        condition_switch,
        modified_vars,
        changed_places,
        body_effects: body_fx.effects,
        deref_body_effects: body_fx.deref_effects,
        double_deref_body_effects: body_fx.double_deref_effects,
        pre_loop_assignments,
        pre_loop_written_params,
        pre_loop_deref_stored_names,
        unresolved_pre_loop_calls,
        ref_source_locals,
        borrow_backing_names,
        pre_loop_init_facts,
        return_expr,
        post_loop_deref_writes,
        post_loop_deref_final_values,
        for_loop_state,
        call_facts: body_fx.call_facts,
        dropped_premises,
        condition_facts,
        condition_unstated,
    }
}

/// What the loop condition may assume about the call on its header path.
enum ConditionCallPremise {
    /// The destination's value, and every postcondition clause stated at it.
    Stated {
        value: PureExpr,
        facts: Vec<PureExpr>,
    },
    /// The contract supplies something about the value that no premise states.
    Unstated(String),
}

/// State the call ending `cond_block`, whose result the loop condition reads,
/// with the body walk's own call modeling.
///
/// The call runs at every iteration's start and once more at the exit, in the
/// state the invariant describes, so its postcondition is a premise of every
/// VC that assumes the condition or its negation. `None` leaves the
/// condition to the iterator machinery (`Iterator::next` is stated by a
/// for-loop's structural facts). A call that writes through a reference
/// changes the state between the invariant's point and the switch, which no
/// VC reading the condition models, so it is unstated.
#[allow(clippy::too_many_arguments)] // one call site; mirrors the walk's inputs
fn state_condition_call<'tcx>(
    ctx: &CallSpecContext<'_, 'tcx>,
    body: &Body<'tcx>,
    loop_info: &LoopInfo,
    local_to_name: &HashMap<Local, String>,
    cond_block: BasicBlock,
    func: &rustc_middle::mir::Operand<'tcx>,
    args: &[rustc_span::Spanned<rustc_middle::mir::Operand<'tcx>>],
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<ConditionCallPremise> {
    let def_id = extract_call_def_id(func);
    let callee = def_id.map_or_else(
        || "the loop condition's call".to_string(),
        |def_id| format!("`{}`", ctx.tcx.def_path_str(def_id)),
    );
    if def_id.is_some_and(|def_id| {
        let method = resolve_trait_method_def_id(ctx.tcx, def_id).unwrap_or(def_id);
        ctx.tcx.def_path_str(method).ends_with("Iterator::next")
    }) {
        return None;
    }
    let writes_through_reference = args.iter().any(|arg| {
        arg.node.ty(&body.local_decls, ctx.tcx).walk().any(|part| {
            part.as_type().is_some_and(|ty| {
                matches!(
                    ty.kind(),
                    rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
                        | rustc_middle::ty::TyKind::RawPtr(_, rustc_middle::ty::Mutability::Mut)
                )
            })
        })
    });
    if writes_through_reference {
        return Some(ConditionCallPremise::Unstated(format!(
            "the effect of {callee}, which the loop condition calls with a mutable reference"
        )));
    }
    let stated = body_effects::condition_call_value(
        body,
        &loop_info.body_blocks,
        loop_info.header,
        local_to_name,
        *ctx,
        cond_block,
        local_exprs,
    )?;
    if let Some(dropped) = stated.dropped.into_iter().next() {
        return Some(ConditionCallPremise::Unstated(dropped.what));
    }
    match stated.value {
        Some(value) => Some(ConditionCallPremise::Stated {
            value,
            facts: stated.facts,
        }),
        None => Some(ConditionCallPremise::Unstated(format!(
            "the value {callee} returns to the loop condition"
        ))),
    }
}

fn translate_loop_assignment_rvalue<'tcx>(
    ctx: &CallSpecContext<'_, 'tcx>,
    body: &Body<'tcx>,
    rvalue: &rustc_middle::mir::Rvalue<'tcx>,
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<PureExpr> {
    translate_rvalue_typed(ctx.tcx, rvalue, local_exprs, Some(body)).or_else(|| match rvalue {
        rustc_middle::mir::Rvalue::Ref(_, _, place)
        | rustc_middle::mir::Rvalue::CopyForDeref(place) => {
            translate_typed_field_place(ctx.tcx, body, place, local_exprs)
        }
        _ => None,
    })
}

fn resolve_loop_condition_call_result<'tcx>(
    ctx: &CallSpecContext<'_, 'tcx>,
    func: &rustc_middle::mir::Operand<'tcx>,
    args: &[rustc_span::Spanned<rustc_middle::mir::Operand<'tcx>>],
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<PureExpr> {
    let def_id = extract_call_def_id(func)?;
    let path = ctx.tcx.def_path_str(def_id);
    let trait_path =
        resolve_trait_method_def_id(ctx.tcx, def_id).map(|id| ctx.tcx.def_path_str(id));
    let method_name = trait_path
        .as_deref()
        .and_then(|path| path.rsplit("::").next())
        .or_else(|| path.rsplit("::").next())?;

    if method_name != "len" {
        return None;
    }

    let receiver = args
        .first()
        .and_then(|arg| translate_operand(&arg.node, local_exprs))?;

    Some(PureExpr::MethodCall {
        receiver: Arc::new(PureExpr::View(Arc::new(receiver))),
        method: "len".to_string(),
        args: vec![],
    })
}

fn resolve_condition_predecessor_call_results<'tcx>(
    ctx: &CallSpecContext<'_, 'tcx>,
    body: &Body<'tcx>,
    cond_block: BasicBlock,
    preds: &HashMap<BasicBlock, Vec<BasicBlock>>,
    local_exprs: &mut HashMap<Local, PureExpr>,
) {
    let Some(pred_blocks) = preds.get(&cond_block) else {
        return;
    };

    for pred in pred_blocks {
        let pred_data = &body.basic_blocks[*pred];
        for stmt in &pred_data.statements {
            if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
                if place.projection.is_empty() {
                    if let Some(expr) =
                        translate_loop_assignment_rvalue(ctx, body, rvalue, local_exprs)
                    {
                        local_exprs.insert(place.local, expr);
                    }
                }
            }
        }

        let TerminatorKind::Call {
            func,
            args,
            target: Some(target),
            destination,
            ..
        } = &pred_data.terminator().kind
        else {
            continue;
        };
        if *target != cond_block || !destination.projection.is_empty() {
            continue;
        }
        if let Some(resolved) = resolve_loop_condition_call_result(ctx, func, args, local_exprs) {
            local_exprs.insert(destination.local, resolved);
        }
    }
}

fn is_eq_int(expr: &PureExpr) -> Option<(&PureExpr, i64)> {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Eq, rhs) => match rhs.as_ref() {
            PureExpr::Int(value) => Some((lhs.as_ref(), *value)),
            _ => None,
        },
        _ => None,
    }
}

fn is_two_variant_discriminant_tautology(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Or, rhs) => {
            let Some((lhs_discr, lhs_value)) = is_eq_int(lhs) else {
                return false;
            };
            let Some((rhs_discr, rhs_value)) = is_eq_int(rhs) else {
                return false;
            };
            lhs_discr == rhs_discr && lhs_value != rhs_value
        }
        _ => false,
    }
}

fn range_loop_condition_fallback(state: &ForLoopGhostState) -> Option<PureExpr> {
    match &state.loop_elem {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "start_log" && args.is_empty() && receiver.as_ref() == &state.iter_state => {
            Some(PureExpr::BinOp(
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(state.iter_state.clone()),
                    method: "start_log".to_string(),
                    args: vec![],
                }),
                BinOp::Lt,
                Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(state.iter_old.clone()),
                    method: "end_log".to_string(),
                    args: vec![],
                }),
            ))
        }
        _ => None,
    }
}

fn populate_pre_loop_temps(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    local_to_name: &HashMap<Local, String>,
    local_exprs: &mut HashMap<Local, PureExpr>,
) {
    let mut visited: HashSet<BasicBlock> = HashSet::new();
    let mut worklist = vec![BasicBlock::from_u32(0)];
    while let Some(bb) = worklist.pop() {
        if loop_info.body_blocks.contains(&bb) || !visited.insert(bb) {
            continue;
        }
        let bb_data = &body.basic_blocks[bb];
        for stmt in &bb_data.statements {
            if let StatementKind::Assign((place, rvalue)) = &stmt.kind {
                if place.projection.is_empty() {
                    // Don't overwrite symbolic Var entries for named locals.
                    if local_to_name.contains_key(&place.local) {
                        continue;
                    }
                    if let Some(expr) = translate_rvalue(rvalue, local_exprs, Some(body)) {
                        local_exprs.insert(place.local, expr);
                    }
                }
            }
        }
        for succ in bb_data.terminator().successors() {
            worklist.push(succ);
        }
    }
}

#[cfg(test)]
mod changed_places_tests {
    use super::{ChangedPlaces, ChangedPlacesTree};

    fn field(idx: u32, tree: ChangedPlacesTree) -> ChangedPlacesTree {
        let mut fields = std::collections::BTreeMap::new();
        fields.insert(idx, tree);
        ChangedPlacesTree::Fields(fields)
    }

    fn deref(tree: ChangedPlacesTree) -> ChangedPlacesTree {
        ChangedPlacesTree::Deref(Box::new(tree))
    }

    #[test]
    fn merge_changed_absorbs_everything() {
        let mut a = field(0, ChangedPlacesTree::Changed);
        a.merge(&ChangedPlacesTree::Changed);
        assert!(a.is_fully_changed());
    }

    #[test]
    fn merge_fields_union() {
        let mut a = field(0, ChangedPlacesTree::Changed);
        let b = field(1, ChangedPlacesTree::Changed);
        a.merge(&b);
        match &a {
            ChangedPlacesTree::Fields(fields) => {
                assert!(fields.contains_key(&0));
                assert!(fields.contains_key(&1));
                assert_eq!(fields.len(), 2);
            }
            other => panic!("expected Fields, got: {other:?}"),
        }
    }

    #[test]
    fn merge_overlapping_fields_recurse() {
        let mut a = field(0, field(1, ChangedPlacesTree::Changed));
        let b = field(0, field(2, ChangedPlacesTree::Changed));
        a.merge(&b);
        match &a {
            ChangedPlacesTree::Fields(outer) => match outer.get(&0) {
                Some(ChangedPlacesTree::Fields(inner)) => {
                    assert!(inner.contains_key(&1));
                    assert!(inner.contains_key(&2));
                }
                other => panic!("expected nested Fields, got: {other:?}"),
            },
            other => panic!("expected Fields, got: {other:?}"),
        }
    }

    #[test]
    fn merge_deref_recurse() {
        let mut a = deref(field(0, ChangedPlacesTree::Changed));
        let b = deref(field(1, ChangedPlacesTree::Changed));
        a.merge(&b);
        match &a {
            ChangedPlacesTree::Deref(inner) => match inner.as_ref() {
                ChangedPlacesTree::Fields(fields) => {
                    assert!(fields.contains_key(&0));
                    assert!(fields.contains_key(&1));
                }
                other => panic!("expected Fields inside Deref, got: {other:?}"),
            },
            other => panic!("expected Deref, got: {other:?}"),
        }
    }

    #[test]
    fn merge_incompatible_shapes_becomes_changed() {
        let mut a = field(0, ChangedPlacesTree::Changed);
        let b = deref(ChangedPlacesTree::Changed);
        a.merge(&b);
        assert!(a.is_fully_changed());
    }

    #[test]
    fn is_field_unchanged_for_unmentioned_field() {
        let tree = field(0, ChangedPlacesTree::Changed);
        assert!(!tree.is_field_unchanged(0), "field 0 is changed");
        assert!(tree.is_field_unchanged(1), "field 1 should be unchanged");
        assert!(tree.is_field_unchanged(2), "field 2 should be unchanged");
    }

    #[test]
    fn is_field_unchanged_fully_changed() {
        let tree = ChangedPlacesTree::Changed;
        assert!(!tree.is_field_unchanged(0));
        assert!(!tree.is_field_unchanged(1));
    }

    #[test]
    fn changed_places_is_modified_and_unchanged() {
        let mut cp = ChangedPlaces::default();
        cp.0.insert("i".to_string(), ChangedPlacesTree::Changed);
        assert!(cp.is_modified("i"));
        assert!(!cp.is_modified("n"));
        assert!(cp.is_unchanged("n"));
        assert!(!cp.is_unchanged("i"));
    }

    #[test]
    fn changed_places_to_modified_vars() {
        let mut cp = ChangedPlaces::default();
        cp.0.insert("i".to_string(), ChangedPlacesTree::Changed);
        cp.0.insert("x".to_string(), deref(ChangedPlacesTree::Changed));
        let mut vars = cp.to_modified_vars();
        vars.sort();
        assert_eq!(vars, vec!["i", "x"]);
    }
}

#[cfg(test)]
mod tests;
