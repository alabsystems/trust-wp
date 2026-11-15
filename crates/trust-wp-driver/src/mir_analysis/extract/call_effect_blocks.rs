// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Block-scoped call effect collection for assumption/obligation filtering.
//!
//! This module provides [`collect_call_effects_for_blocks`], a generalized
//! version of [`super::loop_body::collect_loop_body_call_obligations`] that
//! collects **full** [`CallEffects`] (obligations + assumptions) from a given
//! set of basic blocks.
//!
//! Used by `callbacks/parsing/extraction.rs` to filter loop-body call
//! assumptions out of the function-level verification path. (#2496)
//!
//! ## Why a separate module?
//!
//! `loop_body.rs` collects obligations only (for loop induction). This module
//! collects full effects (for function-level filtering). The setup logic
//! (local_exprs seeding, pre-target walk) is duplicated rather than extracted
//! because the two modules have different callers and different evolution
//! paths.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Location, StatementKind, TerminatorKind},
    ty::TyCtxt,
};
use trust_wp_core::formula::{PureExpr, UnOp};
use trust_wp_driver::StdSpec;

use super::{
    super::{
        call_resolve::{
            arg_names_for_def_id, extract_call_def_id, resolve_trait_method_def_id,
            ufcs_path_for_call,
        },
        effects::{fail_closed_marker, CallEffects},
        spec_apply::{apply_postconditions_with_effects, collect_precondition_obligations},
        translate::{translate_rvalue_typed, ty_to_expr_sort_enriched},
    },
    call_effect_paths::path_bindings_before_loops,
    call_effect_reach::{facts_where_their_block_runs, scope_effects_to_block_reach},
    helpers::{
        block_diverges_via_panic, switch_discr_is_value_stable, translate_rvalue_with_enum_variants,
    },
    loop_body::switch_branch_conditions,
    past_loop_names::PastLoopNames,
    translate_call_args_for_substitutions_with_tcx,
};
use crate::trait_credit::{lookup_user_or_trait_spec, GrantSite};

/// Whether [`collect_call_effects_for_blocks`] states the value a local set on
/// one path holds where a loop is entered (D-243).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LoopEntryValues {
    /// For premises read at a loop's entry or after the loops: the
    /// function-level VC and a loop's initiation.
    Stated,
    /// For premises that reach a goal inside a loop, where the bare name is
    /// the value on the current pass.
    Omitted,
}

/// Collect full call effects (obligations + postcondition-derived assumptions)
/// from a specified set of basic blocks. (#2496)
///
/// This is the generalized version of `collect_loop_body_call_obligations`:
/// instead of returning only precondition obligations, it returns a complete
/// [`CallEffects`] including postcondition-derived assumptions.
///
/// Used to compute non-loop call effects for function-level verification,
/// ensuring that loop-body assumptions don't leak into the post-loop VC.
///
/// # Arguments
/// * `allowed_blocks` - Set of basic blocks to walk (typically non-loop blocks)
/// * `loop_lane_owned_blocks` - Off-body (must-diverge) blocks the loop lane's
///   guarded walk processed (`LoopBodyObligations::off_body_blocks`); empty
///   when no loop lane runs. Only these may be left to the loop lane.
///
/// * `loop_entry_values` - Whether the assumptions also state the value a
///   local set on one path holds where a loop is entered (D-243). Those facts
///   name the local by its bare name, which is its value at the loop's entry
///   (and, for a local nothing changes from there on, after the loop) but not
///   its value on a later pass: a caller whose premises reach a goal inside a
///   loop omits them.
///
/// Note: mapping_closure detection is not replicated here (it requires the
/// full extraction context). Mapping closure filtering is tracked separately.
#[allow(clippy::too_many_arguments)]
pub(crate) fn collect_call_effects_for_blocks<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    allowed_blocks: &HashSet<BasicBlock>,
    loop_lane_owned_blocks: &HashSet<BasicBlock>,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    loop_entry_values: LoopEntryValues,
) -> CallEffects {
    // Name every argument and user variable (same as loop_body.rs).
    let mut local_exprs: HashMap<Local, PureExpr> = HashMap::new();
    let mut local_names: HashMap<Local, String> = HashMap::new();
    let param_locals: HashSet<Local> = (0..arg_names.len())
        .map(|i| Local::from_usize(i + 1))
        .collect();

    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
        local_exprs.insert(local, PureExpr::Var(name.clone(), sort));
        local_names.insert(local, name.clone());
    }

    // Seed with debug info variable names for symbolic resolution.
    for var_debug in &body.var_debug_info {
        if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &var_debug.value {
            if place.projection.is_empty() && !param_locals.contains(&place.local) {
                let name = var_debug.name.to_string();
                let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[place.local].ty);
                local_exprs.insert(place.local, PureExpr::Var(name.clone(), sort));
                local_names.insert(place.local, name);
            }
        }
    }

    // Code after a loop is read with the loop-exit names, never with a value
    // bound before the loop (D-235).
    let past_loop = PastLoopNames::new(tcx, body);
    let mut past_exprs = local_exprs.clone();

    // Code before every loop is read path by path: the bindings at each
    // block's terminator merge its predecessors' (D-243), so at a join no
    // arm's value stands for the other arm's.
    // A call before every loop names its result by a symbol of its site. The
    // site's name is the destination's bare name where the destination keeps
    // the result at every point this slice is read: nothing changes the local
    // again before a loop is entered (D-243 (f)), and, when the slice's
    // premises are read after a later loop, no such loop may change it
    // (D-244). Every premise, goal and join definition that reads the result
    // then reads the one name, so the choice is made once for the whole
    // dependency closure, and a name is never equated with a value the local
    // loses.
    let result_at = |bb: BasicBlock, local: Local| {
        let rebound = !past_loop.is_past_a_loop(bb)
            && (past_loop.changed_again_before_the_loops(bb, local)
                || past_loop.slice_runs_after_a_later_loop(bb, allowed_blocks)
                    && past_loop.later_loop_may_change(bb, local));
        if rebound {
            let name = local_names.get(&local).map_or("", String::as_str);
            PureExpr::Var(
                format!("{name}$walk_call{}_{}", bb.as_u32(), local.as_u32()),
                ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty),
            )
        } else {
            call_result_local_expr(tcx, body, local, &local_names)
        }
    };
    // A premise recorded for block `site` that reads a name a later loop may
    // change, in a slice whose premises are read after that loop, states the
    // name's value at the site about its value at that loop's exit: it is
    // retired (D-243 (c), D-244). The names are the ones the walk spells for
    // a local, a pointer's included (a premise over `*p` reads `p`); a call
    // result is anchored by `result_at` above, so the names that remain are a
    // parameter's, a pointer's, and a projection destination's base.
    let mut locals_of_name: HashMap<String, Vec<Local>> = HashMap::new();
    for (&local, name) in &local_names {
        locals_of_name.entry(name.clone()).or_default().push(local);
    }
    for local in body.local_decls.indices() {
        if !local_names.contains_key(&local) {
            locals_of_name
                .entry(format!("$_call_{}", local.as_u32()))
                .or_default()
                .push(local);
        }
    }
    let retired_by_a_later_loop = |site: BasicBlock, premise: &PureExpr| {
        past_loop.slice_runs_after_a_later_loop(site, allowed_blocks)
            && premise.free_vars().iter().any(|name| {
                locals_of_name.get(name).is_some_and(|locals| {
                    locals
                        .iter()
                        .any(|&local| past_loop.later_loop_may_change(site, local))
                })
            })
    };
    let mut paths = path_bindings_before_loops(
        tcx,
        body,
        allowed_blocks,
        &past_loop,
        &local_exprs,
        &local_names,
        &param_locals,
        &result_at,
    );

    // After a loop a local is its loop-exit name, unless its one definition
    // in the body is there: then every read sees that definition. A call's
    // result is its own symbol, as the entry walk names it.
    // In reverse postorder a definition is resolved before the reads it
    // dominates, so a local defined from another one after the loop is bound
    // through that one's definition, not its name.
    let past_blocks: Vec<BasicBlock> = body
        .basic_blocks
        .reverse_postorder()
        .iter()
        .copied()
        .filter(|bb| allowed_blocks.contains(bb) && past_loop.is_past_a_loop(*bb))
        .collect();
    let mut changed = true;
    while changed {
        changed = false;
        for &bb in &past_blocks {
            let data = &body.basic_blocks[bb];
            for stmt in &data.statements {
                let StatementKind::Assign((place, _)) = &stmt.kind else {
                    continue;
                };
                let Some(rvalue) = past_loop.single_past_definition(place.local) else {
                    continue;
                };
                if past_exprs
                    .get(&place.local)
                    .is_some_and(|bound| !matches!(bound, PureExpr::Var(name, _) if local_names.get(&place.local) == Some(name)))
                {
                    continue;
                }
                if let Some(expr) = translate_rvalue_with_enum_variants(
                    tcx,
                    rvalue,
                    &past_exprs,
                    Some(body),
                    None,
                    None,
                )
                .or_else(|| translate_rvalue_typed(tcx, rvalue, &past_exprs, Some(body)))
                {
                    if past_exprs.get(&place.local) != Some(&expr) {
                        past_exprs.insert(place.local, expr);
                        changed = true;
                    }
                }
            }
            if let TerminatorKind::Call { destination, .. } = &data.terminator().kind {
                if destination.projection.is_empty() && !param_locals.contains(&destination.local) {
                    past_exprs.entry(destination.local).or_insert_with(|| {
                        call_result_local_expr(tcx, body, destination.local, &local_names)
                    });
                }
            }
        }
    }

    let mut effects = CallEffects::new();
    // The block each obligation / assumption was recorded for (parallel to
    // `effects.obligations` / `effects.assumptions`), for the flow-sensitive
    // premise guards applied after the walk.
    let mut obligation_blocks: Vec<BasicBlock> = Vec::new();
    let mut assumption_blocks: Vec<BasicBlock> = Vec::new();
    let mut previous_bb: Option<BasicBlock> = None;

    // Walk allowed blocks collecting call effects.
    for &bb in allowed_blocks {
        // Entries recorded since the last attribution belong to the block
        // walked just before this one (every `continue` below precedes any
        // push, and a `truncate` only removes the current block's entries).
        if let Some(owner) = previous_bb {
            record_effect_blocks(
                &effects,
                owner,
                &mut obligation_blocks,
                &mut assumption_blocks,
            );
        }
        previous_bb = Some(bb);
        let bb_data = &body.basic_blocks[bb];
        let Some(ref terminator) = bb_data.terminator else {
            continue;
        };
        let past = past_loop.is_past_a_loop(bb);
        // A block the path walk did not reach (an unwind) reads every local
        // by its name alone.
        let local_exprs = if past {
            &past_exprs
        } else {
            paths.at_terminator.get(&bb).unwrap_or(&local_exprs)
        };

        // A switch arm that diverges into a panic entry point
        // (`assert!`, `assert_eq!`, `panic!`, `unreachable!`) must be PROVED
        // unreachable. The obligation is owed where this block runs: it is
        // guarded by the block's reach condition after the walk
        // (`scope_effects_to_block_reach`, D-243), and stays unconditional
        // where there is none (strictly stronger). An untranslatable branch
        // condition fails closed as `false`.
        if let TerminatorKind::SwitchInt { discr, targets } = &terminator.kind {
            let mut branch_conditions = None;
            for target in targets.all_targets() {
                if !block_diverges_via_panic(tcx, body, *target) {
                    continue;
                }
                // Flow-insensitive resolution pins user variables to their
                // symbolic names and keeps a temporary's first assignment, so
                // stability is checked in its strict mode; an unstable
                // condition fails closed as `false`.
                let conditions = branch_conditions.get_or_insert_with(|| {
                    if switch_discr_is_value_stable(tcx, body, discr, true) {
                        switch_branch_conditions(discr, targets, local_exprs, body, None)
                            .unwrap_or_default()
                    } else {
                        HashMap::new()
                    }
                });
                effects.obligations.push(
                    conditions
                        .get(target)
                        .map(|cond| PureExpr::UnOp(UnOp::Not, Arc::new(cond.clone())))
                        .unwrap_or_else(|| fail_closed_marker("call-effect-switch-no-cond")),
                );
            }
        }

        // An assert on a path that can only DIVERGE (e.g. before a trusted
        // inert spin) has no continuation to carry its check, so it is an
        // obligation here (see `diverging_path_assert_obligation`), in strict
        // (flow-insensitive) stability mode. Its guard is the conjunction of
        // the switch-arm conditions along the block's unique-predecessor
        // chain; a conjunct that is unstable or untranslatable is dropped,
        // which only strengthens the obligation. A chain that enters a block
        // outside this slice is left to the loop lane ONLY when the loop lane
        // provably walked it (see `unique_predecessor_guard`).
        if let TerminatorKind::Assert {
            cond,
            expected,
            msg,
            target,
            ..
        } = &terminator.kind
        {
            if super::helpers::block_must_diverge(body, *target, &mut HashSet::new()) {
                if let Some(guard) = unique_predecessor_guard(
                    tcx,
                    body,
                    bb,
                    allowed_blocks,
                    loop_lane_owned_blocks,
                    local_exprs,
                ) {
                    let obligation = super::assertion::diverging_path_assert_obligation(
                        tcx,
                        body,
                        cond,
                        *expected,
                        msg,
                        local_exprs,
                        true,
                    );
                    effects.obligations.push(match guard {
                        Some(guard) => PureExpr::BinOp(
                            Arc::new(guard),
                            trust_wp_core::formula::BinOp::Implies,
                            Arc::new(obligation),
                        ),
                        None => obligation,
                    });
                }
            }
        }

        // A built-in index bounds check (`a[i]` on an array or slice) is a
        // PROOF obligation (Creusot: `ix@ < self@.len()`), never a fact,
        // owed under the block's reach condition (D-243). An unstable or
        // untranslatable condition fails closed as `false`.
        if let TerminatorKind::Assert {
            cond,
            expected,
            msg,
            ..
        } = &terminator.kind
        {
            if let Some(obligation) = super::assertion::bounds_check_obligation(
                tcx,
                cond,
                *expected,
                msg,
                local_exprs,
                body,
                true,
            ) {
                effects.obligations.push(obligation);
            }
        }

        if let TerminatorKind::Drop { place, .. } = &terminator.kind {
            if let Some(obligation) =
                super::assertion::drop_glue_obligation(tcx, body, place, user_specs)
            {
                effects.obligations.push(obligation);
            }
        }
        if let TerminatorKind::Call { func, .. } = &terminator.kind {
            if let Some(obligation) =
                super::assertion::call_type_obligation(tcx, body, bb, func, user_specs)
            {
                effects.obligations.push(obligation);
            }
        }

        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        {
            if let Some(def_id) = extract_call_def_id(func) {
                let translated_args = translate_call_args_for_substitutions_with_tcx(
                    args,
                    local_exprs,
                    Some(body),
                    Some(tcx),
                );

                let hir_param_names = arg_names_for_def_id(tcx, def_id);

                let extern_opt = if extern_specs.is_empty() {
                    None
                } else {
                    Some(extern_specs)
                };
                let site = GrantSite { tcx, body, func };
                let user_or_trait_spec =
                    lookup_user_or_trait_spec(user_specs, trait_specs, def_id, site);
                let from_user_or_trait_table = user_or_trait_spec.is_some();
                let spec = user_or_trait_spec
                    .cloned()
                    .map(|spec| {
                        crate::logic::identity_typed::instantiate_generic_markers_for_call(
                            tcx, body, func, def_id, spec,
                        )
                    })
                    .or_else(|| {
                        ufcs_path_for_call(tcx, func).and_then(|ufcs_path| {
                            crate::provenance::lookup_spec_for_def(
                                tcx,
                                def_id,
                                crate::provenance::builtin_spec_admission_for_operand(
                                    tcx,
                                    func,
                                    Some(body.source.def_id()),
                                ),
                                extern_opt,
                                &ufcs_path,
                                crate::provenance::CallSite::of_operand(
                                    func,
                                    Some(body.source.def_id()),
                                ),
                            )
                        })
                    })
                    .or_else(|| {
                        let path = tcx.def_path_str(def_id);
                        crate::provenance::lookup_spec_for_def(
                            tcx,
                            def_id,
                            crate::provenance::builtin_spec_admission_for_operand(
                                tcx,
                                func,
                                Some(body.source.def_id()),
                            ),
                            extern_opt,
                            &path,
                            crate::provenance::CallSite::of_operand(
                                func,
                                Some(body.source.def_id()),
                            ),
                        )
                    })
                    .or_else(|| {
                        let trait_method_id = resolve_trait_method_def_id(tcx, def_id)?;
                        let trait_path = tcx.def_path_str(trait_method_id);
                        crate::provenance::lookup_spec_for_def(
                            tcx,
                            trait_method_id,
                            crate::provenance::builtin_spec_admission_for_operand(
                                tcx,
                                func,
                                Some(body.source.def_id()),
                            ),
                            extern_opt,
                            &trait_path,
                            crate::provenance::CallSite::of_operand(
                                func,
                                Some(body.source.def_id()),
                            ),
                        )
                    });

                // After a loop, an argument read at a value other than the
                // one its name has there (a local changed since the loop's
                // exit, a value bound before the loop) is no statement about
                // this call: its precondition fails closed and its
                // postcondition is not assumed (D-235).
                let stale_after_loop =
                    past && spec.is_some() && !past_loop.call_reads_named_values(bb, args);
                if stale_after_loop {
                    // The callee invariants a user or trait spec grants are
                    // obligations over the same arguments.
                    let charges_invariants = from_user_or_trait_table && {
                        let mut charged = CallEffects::new();
                        super::call_spec::charge_callee_invariant_grant(
                            tcx,
                            body,
                            func,
                            def_id,
                            (user_specs, trait_specs),
                            &translated_args,
                            &mut charged,
                        )
                        .map_or(true, |()| !charged.obligations.is_empty())
                    };
                    // A postcondition left out leaves the call's result and
                    // the memory it was lent free; a refutation over them is
                    // no counterexample, so it fails closed as well.
                    if spec
                        .as_ref()
                        .is_some_and(|spec| !spec.requires.is_empty() || !spec.ensures.is_empty())
                        || charges_invariants
                    {
                        effects.record_injected_fail_closed_obligation(
                            "post-loop-call-argument-not-at-call-value",
                        );
                    }
                } else if let Some(spec) = spec {
                    let param_names = hir_param_names.or_else(|| spec.param_names.clone());

                    // Collect precondition obligations.
                    let obligations_before = effects.obligations.len();
                    let user_written_false_before = effects.user_written_false_obligations;
                    collect_precondition_obligations(
                        &spec.requires,
                        &translated_args,
                        param_names.as_deref(),
                        &mut effects,
                    );
                    if from_user_or_trait_table
                        && super::call_spec::charge_callee_invariant_grant(
                            tcx,
                            body,
                            func,
                            def_id,
                            (user_specs, trait_specs),
                            &translated_args,
                            &mut effects,
                        )
                        .is_err()
                    {
                        effects.record_injected_fail_closed_obligation(
                            "trait-call-typeinv-grant-unidentified",
                        );
                    }
                    // prophecy-store: an argument read through a reference
                    // after a store through it (or an alias) denotes the
                    // pointee's ENTRY value here; fail closed.
                    if effects.obligations.len() > obligations_before {
                        let call_location = Location {
                            block: bb,
                            statement_index: bb_data.statements.len(),
                        };
                        let mut staleness =
                            crate::mir_analysis::deref_store_staleness::DerefStoreStaleness::new(
                                Some(tcx),
                                body,
                            );
                        if args
                            .iter()
                            .any(|arg| staleness.operand_may_read_stale(&arg.node, call_location))
                        {
                            effects.obligations.truncate(obligations_before);
                            // The written clauses are DROPPED and replaced by
                            // a marker, so their count goes too (D-27).
                            effects.user_written_false_obligations = user_written_false_before;
                            effects
                                .record_injected_fail_closed_obligation("prophecy-store-stale-arg");
                        }
                    }

                    // Collect postcondition-derived assumptions.
                    // Build the result variable from the call destination.
                    // After a loop, a destination name some other change also
                    // binds (the loop-exit value of `k` in `k = zero()`)
                    // would carry the postcondition to that other value.
                    let conflated_destination = past
                        && !spec.ensures.is_empty()
                        && !past_loop.destination_names_only_this_result(bb, destination);
                    if conflated_destination {
                        effects.record_injected_fail_closed_obligation(
                            "post-loop-call-destination-names-another-value",
                        );
                    }
                    if !spec.ensures.is_empty() && !conflated_destination {
                        let result_var = if destination.projection.is_empty() {
                            result_at(bb, destination.local)
                        } else {
                            call_result_local_expr(tcx, body, destination.local, &local_names)
                        };
                        // A loop after the call that may change a name the
                        // postcondition speaks of is handled with every other
                        // premise once the walk is done (`retired_by_a_later_loop`).
                        apply_postconditions_with_effects(
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
                            &mut effects,
                            true,
                        );
                    }
                }
            }
        }
    }
    if let Some(owner) = previous_bb {
        record_effect_blocks(
            &effects,
            owner,
            &mut obligation_blocks,
            &mut assumption_blocks,
        );
    }
    scope_effects_to_block_reach(
        tcx,
        body,
        &past_loop,
        &paths.at_terminator,
        &past_exprs,
        &mut effects,
        &obligation_blocks,
        &mut assumption_blocks,
    );
    // Retirement reads each premise as it is stated where its block runs,
    // the reach condition included: a guard over a name a later loop changes
    // is read at the loop's exit as well.
    if assumption_blocks.len() == effects.assumptions.len() {
        let mut kept_blocks = Vec::with_capacity(assumption_blocks.len());
        let mut kept = Vec::with_capacity(effects.assumptions.len());
        for (assumption, block) in effects
            .assumptions
            .drain(..)
            .zip(assumption_blocks.drain(..))
        {
            if !retired_by_a_later_loop(block, &assumption) {
                kept.push(assumption);
                kept_blocks.push(block);
            }
        }
        effects.assumptions = kept;
        assumption_blocks = kept_blocks;
    }
    guard_assumptions_by_reaching_obligations(
        body,
        &mut effects,
        &obligation_blocks,
        &assumption_blocks,
    );
    // A join definition is a premise like any other, read wherever the slice
    // reads the symbol: one whose arm value or condition reads a name a later
    // loop may change is retired with the rest, before any premise or goal
    // pulls it in. Its arm's value is then free (D-244).
    paths.retain_definitions(|join, fact| !retired_by_a_later_loop(join, fact));
    // The value a local set on one path holds where a loop is entered, for
    // the name the loop's lane and the code after it read (D-243). A fact
    // about the program's state, not a callee's promise: it is stated where
    // its block runs only.
    if loop_entry_values == LoopEntryValues::Stated {
        let entry_facts = facts_where_their_block_runs(
            tcx,
            body,
            &past_loop,
            &paths.at_terminator,
            &past_exprs,
            paths.loop_entry_values(
                body,
                &past_loop,
                &local_exprs,
                &param_locals,
                !allowed_blocks
                    .iter()
                    .any(|&bb| past_loop.is_past_a_loop(bb)),
            ),
        );
        effects.assumptions.extend(
            entry_facts
                .into_iter()
                .filter(|(block, fact)| !retired_by_a_later_loop(*block, fact))
                .map(|(_, fact)| fact),
        );
    }
    // A join symbol an effect reads is stated with its defining facts, which
    // hold in every execution and so are guarded by nothing.
    let definitions =
        paths.definitions_read_by(effects.obligations.iter().chain(&effects.assumptions));
    effects.assumptions.extend(definitions);

    effects
}

/// Attribute every obligation / assumption recorded but not yet attributed to
/// block `owner`.
fn record_effect_blocks(
    effects: &CallEffects,
    owner: BasicBlock,
    obligation_blocks: &mut Vec<BasicBlock>,
    assumption_blocks: &mut Vec<BasicBlock>,
) {
    let pending_obligations = effects
        .obligations
        .len()
        .saturating_sub(obligation_blocks.len());
    let pending_assumptions = effects
        .assumptions
        .len()
        .saturating_sub(assumption_blocks.len());
    obligation_blocks.extend(std::iter::repeat_n(owner, pending_obligations));
    assumption_blocks.extend(std::iter::repeat_n(owner, pending_assumptions));
}

/// Flow-sensitive premises for this flat, flow-insensitive walker: every
/// assumption recorded for block `B` (a call's postcondition) becomes
/// `obs ==> assumption`, where `obs` is the conjunction of every obligation
/// recorded for a block that can REACH `B` (including `B` itself, whose
/// obligations are the call's own preconditions). An obligation can then
/// never be proved from a postcondition established after it on every path
/// (`let x = v[0]; nonempty(v);`), nor from its own call's postcondition.
/// Obligations of blocks that cannot reach `B` do not precede it on any path
/// and are not guards. SOUND: guarding a premise only removes derivations.
fn guard_assumptions_by_reaching_obligations(
    body: &Body<'_>,
    effects: &mut CallEffects,
    obligation_blocks: &[BasicBlock],
    assumption_blocks: &[BasicBlock],
) {
    if effects.assumptions.is_empty()
        || effects.obligations.is_empty()
        || obligation_blocks.len() != effects.obligations.len()
        || assumption_blocks.len() != effects.assumptions.len()
    {
        // Attribution is incomplete: guard every assumption by every
        // obligation (strongest guard; still sound).
        if !effects.assumptions.is_empty() && !effects.obligations.is_empty() {
            let guard = crate::mir_analysis::effects::conjoin_obligations(&effects.obligations);
            crate::mir_analysis::effects::guard_assumptions(
                &mut effects.assumptions,
                guard.as_ref(),
            );
        }
        return;
    }
    let predecessors = body.basic_blocks.predecessors();
    let mut reaching_cache: HashMap<BasicBlock, HashSet<BasicBlock>> = HashMap::new();
    for (index, assumption) in effects.assumptions.iter_mut().enumerate() {
        let target = assumption_blocks[index];
        let reaching = reaching_cache.entry(target).or_insert_with(|| {
            let mut seen = HashSet::new();
            let mut stack = vec![target];
            while let Some(block) = stack.pop() {
                if seen.insert(block) {
                    stack.extend(predecessors[block].iter().copied());
                }
            }
            seen
        });
        let guards: Vec<PureExpr> = effects
            .obligations
            .iter()
            .zip(obligation_blocks)
            .filter(|(_, block)| reaching.contains(block))
            .map(|(obligation, _)| obligation.clone())
            .collect();
        let guard = crate::mir_analysis::effects::conjoin_obligations(&guards);
        crate::mir_analysis::effects::guard_assumptions(
            std::slice::from_mut(assumption),
            guard.as_ref(),
        );
    }
}

fn call_result_local_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    local: Local,
    local_names: &HashMap<Local, String>,
) -> PureExpr {
    let name = local_names
        .get(&local)
        .cloned()
        .unwrap_or_else(|| format!("$_call_{}", local.as_u32()));
    PureExpr::Var(
        name,
        ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty),
    )
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{HashMap, HashSet},
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    use rustc_driver::{run_compiler, Callbacks, Compilation};
    use rustc_interface::interface::Compiler;

    use super::*;

    static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

    struct CallEffectsCallbacks {
        fn_name: String,
        loop_entry_values: LoopEntryValues,
        assumptions_debug: Option<String>,
        assumptions_display: Vec<String>,
        obligations_debug: Option<String>,
        ran: bool,
    }

    impl Callbacks for CallEffectsCallbacks {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            let suffix = format!("::{}", self.fn_name);

            for local_def_id in tcx.hir_body_owners() {
                let def_path = tcx.def_path_str(local_def_id);
                if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                    continue;
                }

                let body = tcx.optimized_mir(local_def_id.to_def_id());
                let allowed_blocks: HashSet<BasicBlock> = body.basic_blocks.indices().collect();
                let user_specs = HashMap::new();
                let trait_specs = HashMap::new();
                let extern_specs = HashMap::new();
                let effects = collect_call_effects_for_blocks(
                    tcx,
                    body,
                    &["self".to_string()],
                    &allowed_blocks,
                    &HashSet::new(),
                    &user_specs,
                    &trait_specs,
                    &extern_specs,
                    self.loop_entry_values,
                );

                self.assumptions_debug = Some(format!("{:#?}", effects.assumptions));
                self.assumptions_display = effects
                    .assumptions
                    .iter()
                    .map(ToString::to_string)
                    .collect();
                self.obligations_debug = Some(format!("{:#?}", effects.obligations));
                self.ran = true;
                return Compilation::Stop;
            }

            Compilation::Stop
        }
    }

    fn collect_assumptions_debug(source: &str, fn_name: &str) -> String {
        collect_effects_debug(source, fn_name).0
    }

    /// The walker's assumptions and obligations for `fn_name`, debug-printed.
    fn collect_effects_debug(source: &str, fn_name: &str) -> (String, String) {
        collect_effects_debug_with(source, fn_name, LoopEntryValues::Stated)
    }

    /// [`collect_effects_debug`] with the loop-entry values stated or omitted.
    fn collect_effects_debug_with(
        source: &str,
        fn_name: &str,
        loop_entry_values: LoopEntryValues,
    ) -> (String, String) {
        let (assumptions, _, obligations) =
            collect_effects_with(source, fn_name, loop_entry_values);
        (assumptions, obligations)
    }

    /// The walker's assumptions, each displayed as a formula, with the loop
    /// entry values stated.
    fn collect_assumptions_display(source: &str, fn_name: &str) -> Vec<String> {
        collect_effects_with(source, fn_name, LoopEntryValues::Stated).1
    }

    /// The walker's assumptions (debug-printed and displayed) and obligations.
    fn collect_effects_with(
        source: &str,
        fn_name: &str,
        loop_entry_values: LoopEntryValues,
    ) -> (String, Vec<String>, String) {
        let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_call_effect_blocks_{}_{}",
            std::process::id(),
            unique
        ));
        fs::create_dir_all(&temp_dir).expect("create test temp dir");

        let source_path = temp_dir.join("test.rs");
        fs::write(&source_path, source).expect("write test source");

        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_call_effect_blocks_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];

        let mut callbacks = CallEffectsCallbacks {
            fn_name: fn_name.to_string(),
            loop_entry_values,
            assumptions_debug: None,
            assumptions_display: Vec::new(),
            obligations_debug: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);

        let _ = fs::remove_dir_all(&temp_dir);

        assert!(callbacks.ran, "failed to locate function `{fn_name}`");
        (
            callbacks
                .assumptions_debug
                .expect("call effects should be collected"),
            callbacks.assumptions_display,
            callbacks
                .obligations_debug
                .expect("call effects should be collected"),
        )
    }

    #[test]
    fn pre_loop_vec_len_assumption_preserves_typed_field_receiver() {
        let source = r#"
pub struct MyMap {
    buckets: Vec<i32>,
}

impl MyMap {
    pub fn resize(&mut self) -> usize {
        let n = self.buckets.len();
        n * 2
    }
}
"#;

        let assumptions = collect_assumptions_debug(source, "resize");

        assert!(
            assumptions.contains("__trust_wp_field_buckets"),
            "Vec::len postcondition should be tied to self.buckets, got {assumptions}"
        );
        assert!(
            !assumptions.contains("\"arg0\""),
            "Vec::len receiver should not fall back to arg0, got {assumptions}"
        );
    }

    /// A goal owed on one arm is owed under that arm's edge (D-243).
    #[test]
    fn goal_on_one_arm_is_owed_under_its_edge() {
        let source = r#"
pub fn f(a: [u32; 4], i: usize, flag: bool) -> u32 {
    let mut n = 0;
    if flag {
        n = a[i];
    }
    n
}
"#;

        let (_, obligations) = collect_effects_debug(source, "f");

        assert!(
            obligations.contains("Implies") && obligations.contains("\"flag\""),
            "the bounds check should be owed under the arm's edge, got {obligations}"
        );
    }

    /// A local two arms bind apart is a symbol of the join, defined arm by
    /// arm, never the value of the arm walked first (D-243).
    #[test]
    fn join_value_is_defined_by_the_arm_that_reaches_it() {
        let source = r#"
pub fn f(a: Vec<i32>, b: Vec<i32>, flag: bool) -> usize {
    let w = if flag { a } else { b };
    w.len()
}
"#;

        let assumptions = collect_assumptions_debug(source, "f");

        assert!(
            assumptions.contains("w$walk_join"),
            "Vec::len should read the join symbol, got {assumptions}"
        );
        // The harness names the first parameter `self`.
        assert!(
            assumptions.contains("Implies")
                && assumptions.contains("\"self\"")
                && assumptions.contains("\"b\"")
                && assumptions.contains("\"flag\""),
            "the join symbol should be defined by each arm, got {assumptions}"
        );
    }

    /// A postcondition recorded on one arm is a premise only under that
    /// arm's edge (D-243).
    #[test]
    fn callee_post_on_one_arm_is_scoped_to_its_edge() {
        let source = r#"
pub fn f(v: Vec<i32>, flag: bool) -> usize {
    let mut n = 0;
    if flag {
        n = v.len();
    }
    n
}
"#;

        let assumptions = collect_assumptions_debug(source, "f");

        assert!(
            assumptions.contains("Implies") && assumptions.contains("\"flag\""),
            "Vec::len postcondition should be guarded by the arm's edge, got {assumptions}"
        );
    }

    /// A call whose destination changes again before the loop names its
    /// result by a symbol of its site; one whose destination keeps the result
    /// names it by the destination (D-243).
    #[test]
    fn call_result_rebound_before_the_loop_is_a_site_symbol() {
        let rebound = r#"
pub fn f(v: Vec<i32>, flag: bool) -> usize {
    let mut n = v.len();
    if flag {
        n = 5;
    }
    let mut i = 0usize;
    while i < 3 {
        i += 1;
    }
    n
}
"#;
        let assumptions = collect_assumptions_debug(rebound, "f");
        assert!(
            assumptions.contains("n$walk_call"),
            "Vec::len's result should be a symbol of its site, got {assumptions}"
        );

        let kept = r#"
pub fn f(v: Vec<i32>) -> usize {
    let n = v.len();
    let mut i = 0usize;
    while i < 3 {
        i += 1;
    }
    n
}
"#;
        let assumptions = collect_assumptions_debug(kept, "f");
        assert!(
            assumptions.contains("\"n\"") && !assumptions.contains("$walk_call"),
            "Vec::len's result should be named by its destination, got {assumptions}"
        );
    }

    /// A call whose destination a later loop changes names its result by a
    /// symbol of its site in a slice read after that loop, so the premise
    /// and every join definition reading the result read one value (D-244).
    #[test]
    fn call_result_a_later_loop_changes_is_a_site_symbol() {
        let source = r#"
pub fn f(v: Vec<i32>) -> usize {
    let mut n = v.len();
    let mut i = 0usize;
    while i < 3 {
        n = 0;
        i += 1;
    }
    n
}
"#;
        let assumptions = collect_assumptions_debug(source, "f");
        assert!(
            assumptions.contains("n$walk_call") && !assumptions.contains("\"n\""),
            "Vec::len's result should be a symbol of its site, got {assumptions}"
        );
    }

    /// A join definition whose arm value reads a name a later loop may
    /// change is retired; the other arm's is kept (D-244).
    #[test]
    fn join_definition_reading_a_name_a_later_loop_changes_is_retired() {
        let source = r#"
pub fn f(mut a: Vec<i32>, b: Vec<i32>, flag: bool) -> usize {
    let w = if flag { a } else { b };
    let n = w.len();
    a = Vec::new();
    let mut i = 0usize;
    while i < 3 {
        a = Vec::new();
        i += 1;
    }
    drop(a);
    n
}
"#;
        let assumptions = collect_assumptions_display(source, "f");
        // The harness names the first parameter `self`.
        assert!(
            assumptions
                .iter()
                .any(|fact| fact.contains("w$walk_join") && fact.contains(" b)")),
            "the arm that reads `b` should define the join, got {assumptions:?}"
        );
        assert!(
            !assumptions.iter().any(|fact| fact.contains("== self)")),
            "no premise should equate the join with `self`, which the loop reassigns, \
             got {assumptions:?}"
        );
    }

    /// Each arm of an `if` / `else if` / `else` chain meeting at one join is
    /// told apart by the switch of its nearest common dominator (D-244).
    #[test]
    fn join_of_an_else_if_chain_is_defined_arm_by_arm() {
        let source = r#"
pub fn f(k: u32, x: Vec<i32>, y: Vec<i32>, z: Vec<i32>) -> usize {
    let a = if k == 0 { x } else if k == 1 { y } else { z };
    a.len()
}
"#;
        let assumptions = collect_assumptions_display(source, "f");
        for arm in [" x)", " y)", " z)"] {
            assert!(
                assumptions
                    .iter()
                    .any(|fact| fact.contains("a$walk_join") && fact.contains(arm)),
                "the arm ending in `{arm}` should define the join, got {assumptions:?}"
            );
        }
    }

    /// A switch on a local that one arm then reassigns reads the local's
    /// value at the switch: a premise on that arm is scoped by it (D-244).
    #[test]
    fn switch_on_a_local_an_arm_reassigns_scopes_the_arm() {
        let source = r#"
pub fn f(n: u32, v: Vec<i32>) -> usize {
    let mut lim = n;
    let mut k = 0usize;
    if lim > 100 {
        lim = 100;
        k = v.len();
    }
    k + lim as usize
}
"#;
        let assumptions = collect_assumptions_display(source, "f");
        assert!(
            assumptions
                .iter()
                .any(|fact| fact.contains("self > 100") && fact.contains("==>")),
            "Vec::len's postcondition should be scoped by the arm's condition, got {assumptions:?}"
        );
    }

    /// An arm whose value is the local's own call result still lets the
    /// other arms state the local's loop-entry value (D-244).
    #[test]
    fn loop_entry_value_beside_an_arm_of_the_locals_own_call_result() {
        let source = r#"
pub fn f(k: u8, v: Vec<i32>) -> usize {
    let a = match k { 0 => v.len(), _ => 7usize };
    let mut i = 0u32;
    while i < 3 {
        i += 1;
    }
    a
}
"#;
        let assumptions = collect_assumptions_display(source, "f");
        assert!(
            assumptions.iter().any(|fact| fact.contains("==> (a == 7)")),
            "the constant arm should state `a`'s entry value, got {assumptions:?}"
        );
        assert!(
            !assumptions.iter().any(|fact| fact.contains("(a == a)")),
            "the call arm states nothing, got {assumptions:?}"
        );
    }

    /// A local two arms bind apart is stated at the loop's entry arm by arm,
    /// for the loop lane's initiation and the code after the loop to read by
    /// its name, unless the caller omits the loop-entry values (D-243).
    #[test]
    fn loop_entry_value_of_a_join_is_stated_arm_by_arm() {
        let source = r#"
pub fn f(flag: bool) -> u32 {
    let m = if flag { 1u32 } else { 2u32 };
    let mut i = 0u32;
    while i < 3 {
        i += 1;
    }
    m
}
"#;

        let stated = collect_effects_debug_with(source, "f", LoopEntryValues::Stated).0;
        // The harness names the first parameter `self`.
        assert!(
            stated.contains("\"m\"")
                && stated.contains("Implies")
                && stated.contains("\"self\"")
                && !stated.contains("m$walk_join"),
            "`m` should be stated at the loop's entry under each arm's condition, got {stated}"
        );
        let omitted = collect_effects_debug_with(source, "f", LoopEntryValues::Omitted).0;
        assert!(
            !omitted.contains("\"m\""),
            "no premise should name `m` when the entry values are omitted, got {omitted}"
        );
    }
}

/// The guard of `bb` along its unique-predecessor chain, for the
/// flow-insensitive walker: the conjunction of the switch-arm conditions of
/// every `SwitchInt` predecessor on the chain (strict value stability; an
/// unstable or untranslatable arm condition contributes no conjunct).
///
/// Returns `None` (the site is the loop lane's) ONLY when the chain enters this
/// slice through a block `current` whose unique predecessor lies outside the
/// slice AND both `current` and `bb` are in `loop_lane_owned_blocks`, i.e. the
/// loop lane's guarded walk processed them. Every execution reaching `bb` then
/// passes through `current` (unique predecessors), and the loop lane emitted
/// the check under that path — condition-free when the loop condition is not
/// established there (loop-exit arms). Returning `None` for ANY must-diverge
/// entry on the assumption that the loop lane walked it is wrong: the loop
/// lane does walk loop-exit tails, but checks them under the assumed loop
/// condition, so `¬cond ⇒ ob` is vacuous there
/// (`s40v4_while_tail_overflow_spin`, `s40v4_loopbreak_tail_overflow_spin`).
/// Otherwise `Some(None)` when no conjunct survives (the obligation is
/// emitted unguarded — strictly stronger).
fn unique_predecessor_guard<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    allowed_blocks: &HashSet<BasicBlock>,
    loop_lane_owned_blocks: &HashSet<BasicBlock>,
    local_exprs: &HashMap<Local, PureExpr>,
) -> Option<Option<PureExpr>> {
    let predecessors = body.basic_blocks.predecessors();
    let mut conjuncts: Vec<PureExpr> = Vec::new();
    let mut seen: HashSet<BasicBlock> = HashSet::new();
    let mut current = bb;
    while seen.insert(current) {
        let [pred] = predecessors[current].as_slice() else {
            break;
        };
        if !allowed_blocks.contains(pred) {
            // The chain enters this slice from outside. Leave the site to the
            // loop lane only if that lane processed both the entry block and
            // the assert block; any other entry is this slice's own: emit with
            // the conjuncts gathered so far (strictly stronger than the full
            // guard).
            if loop_lane_owned_blocks.contains(&current) && loop_lane_owned_blocks.contains(&bb) {
                return None;
            }
            break;
        }
        if let TerminatorKind::SwitchInt { discr, targets } =
            &body.basic_blocks[*pred].terminator().kind
        {
            if switch_discr_is_value_stable(tcx, body, discr, true) {
                if let Some(cond) =
                    switch_branch_conditions(discr, targets, local_exprs, body, None)
                        .and_then(|conditions| conditions.get(&current).cloned())
                {
                    conjuncts.push(cond);
                }
            }
        }
        current = *pred;
    }
    Some(conjuncts.into_iter().reduce(|acc, cond| {
        PureExpr::BinOp(
            Arc::new(acc),
            trust_wp_core::formula::BinOp::And,
            Arc::new(cond),
        )
    }))
}
