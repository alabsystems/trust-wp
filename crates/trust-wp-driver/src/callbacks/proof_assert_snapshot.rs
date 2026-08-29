// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MIR-location keyed proof_assert snapshot construction.
//!
//! A snapshot captures the driver-side symbolic state at a single proof_assert
//! program point. `prepare_proof_assert` consumes this immutable snapshot and
//! no longer reaches into thread-local extraction side channels.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::{
    mir::{
        Body, BorrowKind, Local, Location, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind, VarDebugInfoContents,
    },
    ty::{TyCtxt, TyKind},
};
use rustc_mir_dataflow::Analysis;
use trust_wp_core::{
    contract_parser::parse_contract,
    formula::{internal::tuple_lowering::tuple_field_logic_fn_name, BinOp, ExprSort, PureExpr},
};
use trust_wp_driver::StdSpec;

use super::{
    super::{ghost::GhostBlock, proof_assert::ProofAssert},
    discovery::source_parsing::collect_loop_contract_attrs,
    ghost_context::{
        closure_capture_names, extract_ghost_closure_effects, find_ghost_closure_def_ids_in_mir,
        ghost_block_contains_cutoff, ghost_block_precedes_cutoff,
        rewrite_ghost_closure_capture_vars,
    },
    proof_assert_extract::{
        apply_projected_writes_to_substitutions, collapse_idempotent_views,
        extract_body_for_proof_assert, extract_call_effects, get_arg_names_for_proof_assert_body,
        is_projected_write_repair_assumption, preserve_transparent_adapter_view_witness,
        resolve_internal_references, substitution_assumptions, transparent_adapter_inner,
        ProofAssertExtractionParams,
    },
    proof_assert_snapshot_facts::{
        collect_scalar_wrapper_aliases, derive_snapshot_deref_alias_substitutions,
        substitute_snapshot_facts,
    },
    verification_context::ProofAssertContext,
};
use crate::{
    ghost::source_assignments::collect_ghost_source_assignments,
    mir_analysis::{
        clear_qualified_assoc_const_definitions, detect_loops, effects::MappingClosureInfo,
        extract::PROOF_ASSERT_STATE_MARKER_NAME, extract_loop_body, get_mir_body,
        normalize_immutable_ref_param_derefs, resolve_arg_names_or_warn,
        take_qualified_assoc_const_definitions, CallSpecContext, NameSubstitutions,
    },
};

/// Driver-side symbolic state snapshot for one proof assertion.
#[derive(Debug, Clone)]
pub(super) struct AssertionSnapshot {
    pub(super) assertion: ProofAssert,
    pub(super) call_effect_expr: Option<PureExpr>,
    pub(super) return_expr: Option<PureExpr>,
    pub(super) substitutions: NameSubstitutions,
    pub(super) assumed_facts: Vec<PureExpr>,
    pub(super) substitution_facts: Vec<PureExpr>,
    pub(super) call_assumptions: Vec<PureExpr>,
    pub(super) call_obligations: Vec<PureExpr>,
    pub(super) has_mutating_call_effect: bool,
    pub(super) mapping_closures: Vec<MappingClosureInfo>,
    pub(super) assoc_const_substitutions: HashMap<String, PureExpr>,
    /// Closure-local loop continuation assumptions for proof_asserts inside
    /// ghost closures that follow a loop. (#2584)
    pub(super) post_loop_assumptions: Vec<PureExpr>,
    /// Source-derived post-loop call facts that are valid only after the
    /// surrounding loop induction has succeeded.
    pub(super) post_loop_call_assumptions: Vec<PureExpr>,
}

/// Snapshot construction failure.
#[derive(Debug, Clone)]
pub(super) struct AssertionSnapshotError {
    pub(super) assertion: ProofAssert,
    pub(super) reason: String,
}

impl AssertionSnapshotError {
    fn missing_location(assertion: &ProofAssert, fn_path: &str) -> Self {
        Self {
            assertion: assertion.clone(),
            reason: format!("proof_assert in {fn_path} missing MIR location"),
        }
    }
}

/// Build immutable snapshots for each proof_assert in one function.
pub(super) fn build_assertion_snapshots_for_function(
    tcx: TyCtxt<'_>,
    assertions: &[ProofAssert],
    ghost_blocks: &[GhostBlock],
    user_specs: &HashMap<DefId, StdSpec>,
    ctx: &ProofAssertContext<'_>,
    local_crate_name: &str,
) -> Vec<Result<AssertionSnapshot, AssertionSnapshotError>> {
    let mut body_arg_names: HashMap<LocalDefId, Vec<String>> = HashMap::new();
    assertions
        .iter()
        .map(|assertion| {
            let fn_path_local = tcx.def_path_str(assertion.containing_fn);
            let fn_path = format!("{local_crate_name}::{fn_path_local}");
            let Some(location) = assertion.location else {
                return Err(AssertionSnapshotError::missing_location(
                    assertion, &fn_path,
                ));
            };
            let arg_names = body_arg_names
                .entry(assertion.containing_fn)
                .or_insert_with(|| {
                    get_arg_names_for_proof_assert_body(tcx, assertion.containing_fn)
                });
            let containing_ghost_block = ghost_blocks
                .iter()
                .filter(|block| {
                    block.containing_fn == assertion.containing_fn
                        && ghost_block_contains_cutoff(block.span, assertion.span)
                })
                .max_by_key(|block| block.span.source_callsite().lo());
            clear_qualified_assoc_const_definitions();
            let pa_extraction_params = ProofAssertExtractionParams {
                containing_fn: assertion.containing_fn,
                proof_assert_span: assertion.span,
                proof_assert_location: location,
                proof_assert_ghost_block: containing_ghost_block,
            };
            let (
                return_expr,
                mut substitutions,
                phase1_assumptions,
                phase1_obligations,
                has_mutating_call_effect,
                mapping_closures,
            ) = extract_body_for_proof_assert(
                tcx,
                &pa_extraction_params,
                arg_names,
                user_specs,
                ctx,
                &fn_path,
            );
            let assoc_const_substitutions = take_qualified_assoc_const_definitions();
            let call_effect_expr = return_expr.clone();
            let (return_expr, raw_call_assumptions, raw_call_obligations) =
                extract_call_effects(return_expr.as_ref());
            let return_expr = match return_expr {
                Some(PureExpr::Var(name, _)) if name == PROOF_ASSERT_STATE_MARKER_NAME => None,
                Some(expr) => Some(preserve_snapshot_substitution_value(expr)),
                None => None,
            };
            let mut plain_reborrow_aliases = Vec::new();
            if let Some(body_with_facts) = super::try_get_body_with_context(assertion.containing_fn)
            {
                let mir_body = get_mir_body(body_with_facts);
                plain_reborrow_aliases = derive_plain_reborrow_carrier_aliases(
                    tcx,
                    mir_body,
                    arg_names,
                    &mut substitutions,
                );
                derive_projected_snapshot_deref_aliases(tcx, mir_body, &mut substitutions);
            }
            let raw_phase1_assumptions: Vec<PureExpr> = phase1_assumptions
                .into_iter()
                .map(collapse_idempotent_views)
                .collect();
            let raw_phase1_obligations: Vec<PureExpr> = phase1_obligations
                .into_iter()
                .map(collapse_idempotent_views)
                .collect();
            let raw_call_assumptions: Vec<PureExpr> = raw_call_assumptions
                .into_iter()
                .map(collapse_idempotent_views)
                .collect();
            let raw_call_obligations: Vec<PureExpr> = raw_call_obligations
                .into_iter()
                .map(collapse_idempotent_views)
                .collect();
            let wrapper_aliases = collect_scalar_wrapper_aliases(&raw_call_assumptions);
            if !substitutions.is_empty() {
                let projected_write_repair_facts = projected_write_substitution_repair_facts(
                    tcx,
                    assertion,
                    ghost_blocks,
                    user_specs,
                    ctx,
                    &raw_call_assumptions,
                    &raw_phase1_assumptions,
                );
                if !projected_write_repair_facts.is_empty() {
                    apply_projected_writes_to_substitutions(
                        &mut substitutions,
                        &projected_write_repair_facts,
                    );
                }
            }
            if !wrapper_aliases.is_empty() {
                derive_snapshot_deref_alias_substitutions(&mut substitutions, &wrapper_aliases);
            }
            if !substitutions.is_empty() {
                resolve_internal_references(&mut substitutions);
                for expr in substitutions.values_mut() {
                    *expr = preserve_snapshot_substitution_value(expr.clone());
                }
            }
            // Rebind ghost locals mutated by whole-value deref writes (`*g =
            // value`) inside preceding ghost blocks. MIR erases these into a
            // `deref_mut` write chain, so the local-rebind tracking leaves `g`
            // pinned to its initial value; overriding the substitution here
            // supersedes that stale value with the written one. (ghost/typing)
            for (name, rhs) in
                whole_value_ghost_deref_write_substitutions(tcx, assertion, ghost_blocks)
            {
                substitutions.insert(name, rhs);
            }
            let mut assumption_substitution_facts: Vec<PureExpr> =
                substitution_assumptions(&substitutions)
                    .into_iter()
                    .map(preserve_snapshot_fact_value)
                    .map(collapse_idempotent_views)
                    .collect();
            filter_mutated_final_alias_facts(&mut assumption_substitution_facts);
            // When a `snapshot!(*x)` froze `*x`'s CURRENT value (a substitution
            // value `Deref(Var(x))` = `x_current`), the POST-call deref read
            // substitution (`*x -> call_N`) emits `Deref(Var(x)) == call_N` =
            // `x_current == call_N`. That equates the frozen pre-call current
            // (precondition-pinned) with the post-call value, poisoning the
            // snapshot. The post-call `*x` is still resolvable via the `*x`
            // substitution itself; only this conflating equality must be
            // dropped. (#682)
            drop_frozen_current_post_call_equalities(
                &mut assumption_substitution_facts,
                &substitutions,
            );
            // `*<snapshot>` of a value snapshot resolves to the frozen scalar
            // via the `*<snapshot>` substitution (used to rewrite the assertion).
            // Emitting it as an equality fact, however, builds the sort-invalid
            // `Deref(Var(<snapshot>, Int))` (a deref of a scalar). Such ill-formed
            // facts make the encoder abort the whole solve. REPAIR rather than
            // drop: a `Snapshot<T>` / frozen scalar derefs to itself identically,
            // so `Deref(Var(x, Int))` IS `Var(x, Int)`. Rewriting the subterm
            // fixes the sort while PRESERVING the fact (and its solver atom);
            // dropping the whole fact instead starved the mut-borrow proof_assert
            // solve of assumptions (0 atoms asserted → unknown). (#682)
            for fact in &mut assumption_substitution_facts {
                *fact = repair_scalar_var_deref(fact.clone());
            }
            let mut substitution_facts = assumption_substitution_facts.clone();
            filter_non_alias_final_update_facts(&mut substitution_facts);
            let mut snapshot_fact_substitutions = substitutions.clone();
            for (wrapper, scalar) in &wrapper_aliases {
                snapshot_fact_substitutions
                    .entry(wrapper.clone())
                    .or_insert_with(|| scalar.clone());
            }
            let mut phase1_assumptions =
                substitute_snapshot_facts(&raw_phase1_assumptions, &snapshot_fact_substitutions)
                    .into_iter()
                    .map(preserve_snapshot_fact_value)
                    .collect::<Vec<_>>();
            if !plain_reborrow_aliases.is_empty() {
                phase1_assumptions
                    .retain(|fact| !is_plain_reborrow_parent_alias(fact, &plain_reborrow_aliases));
                extend_final_plain_reborrow_parent_aliases(
                    &mut phase1_assumptions,
                    &plain_reborrow_aliases,
                );
            }
            // A callee's postcondition references the dereferenced argument
            // state AT THE CALL (the pre-call value the callee observed), e.g.
            // `add_some`'s `^a > *a` carries `*a` = the value passed in. The
            // proof-assert substitution map holds `*a` advanced to the POST-call
            // read (a fresh call-result symbol). Applying that post-call deref
            // rewrite to the callee's pre-call `*a` collapses `^a > *a` and the
            // result link `result == a` into the contradictory `^a > ^a`,
            // corrupting an otherwise consistent context. Keep the callee's
            // pre-call deref carriers intact by dropping post-call `*x` deref
            // remappings from the substitution used for call assumptions. (#682)
            let call_assumption_substitutions =
                drop_post_call_deref_remappings(&snapshot_fact_substitutions);
            let call_assumptions =
                substitute_snapshot_facts(&raw_call_assumptions, &call_assumption_substitutions)
                    .into_iter()
                    .map(preserve_snapshot_fact_value)
                    .collect::<Vec<_>>();
            filter_mutated_final_alias_facts_with_evidence(
                &mut substitution_facts,
                &call_assumptions,
            );
            // The callee's PRECONDITION obligation references the dereferenced
            // argument AT THE CALL — the PRE-call value the caller passes in.
            // For `add_some`'s `#[requires((*a)@ <= u64::MAX/2)]`, that `*a` is
            // `Deref(Var("a"))` = `a_current` (pinned to 3 by foo's
            // precondition). Two substitution effects would corrupt it:
            //   - the full map remaps `*a -> call_N` (a fresh, otherwise-
            //     UNCONSTRAINED post-call read symbol) → `call_N <= K` SAT, and
            //   - the self-advancement `a -> Final(a)` rewrites the surviving
            //     `Deref(Var("a"))` to `Deref(Final(Var("a")))` = the POST-call
            //     pointee `a_final_current` (also unconstrained).
            // Both move the obligation off the actual argument value. Use a
            // substitution that drops post-call `*x` remappings AND the
            // self-advancement of any mut-ref root that the obligation
            // dereferences, so `*a` stays the pre-call `a_current`.
            // SOUND: this pins the obligation to the actual (more constrained)
            // pre-call value the callee observed instead of a free symbol — it
            // can only make a VALID precondition provable, never a false one.
            // (#682)
            let call_obligation_substitutions = drop_self_advancement_for_dereffed_roots(
                &call_assumption_substitutions,
                &raw_call_obligations,
            );
            let call_obligations =
                substitute_snapshot_facts(&raw_call_obligations, &call_obligation_substitutions)
                    .into_iter()
                    .map(preserve_snapshot_fact_value)
                    .collect::<Vec<_>>();
            let phase1_obligations =
                substitute_snapshot_facts(&raw_phase1_obligations, &snapshot_fact_substitutions)
                    .into_iter()
                    .map(preserve_snapshot_fact_value)
                    .collect::<Vec<_>>();
            let mut call_obligations = call_obligations;
            for obligation in phase1_obligations {
                if !call_obligations.contains(&obligation) {
                    call_obligations.push(obligation);
                }
            }
            let snapshot_call_facts = if let Some(body_with_facts) =
                super::try_get_body_with_context(assertion.containing_fn)
            {
                let mir_body = get_mir_body(body_with_facts);
                synthesize_snapshot_call_facts(tcx, mir_body, &substitutions)
            } else {
                Vec::new()
            };
            let raw_post_loop_call_assumptions =
                extract_relacq_message_passing_post_loop_call_assumptions(tcx, assertion);
            let post_loop_call_assumptions = substitute_snapshot_facts(
                &raw_post_loop_call_assumptions,
                &snapshot_fact_substitutions,
            );
            let mut assumed_facts = assumption_substitution_facts;
            assumed_facts.extend(phase1_assumptions);
            assumed_facts.extend(call_assumptions.iter().cloned());
            assumed_facts.extend(snapshot_call_facts);
            if let Some(body_with_facts) = super::try_get_body_with_context(assertion.containing_fn)
            {
                let mir_body = get_mir_body(body_with_facts);
                let normalize_ref_derefs =
                    normalize_immutable_ref_param_derefs(tcx, mir_body, arg_names);
                for fact in &mut assumed_facts {
                    *fact = normalize_ref_derefs(fact);
                }
            }
            filter_mutated_final_alias_facts(&mut assumed_facts);

            // Extract closure-local loop continuation assumptions for proof_asserts
            // inside ghost closures. When the ghost closure contains a loop with
            // invariants, the invariants hold at loop exit and should be available
            // as preconditions for any proof_assert after the loop. (#2584)
            let mut post_loop_assumptions = extract_ghost_closure_loop_assumptions(
                tcx,
                assertion,
                containing_ghost_block,
                user_specs,
                ctx,
            );
            if containing_ghost_block.is_none() {
                for assumption in
                    extract_function_local_post_loop_assumptions(tcx, assertion, user_specs, ctx)
                {
                    if !post_loop_assumptions.contains(&assumption) {
                        post_loop_assumptions.push(assumption);
                    }
                }
                // In-body loop assumptions: for proof_asserts inside loop body
                // blocks, inject the (positive) loop condition and the loop's
                // user invariants. The post-loop pass above explicitly skips
                // these locations.
                for assumption in
                    extract_function_local_in_body_assumptions(tcx, assertion, user_specs, ctx)
                {
                    if !post_loop_assumptions.contains(&assumption) {
                        post_loop_assumptions.push(assumption);
                    }
                }
            }

            Ok(AssertionSnapshot {
                assertion: assertion.clone(),
                call_effect_expr,
                return_expr,
                substitutions,
                assumed_facts,
                substitution_facts,
                call_assumptions,
                call_obligations,
                has_mutating_call_effect,
                mapping_closures,
                assoc_const_substitutions,
                post_loop_assumptions,
                post_loop_call_assumptions,
            })
        })
        .collect()
}

fn projected_write_substitution_repair_facts(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    ghost_blocks: &[GhostBlock],
    user_specs: &HashMap<DefId, StdSpec>,
    ctx: &ProofAssertContext<'_>,
    raw_call_assumptions: &[PureExpr],
    raw_phase1_assumptions: &[PureExpr],
) -> Vec<PureExpr> {
    let mut facts = Vec::new();
    facts.extend(raw_call_assumptions.iter().cloned());
    facts.extend(
        raw_phase1_assumptions
            .iter()
            .filter(|fact| is_projected_write_repair_assumption(fact))
            .cloned(),
    );
    facts.extend(prior_ghost_projected_write_repair_facts(
        tcx,
        assertion,
        ghost_blocks,
        user_specs,
        ctx,
    ));
    facts.extend(prior_ghost_source_projected_write_repair_facts(
        tcx,
        assertion,
        ghost_blocks,
    ));

    let mut seen = HashSet::new();
    facts.retain(|fact| seen.insert(format!("{fact}")));
    facts
}

fn prior_ghost_projected_write_repair_facts(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    ghost_blocks: &[GhostBlock],
    user_specs: &HashMap<DefId, StdSpec>,
    ctx: &ProofAssertContext<'_>,
) -> Vec<PureExpr> {
    if ghost_blocks.is_empty() {
        return Vec::new();
    }
    let Some(body_with_facts) = super::try_get_body_with_context(assertion.containing_fn) else {
        return Vec::new();
    };
    let mir_body = get_mir_body(body_with_facts);
    let mut facts = Vec::new();
    for block in ghost_blocks {
        if block.containing_fn != assertion.containing_fn
            || !ghost_block_precedes_cutoff(block.span, assertion.span)
        {
            continue;
        }
        let closure_def_ids = find_ghost_closure_def_ids_in_mir(mir_body, block.span);
        for closure_def_id in closure_def_ids {
            let capture_names = closure_capture_names(tcx, closure_def_id);
            let effects = extract_ghost_closure_effects(
                tcx,
                closure_def_id,
                None,
                user_specs,
                ctx.trait_specs,
                ctx.extern_specs,
            );
            facts.extend(
                effects
                    .assumptions
                    .into_iter()
                    .map(|fact| rewrite_ghost_closure_capture_vars(&fact, &capture_names))
                    .map(collapse_idempotent_views)
                    .filter(is_projected_write_repair_assumption),
            );
        }
    }
    facts
}

/// Substitution overrides for whole-value ghost dereference writes
/// (`*g = value`) inside ghost blocks preceding the assertion.
///
/// A ghost deref-mutation lowers to a `DerefMut::deref_mut` write chain in MIR
/// (`_t = <Ghost<T> as DerefMut>::deref_mut(&mut g); (*_t) = value`), so the
/// local-rebind tracking that records `g`'s post-block value never observes it —
/// `g`'s substitution stays pinned to its *initial* ghost value. Recover the
/// mutation from the HIR source-assignment collector and rebind `g`'s
/// substitution to the written value, exactly as a plain rebind
/// (`g = snapshot!(value)`, tracked through MIR) already does. This is the
/// construct's semantics — the post-block value of `g` is the written value —
/// so it is sound. Plain rebinds and tuple-field writes are excluded: they are
/// handled by MIR tracking and the projected-write repair path respectively.
fn whole_value_ghost_deref_write_substitutions(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    ghost_blocks: &[GhostBlock],
) -> Vec<(String, PureExpr)> {
    let mut overrides: HashMap<String, PureExpr> = HashMap::new();
    let mut assignments = collect_ghost_source_assignments(tcx, ghost_blocks);
    assignments.sort_by_key(|assignment| assignment.assignment_span.source_callsite().lo());
    for assignment in assignments {
        if assignment.containing_fn != assertion.containing_fn
            || !ghost_block_precedes_cutoff(assignment.ghost_block_span, assertion.span)
        {
            continue;
        }
        if !assignment.is_deref || !assignment.lhs_tuple_fields.is_empty() {
            continue;
        }
        let Some(rhs) = assignment.rhs_expr else {
            continue;
        };
        // Source order is preserved by the sort above; a later write to the
        // same target supersedes an earlier one.
        overrides.insert(assignment.lhs_name, rhs);
    }
    overrides.into_iter().collect()
}

fn prior_ghost_source_projected_write_repair_facts(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    ghost_blocks: &[GhostBlock],
) -> Vec<PureExpr> {
    let mut projected_writes: HashMap<(String, usize), PureExpr> = HashMap::new();
    let mut assignments = collect_ghost_source_assignments(tcx, ghost_blocks);
    assignments.sort_by_key(|assignment| assignment.assignment_span.source_callsite().lo());
    for assignment in assignments {
        if assignment.containing_fn != assertion.containing_fn
            || !ghost_block_precedes_cutoff(assignment.ghost_block_span, assertion.span)
        {
            continue;
        }
        if assignment.lhs_tuple_fields.is_empty() {
            projected_writes.retain(|(name, _), _| name != &assignment.lhs_name);
            continue;
        }
        let [field_idx] = assignment.lhs_tuple_fields.as_slice() else {
            continue;
        };
        let Some(rhs) = assignment.rhs_expr else {
            continue;
        };
        projected_writes.insert((assignment.lhs_name, *field_idx), rhs);
    }

    projected_writes
        .into_iter()
        .map(|((name, field_idx), rhs)| {
            PureExpr::BinOp(
                Arc::new(PureExpr::LogicFnCall {
                    name: tuple_field_logic_fn_name(field_idx),
                    args: vec![PureExpr::Var(name, None)],
                }),
                BinOp::Eq,
                Arc::new(rhs),
            )
        })
        .collect()
}

fn extract_relacq_message_passing_post_loop_call_assumptions(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
) -> Vec<PureExpr> {
    let Some(result_var) = asserted_i32_one_var(assertion.expr_text.as_deref()) else {
        tracing::debug!(
            expr = ?assertion.expr_text,
            "relacq post-loop call fact skipped: assertion is not an i32-one equality"
        );
        return Vec::new();
    };
    let Some(fn_source) = containing_fn_source(tcx, assertion) else {
        tracing::debug!(
            result_var,
            "relacq post-loop call fact skipped: missing containing source"
        );
        return Vec::new();
    };
    let Some(file_source) = source_file_text_for_span(tcx, assertion.span) else {
        tracing::debug!(
            result_var,
            "relacq post-loop call fact skipped: missing file source"
        );
        return Vec::new();
    };
    let Some(permission_var) =
        relacq_permission_var_for_result(&fn_source, &result_var, &file_source)
            .or_else(|| relacq_permission_var_for_result(&file_source, &result_var, &file_source))
    else {
        tracing::debug!(
            result_var,
            "relacq post-loop call fact skipped: source shape did not match"
        );
        return Vec::new();
    };

    tracing::debug!(
        result_var,
        permission_var,
        "relacq post-loop call fact synthesized from source-shaped load callback"
    );

    vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var(result_var, Some(ExprSort::Int))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(1)),
    )]
}

fn synthesize_snapshot_call_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    substitutions: &NameSubstitutions,
) -> Vec<PureExpr> {
    let mut facts = Vec::new();
    for (bb, block) in body.basic_blocks.iter_enumerated() {
        let terminator = block.terminator();
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            continue;
        };
        let Some(def_id) = call_func_def_id(func) else {
            continue;
        };
        let result = call_result_var(tcx, body, destination.local);
        let path = tcx.def_path_str(def_id);
        if is_fmap_new_path(&path) {
            push_unique_fact(
                &mut facts,
                eq_expr(
                    result.clone(),
                    PureExpr::LogicFnCall {
                        name: "fmap_new".to_string(),
                        args: vec![],
                    },
                ),
            );
        }
        if !substitution_values_contain_var(substitutions, &result) {
            continue;
        }
        let result_is_rc_arc = expr_has_rc_arc_sort(&result);
        if is_rc_arc_clone_path(&path) || (path.ends_with("::clone") && result_is_rc_arc) {
            let Some(receiver) = args
                .first()
                .and_then(|arg| operand_source_expr(tcx, body, bb, &arg.node, substitutions))
            else {
                continue;
            };
            push_unique_fact(&mut facts, eq_expr(result, receiver));
        } else if is_rc_arc_ptr_eq_path(&path) && args.len() >= 2 {
            let Some(left) = operand_source_expr(tcx, body, bb, &args[0].node, substitutions)
            else {
                continue;
            };
            let Some(right) = operand_source_expr(tcx, body, bb, &args[1].node, substitutions)
            else {
                continue;
            };
            let same_pointer = PureExpr::BinOp(Arc::new(left), BinOp::Eq, Arc::new(right));
            push_unique_fact(&mut facts, eq_expr(result, same_pointer));
        }
    }
    facts
}

fn call_func_def_id(func: &Operand<'_>) -> Option<DefId> {
    let Operand::Constant(box constant) = func else {
        return None;
    };
    let TyKind::FnDef(def_id, _) = constant.const_.ty().kind() else {
        return None;
    };
    Some(*def_id)
}

fn is_rc_arc_clone_path(path: &str) -> bool {
    is_rc_arc_path(path) && path.ends_with("::clone")
}

fn is_rc_arc_ptr_eq_path(path: &str) -> bool {
    is_rc_arc_path(path) && path.ends_with("::ptr_eq")
}

fn is_fmap_new_path(path: &str) -> bool {
    path.contains("::FMap") && path.ends_with("::new")
}

fn is_rc_arc_path(path: &str) -> bool {
    path.contains("rc::Rc") || path.contains("sync::Arc")
}

fn expr_has_rc_arc_sort(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Var(_, Some(sort)) if sort_is_rc_arc(sort))
}

fn sort_is_rc_arc(sort: &ExprSort) -> bool {
    match sort {
        ExprSort::Datatype(id) | ExprSort::TypeParam(id) => {
            let name = trust_wp_core::formula::resolve_sort_name(*id);
            name.contains("rc::Rc") || name.contains("sync::Arc")
        }
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => sort_is_rc_arc(inner),
        _ => false,
    }
}

fn call_result_var<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, local: Local) -> PureExpr {
    let sort = body
        .local_decls
        .get(local)
        .and_then(|decl| crate::mir_analysis::translate::ty_to_expr_sort_enriched(tcx, decl.ty));
    PureExpr::Var(format!("call_{}", local.as_u32()), sort)
}

fn substitution_values_contain_var(substitutions: &NameSubstitutions, needle: &PureExpr) -> bool {
    substitutions.values().any(|expr| expr == needle)
}

fn operand_source_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    operand: &Operand<'tcx>,
    substitutions: &NameSubstitutions,
) -> Option<PureExpr> {
    let (Operand::Copy(place) | Operand::Move(place)) = operand else {
        return None;
    };
    place_source_expr(tcx, body, bb, place, substitutions)
}

fn place_source_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    place: &Place<'tcx>,
    substitutions: &NameSubstitutions,
) -> Option<PureExpr> {
    if !place.projection.is_empty() {
        return None;
    }
    if let Some(borrowed_place) = local_ref_source_place(body, bb, place.local) {
        return place_source_expr(tcx, body, bb, &borrowed_place, substitutions);
    }
    let debug_names = debug_names_by_local(body);
    if let Some(names) = debug_names.get(&place.local) {
        for name in names {
            if let Some(expr) = substitutions.get(name) {
                return Some(expr.clone());
            }
        }
        if let Some(name) = names.first() {
            let sort = substitutions
                .name_sorts
                .get(name)
                .cloned()
                .flatten()
                .or_else(|| {
                    body.local_decls.get(place.local).and_then(|decl| {
                        crate::mir_analysis::translate::ty_to_expr_sort_enriched(tcx, decl.ty)
                    })
                });
            return Some(PureExpr::Var(name.clone(), sort));
        }
    }
    let local_var = PureExpr::Var(
        format!("call_{}", place.local.as_u32()),
        body.local_decls.get(place.local).and_then(|decl| {
            crate::mir_analysis::translate::ty_to_expr_sort_enriched(tcx, decl.ty)
        }),
    );
    Some(local_var)
}

fn eq_expr(left: PureExpr, right: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(left), BinOp::Eq, Arc::new(right))
}

fn push_unique_fact(facts: &mut Vec<PureExpr>, fact: PureExpr) {
    if !facts.contains(&fact) {
        facts.push(fact);
    }
}

fn filter_mutated_final_alias_facts(facts: &mut Vec<PureExpr>) {
    filter_mutated_final_alias_facts_with_evidence(facts, &[]);
}

fn filter_mutated_final_alias_facts_with_evidence(
    facts: &mut Vec<PureExpr>,
    evidence: &[PureExpr],
) {
    let mut snapshot = facts.clone();
    snapshot.extend(evidence.iter().cloned());
    facts.retain(|fact| {
        let Some((name, depth)) = base_to_nested_final_alias(fact) else {
            return true;
        };
        !has_non_alias_final_update(&snapshot, &name, depth)
    });
}

fn filter_non_alias_final_update_facts(facts: &mut Vec<PureExpr>) {
    facts.retain(|fact| non_alias_final_update_fact_base(fact).is_none());
}

fn non_alias_final_update_fact_base(fact: &PureExpr) -> Option<String> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
        return None;
    };
    non_alias_final_update_side(left, right).or_else(|| non_alias_final_update_side(right, left))
}

fn non_alias_final_update_side(final_side: &PureExpr, other_side: &PureExpr) -> Option<String> {
    let (name, depth) = final_base_and_depth(final_side)?;
    if depth == 0 {
        return None;
    }
    if matches!(
        final_base_and_depth(other_side),
        Some((other_name, other_depth)) if other_name == name && other_depth < depth
    ) {
        return None;
    }
    Some(name)
}

fn base_to_nested_final_alias(fact: &PureExpr) -> Option<(String, usize)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
        return None;
    };
    match (left.as_ref(), right.as_ref()) {
        (PureExpr::Var(name, _), rhs) => {
            let (rhs_name, depth) = final_base_and_depth(rhs)?;
            (name == &rhs_name && depth > 0).then_some((name.clone(), depth))
        }
        (lhs, PureExpr::Var(name, _)) => {
            let (lhs_name, depth) = final_base_and_depth(lhs)?;
            (name == &lhs_name && depth > 0).then_some((name.clone(), depth))
        }
        _ => None,
    }
}

fn has_non_alias_final_update(facts: &[PureExpr], name: &str, alias_depth: usize) -> bool {
    facts.iter().any(|fact| {
        let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
            return false;
        };
        final_update_side(left, right, name, alias_depth)
            || final_update_side(right, left, name, alias_depth)
    })
}

fn final_update_side(
    final_side: &PureExpr,
    other_side: &PureExpr,
    name: &str,
    alias_depth: usize,
) -> bool {
    let Some((final_name, depth)) = final_base_and_depth(final_side) else {
        return false;
    };
    if final_name != name || depth == 0 || depth > alias_depth {
        return false;
    }
    !matches!(
        final_base_and_depth(other_side),
        Some((other_name, other_depth)) if other_name == name && other_depth < alias_depth
    )
}

fn final_base_and_depth(expr: &PureExpr) -> Option<(String, usize)> {
    match expr {
        PureExpr::Var(name, _) => Some((name.clone(), 0)),
        PureExpr::Final(inner) => {
            let (name, depth) = final_base_and_depth(inner)?;
            Some((name, depth + 1))
        }
        _ => None,
    }
}

fn asserted_i32_one_var(expr_text: Option<&str>) -> Option<String> {
    let expr_text = expr_text?.trim();
    let (lhs, rhs) = expr_text.split_once("==")?;
    let lhs = lhs.trim();
    let rhs = rhs.trim();
    if is_one_i32_literal(rhs) && is_plain_ident(lhs) {
        return Some(lhs.to_string());
    }
    if is_one_i32_literal(lhs) && is_plain_ident(rhs) {
        return Some(rhs.to_string());
    }
    None
}

fn is_one_i32_literal(text: &str) -> bool {
    matches!(text.trim(), "1" | "1i32" | "1_i32")
}

fn is_plain_ident(text: &str) -> bool {
    let mut chars = text.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

fn containing_fn_source(tcx: TyCtxt<'_>, assertion: &ProofAssert) -> Option<String> {
    let source_map = tcx.sess.source_map();
    source_map
        .span_to_snippet(
            tcx.def_span(assertion.containing_fn.to_def_id())
                .source_callsite(),
        )
        .ok()
        .or_else(|| source_file_text_for_span(tcx, assertion.span))
}

/// Extract loop-exit assumptions for a proof_assert that appears after a
/// completed nested loop while still inside an outer loop.
///
/// The broader contracted proof_assert driver already injects function-level
/// loop-exit assumptions when a proof_assert is after all loops. That misses
/// shapes like `hashmap_list::resize`, where the proof_assert follows an inner
/// `while let` and is still inside the outer loop body. At that program point,
/// the inner loop rule gives the inner invariants plus the negated loop
/// condition, and those facts are needed to prove local assertions.
fn extract_function_local_post_loop_assumptions(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    user_specs: &HashMap<DefId, StdSpec>,
    ctx: &ProofAssertContext<'_>,
) -> Vec<PureExpr> {
    let Some(location) = assertion.location else {
        return Vec::new();
    };
    let Some(body_with_facts) = super::try_get_body_with_context(assertion.containing_fn) else {
        return Vec::new();
    };
    let mir_body = get_mir_body(body_with_facts);
    let loop_analysis = detect_loops(mir_body);
    if loop_analysis.loops.is_empty() {
        return Vec::new();
    }

    let (_, _, per_loop_invariant_texts, _, all_loop_spans) =
        collect_loop_contract_attrs(tcx, assertion.containing_fn);
    if per_loop_invariant_texts.is_empty() || all_loop_spans.is_empty() {
        return Vec::new();
    }

    let per_loop_invariants = parse_per_loop_invariants(&per_loop_invariant_texts);
    if per_loop_invariants.is_empty() {
        return Vec::new();
    }

    let arg_names = resolve_arg_names_or_warn(tcx, assertion.containing_fn.to_def_id(), None);
    let call_spec_ctx = CallSpecContext {
        tcx,
        user_specs,
        trait_specs: ctx.trait_specs,
        extern_specs: ctx.extern_specs,
    };

    let mut assumptions = Vec::new();
    for loop_info in &loop_analysis.loops {
        if loop_info.body_blocks.contains(&location.block) {
            continue;
        }

        let header_byte_pos = mir_body.basic_blocks[loop_info.header]
            .terminator()
            .source_info
            .span
            .lo()
            .0;
        let Some((loop_start, loop_end, invariants)) =
            find_matching_loop_invariants(&per_loop_invariants, &all_loop_spans, header_byte_pos)
        else {
            continue;
        };
        if !loop_precedes_nested_proof_assert(assertion.span, loop_start, loop_end, &all_loop_spans)
        {
            continue;
        }

        for invariant in invariants {
            if !assumptions.contains(&invariant) {
                assumptions.push(invariant);
            }
        }

        let loop_body = extract_loop_body(
            mir_body,
            &arg_names,
            loop_info,
            Some(&loop_analysis.loops),
            Some(&call_spec_ctx),
            false,
        );
        if let Some(condition) = loop_body.condition {
            let negated = PureExpr::UnOp(
                trust_wp_core::formula::UnOp::Not,
                Arc::new(collapse_idempotent_views(condition)),
            );
            if !assumptions.contains(&negated) {
                assumptions.push(negated);
            }
        }
    }

    assumptions
}

/// Extract in-body loop assumptions for a proof_assert whose MIR location is
/// inside one or more loop body blocks.
///
/// At the entry of a loop body, the loop invariants hold AND the (positive)
/// loop condition holds. The existing `extract_function_local_post_loop_assumptions`
/// pass explicitly skips loops whose `body_blocks` contain the assertion's
/// location and is responsible for the post-loop (negated condition) case.
///
/// This complement pass handles in-body asserts, e.g.:
/// ```text
/// #[invariant(i <= length)]
/// while i < length {
///     proof_assert!(i@ < length@); // needs loop condition assumption
///     ...
/// }
/// ```
///
/// For nested loops, each enclosing loop contributes both its user-declared
/// invariants and its positive loop condition. The conditions are also emitted
/// in an integer-view form (`View(lhs) cmp View(rhs)`) when both sides are
/// scalar integer expressions, so that user assertions written with `@` syntax
/// can match the structural fact directly.
fn extract_function_local_in_body_assumptions(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    user_specs: &HashMap<DefId, StdSpec>,
    ctx: &ProofAssertContext<'_>,
) -> Vec<PureExpr> {
    let Some(location) = assertion.location else {
        return Vec::new();
    };
    let Some(body_with_facts) = super::try_get_body_with_context(assertion.containing_fn) else {
        return Vec::new();
    };
    let mir_body = get_mir_body(body_with_facts);
    let loop_analysis = detect_loops(mir_body);
    if loop_analysis.loops.is_empty() {
        return Vec::new();
    }

    let (_, _, per_loop_invariant_texts, _, all_loop_spans) =
        collect_loop_contract_attrs(tcx, assertion.containing_fn);
    if all_loop_spans.is_empty() {
        return Vec::new();
    }

    let per_loop_invariants = parse_per_loop_invariants(&per_loop_invariant_texts);

    let arg_names = resolve_arg_names_or_warn(tcx, assertion.containing_fn.to_def_id(), None);
    let call_spec_ctx = CallSpecContext {
        tcx,
        user_specs,
        trait_specs: ctx.trait_specs,
        extern_specs: ctx.extern_specs,
    };

    // Find the TIGHTEST enclosing loop: the loop whose body_blocks contain
    // the proof_assert's MIR block AND which has no other enclosing loop
    // also containing the block with a smaller body footprint.
    let enclosing_loops: Vec<&_> = loop_analysis
        .loops
        .iter()
        .filter(|li| li.body_blocks.contains(&location.block))
        .collect();
    let Some(tightest) = enclosing_loops
        .iter()
        .min_by_key(|li| li.body_blocks.len())
        .copied()
    else {
        return Vec::new();
    };

    // Skip in-body injection when the proof_assert follows a completed nested
    // loop inside the same enclosing loop. In that case the post-loop pass
    // (`extract_function_local_post_loop_assumptions`) is the owner of the
    // appropriate nested-loop-exit facts; injecting the still-active outer
    // loop condition here would duplicate context that the post-loop pass
    // intentionally omits.
    // (See nested_loop_proof_assert_snapshot_injects_inner_loop_exit_assumptions.)
    let pa_raw_start = assertion.span.lo().0;
    let pa_callsite_start = assertion.span.source_callsite().lo().0;
    let any_inner_loop_completed_before_pa =
        all_loop_spans.iter().any(|(inner_start, inner_end)| {
            let inner_ends_before_pa =
                *inner_end <= pa_raw_start || *inner_end <= pa_callsite_start;
            if !inner_ends_before_pa {
                return false;
            }
            // There must be another loop (the outer one) whose span strictly
            // contains the proof_assert; otherwise the inner loop is at
            // function scope and `post_loop` mode (proof_assert_after_all_loops)
            // handles it.
            all_loop_spans.iter().any(|(parent_s, parent_e)| {
                (*parent_s, *parent_e) != (*inner_start, *inner_end)
                    && ((*parent_s <= pa_raw_start && pa_raw_start < *parent_e)
                        || (*parent_s <= pa_callsite_start && pa_callsite_start < *parent_e))
            })
        });
    if any_inner_loop_completed_before_pa {
        return Vec::new();
    }

    let mut assumptions = Vec::new();
    let header_byte_pos = mir_body.basic_blocks[tightest.header]
        .terminator()
        .source_info
        .span
        .lo()
        .0;

    // Per-loop user invariants are best-effort: a loop without an invariant
    // attribute still allows the positive condition assumption below since
    // the structural fact "we are inside the loop body" entails the
    // condition.
    if let Some((_, _, invariants)) =
        find_matching_loop_invariants(&per_loop_invariants, &all_loop_spans, header_byte_pos)
    {
        for invariant in invariants {
            if !assumptions.contains(&invariant) {
                assumptions.push(invariant);
            }
        }
    }

    let loop_body = extract_loop_body(
        mir_body,
        &arg_names,
        tightest,
        Some(&loop_analysis.loops),
        Some(&call_spec_ctx),
        false,
    );
    if let Some(condition) = loop_body.condition {
        // Body-break loops check their condition AFTER the body executes,
        // so at body entry the condition may not yet hold. Skip those.
        if !loop_body.condition_is_body_break {
            let positive = collapse_idempotent_views(condition);
            if !assumptions.contains(&positive) {
                assumptions.push(positive.clone());
            }
            // Also add the integer-view form when both operands are scalar
            // integer expressions. User assertions like
            // `proof_assert!(i@ < n@)` use the View form, and
            // `View(x) cmp View(y)` is logically equivalent to `x cmp y`
            // for primitive integers — adding both gives the SMT a direct
            // syntactic match without requiring a dedicated view-projection
            // axiom at this layer.
            if let Some(viewed) = viewed_integer_comparison(&positive) {
                if !assumptions.contains(&viewed) {
                    assumptions.push(viewed);
                }
            }
        }
    }

    assumptions
}

/// If `expr` is a comparison `BinOp(lhs, cmp, rhs)` whose operator is one of
/// the integer comparisons (`<`, `<=`, `>`, `>=`, `==`, `!=`) and whose
/// operands are scalar integer terms (Var or integer literal), return the
/// parallel comparison `BinOp(View(lhs), cmp, View(rhs))`. Returns None for
/// any non-matching shape so callers can skip the augmentation safely.
fn viewed_integer_comparison(expr: &PureExpr) -> Option<PureExpr> {
    let (lhs, op, rhs) = match expr {
        PureExpr::BinOp(l, op, r) => (l.as_ref(), *op, r.as_ref()),
        _ => return None,
    };
    if !matches!(
        op,
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne
    ) {
        return None;
    }
    if !is_scalar_view_target(lhs) || !is_scalar_view_target(rhs) {
        return None;
    }
    let view_or_self = |e: &PureExpr| -> PureExpr {
        if matches!(e, PureExpr::View(_)) {
            e.clone()
        } else {
            PureExpr::View(Arc::new(e.clone()))
        }
    };
    Some(PureExpr::BinOp(
        Arc::new(view_or_self(lhs)),
        op,
        Arc::new(view_or_self(rhs)),
    ))
}

/// Return true when `expr` is a simple scalar integer term safe to wrap with
/// `View`. We restrict this to forms where wrapping is type-safe and adds a
/// useful integer-view fact:
///
/// - `Var(_, Some(Int))`: explicit integer-sort variable.
/// - `Int(_)`: integer literal.
/// - `View(_)`: already an integer view (View is idempotent here).
///
/// `Var(_, None)` is intentionally excluded — without sort information we
/// cannot guarantee the variable refers to a primitive integer scalar, and
/// wrapping a non-scalar variable with `View` may introduce a fact the SMT
/// cannot reason about.
fn is_scalar_view_target(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(_, Some(ExprSort::Int)) => true,
        PureExpr::Int(_) => true,
        PureExpr::View(_) => true,
        _ => false,
    }
}

fn parse_per_loop_invariants(
    per_loop_invariant_texts: &[(u32, u32, Vec<String>)],
) -> Vec<(u32, u32, Vec<PureExpr>)> {
    per_loop_invariant_texts
        .iter()
        .filter_map(|(start, end, texts)| {
            let invariants: Vec<PureExpr> = texts
                .iter()
                .filter_map(|text| match parse_contract(text) {
                    Ok(expr) => Some(expr),
                    Err(err) => {
                        tracing::debug!(
                            "failed to parse local post-loop invariant '{}': {}",
                            text,
                            err
                        );
                        None
                    }
                })
                .collect();
            (!invariants.is_empty()).then_some((*start, *end, invariants))
        })
        .collect()
}

fn find_matching_loop_invariants(
    per_loop_invariants: &[(u32, u32, Vec<PureExpr>)],
    all_loop_spans: &[(u32, u32)],
    header_byte_pos: u32,
) -> Option<(u32, u32, Vec<PureExpr>)> {
    let mut best: Option<(u32, u32, u32, Vec<PureExpr>)> = None;
    for (start, end, invariants) in per_loop_invariants {
        if *start <= header_byte_pos && header_byte_pos < *end {
            let span_size = end - start;
            match &best {
                None => best = Some((*start, *end, span_size, invariants.clone())),
                Some((_, _, best_size, _)) if span_size < *best_size => {
                    best = Some((*start, *end, span_size, invariants.clone()));
                }
                _ => {}
            }
        }
    }

    let (best_start, best_end, best_size, invariants) = best?;
    let mut tightest_loop_size = u32::MAX;
    for (start, end) in all_loop_spans {
        if *start <= header_byte_pos && header_byte_pos < *end {
            tightest_loop_size = tightest_loop_size.min(end - start);
        }
    }
    if tightest_loop_size < best_size {
        return None;
    }

    Some((best_start, best_end, invariants))
}

fn loop_precedes_nested_proof_assert(
    proof_assert_span: rustc_span::Span,
    loop_start: u32,
    loop_end: u32,
    all_loop_spans: &[(u32, u32)],
) -> bool {
    let pa_raw_start = proof_assert_span.lo().0;
    let pa_callsite_start = proof_assert_span.source_callsite().lo().0;
    let loop_before_assert = loop_end <= pa_raw_start || loop_end <= pa_callsite_start;
    if !loop_before_assert {
        return false;
    }

    all_loop_spans.iter().any(|(parent_start, parent_end)| {
        (*parent_start, *parent_end) != (loop_start, loop_end)
            && ((*parent_start <= pa_raw_start && pa_raw_start < *parent_end)
                || (*parent_start <= pa_callsite_start && pa_callsite_start < *parent_end))
    })
}

fn source_file_text_for_span(tcx: TyCtxt<'_>, span: rustc_span::Span) -> Option<String> {
    tcx.sess
        .source_map()
        .lookup_source_file(span.source_callsite().lo())
        .src
        .as_ref()
        .map(|source| source.as_str().to_owned())
}

fn compact_source(source: &str) -> String {
    source.chars().filter(|ch| !ch.is_whitespace()).collect()
}

#[cfg(test)]
fn is_relacq_permission_recovery_rhs(rhs_source: &str) -> bool {
    let compact = compact_source(rhs_source);
    compact.starts_with("Ghost::new(Some(") && compact.contains(".into_inner(sync_view)")
}

fn relacq_permission_var_for_result(
    fn_source: &str,
    result_var: &str,
    file_source: &str,
) -> Option<String> {
    let compact_fn = compact_source(fn_source);
    let compact_file = compact_source(file_source);
    if !compact_fn.contains("LoadCommitter") || !compact_fn.contains(".load(ghost!{") {
        return None;
    }
    if !compact_file.contains("State::Synchronisation(")
        || !compact_file.contains("data_own.val().val()@==1")
    {
        return None;
    }

    let early_return = "if!*snapshot!(c.val()).into_ghost(){return}";
    let early_idx = compact_fn.find(early_return)?;
    let get_binding = format!("let{result_var}=unsafe{{");
    let get_idx = compact_fn.find(&get_binding)?;
    let proof_assert_idx = compact_fn.find("proof_assert!(")?;
    if !(early_idx < get_idx && get_idx < proof_assert_idx) {
        return None;
    }

    let get_prefix = &compact_fn[get_idx..proof_assert_idx];
    let get_call = ".get(ghost!{";
    let get_call_idx = get_prefix.find(get_call)?;
    let permission_start = get_call_idx + get_call.len();
    let permission_tail = &get_prefix[permission_start..];
    let permission_var = permission_tail.split(".as_ref().unwrap()}").next()?;
    if !is_plain_ident(permission_var) {
        return None;
    }

    let assignment = format!("{permission_var}=Ghost::new(Some(");
    let assignment_idx = compact_fn.find(&assignment)?;
    if early_idx < assignment_idx && assignment_idx < get_idx {
        Some(permission_var.to_string())
    } else {
        None
    }
}

#[derive(Debug, Clone)]
struct PlainReborrowCarrierAlias {
    child_name: String,
    parent_name: String,
    sort: Option<ExprSort>,
    final_same_parent: bool,
}

fn derive_plain_reborrow_carrier_aliases<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    substitutions: &mut NameSubstitutions,
) -> Vec<PlainReborrowCarrierAlias> {
    let debug_names = debug_names_by_local(body);
    let mut local_to_borrow_name: HashMap<Local, String> = HashMap::new();
    let mut aliases = Vec::new();
    let analysis = crate::mir_analysis::not_final_places::NotFinalPlaces::new(tcx, body);
    let results = analysis.iterate_to_fixpoint(tcx, body, None);
    let mut cursor = results.into_results_cursor(body);

    for (index, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(index + 1);
        if body.local_decls.get(local).is_some_and(|decl| {
            matches!(
                decl.ty.kind(),
                TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
            )
        }) {
            local_to_borrow_name.insert(local, name.clone());
        }
    }

    for (bb_idx, block) in body.basic_blocks.iter_enumerated() {
        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            let StatementKind::Assign(box (dest, rvalue)) = &stmt.kind else {
                continue;
            };
            if !dest.projection.is_empty() {
                continue;
            }
            let Rvalue::Ref(_, BorrowKind::Mut { .. }, place) = rvalue else {
                continue;
            };
            if !is_plain_deref_reborrow(place) {
                continue;
            };
            let Some(parent_name) = local_to_borrow_name.get(&place.local).cloned() else {
                continue;
            };
            let child_name = format!("{parent_name}_rb{}", dest.local.as_u32());
            local_to_borrow_name.insert(dest.local, child_name.clone());
            let mut inserted_alias = false;

            let Some(names) = debug_names.get(&dest.local) else {
                continue;
            };
            let sort = crate::mir_analysis::translate::ty_to_expr_sort_enriched(
                tcx,
                body.local_decls[dest.local].ty,
            );
            let child_expr = PureExpr::Var(child_name.clone(), sort.clone());
            for name in names {
                if substitutions.contains_key(name) {
                    substitutions.insert(name.clone(), child_expr.clone());
                    substitutions.name_sorts.insert(name.clone(), sort.clone());
                    inserted_alias = true;
                }
            }
            if inserted_alias {
                let final_same_parent =
                    crate::mir_analysis::not_final_places::NotFinalPlaces::is_final_at(
                        &mut cursor,
                        place,
                        Location {
                            block: bb_idx,
                            statement_index: stmt_idx,
                        },
                    )
                    .is_some();
                aliases.push(PlainReborrowCarrierAlias {
                    child_name,
                    parent_name,
                    sort,
                    final_same_parent,
                });
            }
        }
    }

    aliases
}

fn debug_names_by_local(body: &Body<'_>) -> HashMap<Local, Vec<String>> {
    let mut names: HashMap<Local, Vec<String>> = HashMap::new();
    for debug in &body.var_debug_info {
        let VarDebugInfoContents::Place(place) = &debug.value else {
            continue;
        };
        if !place.projection.is_empty() {
            continue;
        }
        let name = debug.name.to_string();
        if name == "_" {
            continue;
        }
        names.entry(place.local).or_default().push(name);
    }
    names
}

fn is_plain_deref_reborrow(place: &Place<'_>) -> bool {
    place.projection.len() == 1 && matches!(place.projection.first(), Some(ProjectionElem::Deref))
}

fn is_plain_reborrow_parent_alias(expr: &PureExpr, aliases: &[PlainReborrowCarrierAlias]) -> bool {
    let PureExpr::BinOp(left, trust_wp_core::formula::BinOp::Eq, right) = expr else {
        return false;
    };
    let Some(left_name) = bare_var_name(left) else {
        return false;
    };
    let Some(right_name) = bare_var_name(right) else {
        return false;
    };
    aliases.iter().any(|alias| {
        !alias.final_same_parent
            && ((left_name == alias.child_name && right_name == alias.parent_name)
                || (left_name == alias.parent_name && right_name == alias.child_name))
    })
}

fn extend_final_plain_reborrow_parent_aliases(
    assumptions: &mut Vec<PureExpr>,
    aliases: &[PlainReborrowCarrierAlias],
) {
    for alias in aliases.iter().filter(|alias| alias.final_same_parent) {
        let fact = PureExpr::BinOp(
            Arc::new(PureExpr::Var(alias.child_name.clone(), alias.sort.clone())),
            trust_wp_core::formula::BinOp::Eq,
            Arc::new(PureExpr::Var(alias.parent_name.clone(), alias.sort.clone())),
        );
        if !assumptions.contains(&fact) {
            assumptions.push(fact);
        }
    }
}

fn bare_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        _ => None,
    }
}

fn derive_projected_snapshot_deref_aliases<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    substitutions: &mut NameSubstitutions,
) -> usize {
    let mut added = 0usize;
    for (bb, block) in body.basic_blocks.iter_enumerated() {
        let terminator = block.terminator();
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            continue;
        };
        if !is_snapshot_capture_call(tcx, &func) {
            continue;
        }

        let snapshot_names =
            snapshot_names_for_capture_result(body, substitutions, destination.local);
        if snapshot_names.is_empty() {
            continue;
        }

        // The captured reference is the sole inline `&expr`. For a direct
        // `Snapshot::capture(&expr)` it is the last argument of THIS call; for
        // the type-directed dispatch the matched `.capture()` is the identity
        // tail whose sole argument is the selector, so the `&expr` lives in the
        // preceding `snapshot_capture_select(&expr)` call — `ref_bb` is the
        // block that formed it (which the projection search below must scan).
        // (bug/869)
        let Some((ref_bb, captured_place)) = args
            .last()
            .and_then(|arg| resolve_dispatch_capture_place(tcx, body, bb, &arg.node))
        else {
            continue;
        };
        let alias =
            projected_mut_ref_snapshot_alias(tcx, body, ref_bb, &captured_place).or_else(|| {
                // Plain `snapshot!(*a)` of a `&mut T`: the snapshot's value is the
                // frozen current pointee `Deref(Var("a"))` (= `a_current`). Since
                // `Snapshot<T>` derefs to `T` identically, `*<snapshot>` must
                // resolve to that same frozen current — NOT a second `Deref`
                // (which would deref an integer). Reuse the snapshot's own
                // current-deref carrier value as the `*<snapshot>` alias. (#682)
                snapshot_names.iter().find_map(|name| {
                    substitutions.get(name).and_then(|value| match value {
                        PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(_, _)) => {
                            Some(value.clone())
                        }
                        _ => None,
                    })
                })
            });
        let Some(alias) = alias else {
            continue;
        };

        for snapshot_name in snapshot_names {
            let key = format!("*{snapshot_name}");
            if substitutions.contains_key(&key) {
                continue;
            }
            substitutions.insert(key, alias.clone());
            added += 1;
        }
    }
    added
}

fn snapshot_names_for_capture_result(
    body: &Body<'_>,
    substitutions: &NameSubstitutions,
    result_local: Local,
) -> Vec<String> {
    let call_result_name = format!("call_{}", result_local.as_u32());
    let mut names: Vec<String> = substitutions
        .iter()
        .filter_map(|(name, expr)| {
            if name.starts_with('*') || name.starts_with('^') {
                return None;
            }
            match expr {
                PureExpr::Var(var, _) if var == &call_result_name => Some(name.clone()),
                _ => None,
            }
        })
        .collect();
    for debug in &body.var_debug_info {
        let VarDebugInfoContents::Place(place) = &debug.value else {
            continue;
        };
        if place.local != result_local || !place.projection.is_empty() {
            continue;
        }
        let name = debug.name.to_string();
        if name != "_" && !names.contains(&name) {
            names.push(name);
        }
    }
    names
}

fn is_snapshot_capture_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    let Operand::Constant(box constant) = func else {
        return false;
    };
    let TyKind::FnDef(def_id, _) = constant.const_.ty().kind() else {
        return false;
    };
    let path = tcx.def_path_str(*def_id);
    path.ends_with("::capture") && path.contains("Snapshot")
}

fn snapshot_capture_argument_place<'tcx>(
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    operand: &Operand<'tcx>,
) -> Option<Place<'tcx>> {
    let (Operand::Copy(place) | Operand::Move(place)) = operand else {
        return None;
    };
    if !place.projection.is_empty() {
        return None;
    }

    for stmt in body.basic_blocks[bb].statements.iter().rev() {
        let rustc_middle::mir::StatementKind::Assign(box (dest, rvalue)) = &stmt.kind else {
            continue;
        };
        if dest.local != place.local || !dest.projection.is_empty() {
            continue;
        }
        let Rvalue::Ref(_, _, captured_place) = rvalue else {
            return None;
        };
        return Some(*captured_place);
    }
    None
}

/// Whether `func` calls the `snapshot!` dispatch's `snapshot_capture_select`. (bug/869)
fn is_dispatch_select_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    let Operand::Constant(box constant) = func else {
        return false;
    };
    let TyKind::FnDef(def_id, _) = constant.const_.ty().kind() else {
        return false;
    };
    tcx.def_path_str(*def_id)
        .ends_with("::snapshot_capture_select")
}

/// Resolve the captured `&expr` reborrow behind a snapshot capture, returning
/// the block that formed it and the borrowed place.
///
/// - A direct `Snapshot::capture(&expr)` forms `&expr` inline in `bb`, so the
///   last argument resolves there directly.
/// - The type-directed `snapshot!` dispatch's `.capture()` tail takes the ZST
///   selector as its argument; the `&expr` was formed one call earlier by
///   `snapshot_capture_select(&expr)`. Trace the selector local back to that
///   call and read its inline reborrow (in the select's own block). (bug/869)
fn resolve_dispatch_capture_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    operand: &Operand<'tcx>,
) -> Option<(rustc_middle::mir::BasicBlock, Place<'tcx>)> {
    if let Some(place) = snapshot_capture_argument_place(body, bb, operand) {
        return Some((bb, place));
    }
    let (Operand::Copy(sel) | Operand::Move(sel)) = operand else {
        return None;
    };
    if !sel.projection.is_empty() {
        return None;
    }
    for (sbb, block) in body.basic_blocks.iter_enumerated() {
        let Some(terminator) = &block.terminator else {
            continue;
        };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        else {
            continue;
        };
        if destination.local != sel.local
            || !destination.projection.is_empty()
            || !is_dispatch_select_call(tcx, func)
        {
            continue;
        }
        return args
            .last()
            .and_then(|arg| snapshot_capture_argument_place(body, sbb, &arg.node))
            .map(|place| (sbb, place));
    }
    None
}

fn projected_mut_ref_snapshot_alias<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    captured_place: &Place<'tcx>,
) -> Option<PureExpr> {
    let (alias_local, alias_projection, captured_ty) =
        projected_mut_ref_snapshot_alias_input(tcx, body, bb, captured_place)?;
    if alias_projection.is_empty() {
        return None;
    }
    let TyKind::Ref(_, inner_ty, mutability) = captured_ty.kind() else {
        return None;
    };
    if !mutability.is_mut() {
        return None;
    }
    let inner_sort = crate::mir_analysis::translate::ty_to_expr_sort_enriched(tcx, *inner_ty)?;
    let mut projection_segments = alias_projection
        .into_iter()
        .map(projected_snapshot_alias_projection_segment)
        .collect::<Option<Vec<_>>>()?;
    projection_segments.push("deref".to_string());

    Some(PureExpr::Var(
        format!(
            "__trust_wp_reborrow_{}_{}",
            alias_local.as_u32(),
            projection_segments.join("_"),
        ),
        Some(ExprSort::MutRef(Box::new(inner_sort))),
    ))
}

fn projected_mut_ref_snapshot_alias_input<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    captured_place: &Place<'tcx>,
) -> Option<(
    Local,
    Vec<ProjectionElem<Local, rustc_middle::ty::Ty<'tcx>>>,
    rustc_middle::ty::Ty<'tcx>,
)> {
    if let Some(source_place) = captured_snapshot_ref_source_place(body, bb, captured_place) {
        return Some((
            source_place.local,
            source_place.projection.iter().collect(),
            source_place.ty(body, tcx).ty,
        ));
    }
    Some((
        captured_place.local,
        captured_place.projection.iter().collect(),
        captured_place.ty(body, tcx).ty,
    ))
}

fn captured_snapshot_ref_source_place<'tcx>(
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    captured_place: &Place<'tcx>,
) -> Option<Place<'tcx>> {
    let mut projection = captured_place.projection.iter();
    if !matches!(projection.next(), Some(ProjectionElem::Deref)) || projection.next().is_some() {
        return None;
    }
    local_ref_source_place(body, bb, captured_place.local)
}

fn local_ref_source_place<'tcx>(
    body: &Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    local: Local,
) -> Option<Place<'tcx>> {
    for stmt in body.basic_blocks[bb].statements.iter().rev() {
        let rustc_middle::mir::StatementKind::Assign(box (dest, rvalue)) = &stmt.kind else {
            continue;
        };
        if dest.local != local || !dest.projection.is_empty() {
            continue;
        }
        let Rvalue::Ref(_, _, source_place) = rvalue else {
            return None;
        };
        return Some(*source_place);
    }
    None
}

fn projected_snapshot_alias_projection_segment(
    proj: ProjectionElem<Local, rustc_middle::ty::Ty<'_>>,
) -> Option<String> {
    match proj {
        ProjectionElem::Deref => Some("deref".to_string()),
        ProjectionElem::Field(field, _) => Some(format!("field{}", field.as_u32())),
        ProjectionElem::Downcast(_, variant) => Some(format!("downcast{}", variant.as_u32())),
        ProjectionElem::Index(local) => Some(format!("index{}", local.as_u32())),
        ProjectionElem::ConstantIndex {
            offset,
            min_length,
            from_end,
        } => Some(format!("const{offset}_{min_length}_{}", u8::from(from_end))),
        ProjectionElem::Subslice { from, to, from_end } => {
            Some(format!("subslice{from}_{to}_{}", u8::from(from_end)))
        }
        ProjectionElem::OpaqueCast(_) => Some("opaque".to_string()),
        ProjectionElem::UnwrapUnsafeBinder(_) => Some("unwrap".to_string()),
    }
}

/// Extract loop invariant-based continuation assumptions from ghost closures
/// that contain a loop preceding the proof_assert. (#2584)
fn extract_ghost_closure_loop_assumptions(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    containing_ghost_block: Option<&GhostBlock>,
    user_specs: &HashMap<DefId, StdSpec>,
    ctx: &ProofAssertContext<'_>,
) -> Vec<PureExpr> {
    let Some(ghost_block) = containing_ghost_block else {
        return Vec::new();
    };

    let Some(body_with_facts) = super::try_get_body_with_context(assertion.containing_fn) else {
        return Vec::new();
    };
    let mir_body = get_mir_body(body_with_facts);
    let ghost_closure_def_ids =
        ghost_closure_candidates_for_assertion(tcx, assertion, ghost_block, mir_body);

    let mut assumptions = Vec::new();
    for closure_def_id in ghost_closure_def_ids {
        let Some(local_def_id) = closure_def_id.as_local() else {
            continue;
        };
        let (flat_invariants, _, _, _, all_loop_spans) =
            collect_loop_contract_attrs(tcx, local_def_id);
        if flat_invariants.is_empty()
            || all_loop_spans.is_empty()
            || !proof_assert_is_after_all_loops(assertion.span, &all_loop_spans)
        {
            continue;
        }
        // Keep the first slice bounded to the single-loop ghost-closure case
        // required by #2584's `ghost/fmap_iter.rs` shape.
        if all_loop_spans.len() != 1 {
            continue;
        }

        let Ok(closure_body) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            tcx.optimized_mir(closure_def_id)
        })) else {
            continue;
        };
        let loop_analysis = detect_loops(closure_body);
        if loop_analysis.loops.len() != 1 {
            continue;
        }

        let arg_names = resolve_arg_names_or_warn(tcx, closure_def_id, None);
        let call_spec_ctx = CallSpecContext {
            tcx,
            user_specs,
            trait_specs: ctx.trait_specs,
            extern_specs: ctx.extern_specs,
        };
        let loop_body = extract_loop_body(
            closure_body,
            &arg_names,
            &loop_analysis.loops[0],
            Some(&loop_analysis.loops),
            Some(&call_spec_ctx),
            false,
        );

        let mut parsed_invariants = Vec::new();
        for inv_text in &flat_invariants {
            match parse_contract(inv_text) {
                Ok(expr) => parsed_invariants.push(expr),
                Err(e) => {
                    tracing::debug!(
                        "failed to parse ghost closure loop invariant '{}': {}",
                        inv_text,
                        e
                    );
                }
            }
        }
        if parsed_invariants.is_empty() {
            continue;
        }

        // For proof_assert, only inject the user invariants — not the full
        // continuation bundle (produces, structural, bridge facts) which references
        // loop-internal iterator state variables not declared in the proof_assert
        // encoding scope. Specialize the invariants for the completed-iterator
        // case: at loop exit, the iterator's view is empty. (#2584)
        let capture_names = closure_capture_names(tcx, closure_def_id);
        let is_fmap_iter = loop_body.for_loop_state.as_ref().is_some_and(|st| {
            super::iterator_spec_rewrite::helpers::is_fmap_backed_iterator(&st.iter_state)
                || super::iterator_spec_rewrite::helpers::is_logical_fmap_iter(&st.iter_state)
        });
        let specialized_invariants = if is_fmap_iter {
            specialize_invariants_for_completed_fmap_iter(&parsed_invariants, &capture_names)
        } else {
            parsed_invariants.clone()
        };
        for assumption in specialized_invariants
            .into_iter()
            .map(|expr| rewrite_ghost_closure_capture_vars(&expr, &capture_names))
        {
            if !assumptions.contains(&assumption) {
                assumptions.push(assumption);
            }
        }
    }
    if assumptions.is_empty() {
        assumptions.extend(extract_ghost_block_function_loop_assumptions(
            tcx,
            assertion,
            ghost_block,
            mir_body,
            user_specs,
            ctx,
        ));
    }
    assumptions
}

#[allow(clippy::similar_names)] // has_hir_loops / has_mir_loops are domain-distinct
fn ghost_closure_candidates_for_assertion(
    tcx: TyCtxt<'_>,
    assertion: &ProofAssert,
    ghost_block: &GhostBlock,
    mir_body: &Body<'_>,
) -> Vec<DefId> {
    let mut closure_def_ids = Vec::new();

    if let Some(mut current) = assertion.closure_def_id {
        while let Some(parent) = tcx.opt_parent(current) {
            current = parent;
            if !matches!(tcx.def_kind(parent), DefKind::Closure) {
                continue;
            }
            let Some(local_def_id) = parent.as_local() else {
                continue;
            };
            let (_, _, _, _, all_loop_spans) = collect_loop_contract_attrs(tcx, local_def_id);
            let has_hir_loops = !all_loop_spans.is_empty();
            let has_mir_loops = tcx.is_mir_available(parent)
                && std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    tcx.optimized_mir(parent)
                }))
                .ok()
                .map_or(false, |body| !detect_loops(body).loops.is_empty());
            if has_hir_loops || has_mir_loops {
                closure_def_ids.push(parent);
                break;
            }
        }
    }

    for closure_def_id in find_ghost_closure_def_ids_in_mir(mir_body, ghost_block.span) {
        if !closure_def_ids.contains(&closure_def_id) {
            closure_def_ids.push(closure_def_id);
        }
    }

    closure_def_ids
}

fn extract_ghost_block_function_loop_assumptions<'tcx>(
    tcx: TyCtxt<'tcx>,
    assertion: &ProofAssert,
    ghost_block: &GhostBlock,
    mir_body: &Body<'tcx>,
    _user_specs: &HashMap<DefId, StdSpec>,
    _ctx: &ProofAssertContext<'_>,
) -> Vec<PureExpr> {
    let (_, _, per_loop_invariants, _, all_loop_spans) =
        collect_loop_contract_attrs(tcx, assertion.containing_fn);
    // Keep the ghost-block span in the same expansion coordinate space as the
    // raw loop-attribute spans collected from HIR. Using source_callsite()
    // here can move the ghost block to source coordinates while the loop spans
    // remain in proc-macro expansion coordinates, which drops the live #2584
    // fallback match in ghost/fmap_iter.rs.
    let ghost_block_span = ghost_block.span;
    let loop_spans_in_block: Vec<(u32, u32)> = all_loop_spans
        .into_iter()
        .filter(|(start, end)| ghost_block_span.lo().0 <= *start && *end <= ghost_block_span.hi().0)
        .collect();
    if loop_spans_in_block.len() != 1 {
        return Vec::new();
    }
    let (loop_start, loop_end) = loop_spans_in_block[0];
    let invariant_texts = per_loop_invariants
        .into_iter()
        .find_map(|(start, end, invariants)| {
            (start == loop_start && end == loop_end).then_some(invariants)
        })
        .unwrap_or_default();
    let mut parsed_invariants = Vec::new();
    for inv_text in &invariant_texts {
        match parse_contract(inv_text) {
            Ok(expr) => parsed_invariants.push(expr),
            Err(e) => {
                tracing::debug!(
                    "failed to parse ghost block loop invariant '{}': {}",
                    inv_text,
                    e
                );
            }
        }
    }
    if parsed_invariants.is_empty() {
        return Vec::new();
    }

    let loop_analysis = detect_loops(mir_body);
    let matching_loops: Vec<_> = loop_analysis
        .loops
        .iter()
        .filter(|loop_info| {
            let header_pos = mir_body.basic_blocks[loop_info.header]
                .terminator()
                .source_info
                .span
                .lo()
                .0;
            loop_start <= header_pos
                && header_pos < loop_end
                && assertion
                    .location
                    .is_none_or(|location| !loop_info.body_blocks.contains(&location.block))
        })
        .collect();
    if matching_loops.len() != 1 {
        return Vec::new();
    }

    // For proof_assert in the fallback path (outer function, not ghost closure),
    // only inject user invariants — not the full continuation bundle which references
    // loop-internal iterator state variables not in the proof_assert scope. (#2584)
    // Always specialize: non-arg iterator views become fmap_new() at loop exit.
    let arg_names = resolve_arg_names_or_warn(tcx, assertion.containing_fn.to_def_id(), None);
    specialize_invariants_for_completed_fmap_iter(&parsed_invariants, &arg_names)
}

/// Specialize loop invariants for the proof_assert post-loop context by
/// replacing non-capture iterator views with the empty FMap. (#2584)
///
/// At loop exit, the FMap iterator is exhausted — its `view()` is the empty FMap.
/// The proof_assert encoding scope doesn't declare the loop-local iterator
/// variable, so `View(Var("iter"))` or `LogicFnCall("view", [Var("iter")])`
/// would trigger a ay sort mismatch panic. This function replaces both forms
/// for non-capture variables (loop-local iterator references) with `fmap_new()`.
///
/// The contract parser produces `LogicFnCall { name: "view", .. }` for `view(x)`
/// syntax, while the macro preprocess produces `View(x)` for `x@` syntax.
/// Both must be handled.
fn specialize_invariants_for_completed_fmap_iter(
    invariants: &[PureExpr],
    capture_names: &[String],
) -> Vec<PureExpr> {
    let captures: HashSet<&str> = capture_names.iter().map(String::as_str).collect();
    let fmap_new = || PureExpr::LogicFnCall {
        name: "fmap_new".to_string(),
        args: vec![],
    };
    invariants
        .iter()
        .map(|inv| {
            inv.rewrite_bottom_up(|node| match &node {
                // Match `x@` syntax (View node)
                PureExpr::View(inner) => match inner.as_ref() {
                    PureExpr::Var(name, _) if !captures.contains(name.as_str()) => fmap_new(),
                    _ => node,
                },
                // Match `view(x)` syntax (LogicFnCall node from contract parser)
                PureExpr::LogicFnCall { name, args } if name == "view" && args.len() == 1 => {
                    match &args[0] {
                        PureExpr::Var(var_name, _) if !captures.contains(var_name.as_str()) => {
                            fmap_new()
                        }
                        _ => node,
                    }
                }
                _ => node,
            })
        })
        .collect()
}

fn proof_assert_is_after_all_loops(span: rustc_span::Span, loop_spans: &[(u32, u32)]) -> bool {
    if loop_spans.is_empty() {
        return false;
    }
    let callsite = span.source_callsite();
    let proof_assert_start = callsite.lo().0;
    loop_spans.iter().all(|(_, end)| *end <= proof_assert_start)
}

/// Build a substitution map for callee call-assumption rewriting that drops
/// POST-call deref remappings (`*x -> call_N`, the value read AFTER the call).
///
/// A callee's postcondition (e.g. `^a > *a`) references the dereferenced
/// argument as observed AT the call (pre-call). Rewriting that pre-call `*a`
/// with the post-call read corrupts the postcondition. Only `*<simple var>`
/// keys whose value is a fresh `call_*` post-state symbol are removed; every
/// other mapping (including identity `*x` carriers) is preserved. (#682)
/// Drop the conflating `Deref(Var(x)) == call_N` equalities for variables `x`
/// whose CURRENT pointee was frozen by a `snapshot!(*x)`. See the call site:
/// these equate the frozen pre-call current with the post-call read. (#682)
fn drop_frozen_current_post_call_equalities(
    facts: &mut Vec<PureExpr>,
    substitutions: &NameSubstitutions,
) {
    let frozen_roots: HashSet<String> = substitutions
        .values()
        .filter_map(|value| match value {
            PureExpr::Deref(inner) => match inner.as_ref() {
                PureExpr::Var(name, _) => Some(name.clone()),
                _ => None,
            },
            _ => None,
        })
        .collect();
    if frozen_roots.is_empty() {
        return;
    }
    facts.retain(|fact| {
        let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = fact else {
            return true;
        };
        !(is_frozen_current_post_call_equality(lhs, rhs, &frozen_roots)
            || is_frozen_current_post_call_equality(rhs, lhs, &frozen_roots))
    });
}

fn is_frozen_current_post_call_equality(
    deref_side: &PureExpr,
    other_side: &PureExpr,
    frozen_roots: &HashSet<String>,
) -> bool {
    let PureExpr::Deref(inner) = deref_side else {
        return false;
    };
    let PureExpr::Var(name, _) = inner.as_ref() else {
        return false;
    };
    if !frozen_roots.contains(name) {
        return false;
    }
    matches!(other_side, PureExpr::Var(other, _) if other.starts_with("call_"))
}

fn drop_post_call_deref_remappings(
    substitutions: &std::collections::HashMap<String, PureExpr>,
) -> std::collections::HashMap<String, PureExpr> {
    substitutions
        .iter()
        .filter(|(key, value)| {
            let is_deref_key = key.strip_prefix('*').is_some_and(is_simple_ident_local);
            let is_post_call_value =
                matches!(value, PureExpr::Var(name, _) if name.starts_with("call_"));
            !(is_deref_key && is_post_call_value)
        })
        .map(|(key, value)| (key.clone(), value.clone()))
        .collect()
}

/// Build a substitution for callee PRECONDITION obligations that keeps the
/// dereferenced argument at its PRE-call value.
///
/// A callee's precondition `P(*x)` is evaluated against the value the caller
/// holds AT THE CALL — the pre-call current pointee `Deref(Var(x))`
/// (= `x_current`). The proof_assert substitution map, however, advances each
/// mutated reference root to its prophecy (`x -> Final(Var(x))`) to express the
/// post-call program state. Applying that to a surviving `Deref(Var(x))` in the
/// obligation rewrites it to `Deref(Final(Var(x)))` (= the POST-call pointee),
/// which is the wrong (and, in the proof_assert solve, unconstrained) value.
///
/// We therefore drop exactly the self-advancement entry `root -> Final(.. root
/// ..)` for any root the obligations actually dereference. Every other mapping
/// (including the post-call `*x -> call_N` remapping, already excluded upstream
/// for the call-assumption substitution) is preserved unchanged.
///
/// SOUND: removing an advancement mapping makes `*x` resolve to the pre-call
/// `x_current` — the exact value the callee observes — instead of a free
/// post-call symbol. The obligation is checked against the actual (more
/// constrained) argument value, so this can only make a VALID precondition
/// provable; it can never let a false precondition verify. (#682)
fn drop_self_advancement_for_dereffed_roots(
    substitutions: &std::collections::HashMap<String, PureExpr>,
    raw_obligations: &[PureExpr],
) -> std::collections::HashMap<String, PureExpr> {
    let mut dereffed_roots: HashSet<String> = HashSet::new();
    for obligation in raw_obligations {
        collect_dereffed_var_roots(obligation, &mut dereffed_roots);
    }
    if dereffed_roots.is_empty() {
        return substitutions.clone();
    }
    substitutions
        .iter()
        .filter(|(key, value)| {
            let advances_self = dereffed_roots.contains(key.as_str())
                && matches!(value, PureExpr::Final(_))
                && advancement_root_name(value).is_some_and(|root| root == key.as_str());
            !advances_self
        })
        .map(|(key, value)| (key.clone(), value.clone()))
        .collect()
}

/// Collect the names of variables that appear directly inside a `Deref(Var(_))`
/// anywhere in `expr` (the roots whose current pointee the expression reads).
fn collect_dereffed_var_roots(expr: &PureExpr, out: &mut HashSet<String>) {
    // `rewrite_bottom_up` visits every subterm; we only observe (returning each
    // node unchanged) and record any `Deref(Var(_))` root encountered.
    let _ = expr.rewrite_bottom_up(|node| {
        if let PureExpr::Deref(inner) = &node {
            if let PureExpr::Var(name, _) = inner.as_ref() {
                out.insert(name.clone());
            }
        }
        node
    });
}

/// For a `Final`-carrier substitution value, return the variable name at its
/// leaf (`Final(Var(x))` → `x`, `Final(Deref(Var(x)))` → `x`).
fn advancement_root_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Final(inner) | PureExpr::Deref(inner) => advancement_root_name(inner),
        _ => None,
    }
}

/// True when `fact` contains a sort-invalid `Deref(Var(_, Int))` — a deref of a
/// scalar-sorted variable. These arise as Snapshot-deref-identity equality
/// artifacts and must not be asserted. (#682)
/// Repair the sort-invalid `Deref(Var(x, scalar))` subterm (a deref of a scalar)
/// by collapsing it to `Var(x, scalar)`. Arises when `*<snapshot>` of a value
/// snapshot is materialized as an equality fact: a `Snapshot<T>` / frozen scalar
/// derefs to itself identically, so the deref is a no-op on the value. Repairing
/// in place keeps the fact well-sorted AND preserves it as a solver assumption
/// (vs. dropping the whole fact, which starved the mut-borrow proof_assert solve
/// of atoms). (#682)
fn repair_scalar_var_deref(fact: PureExpr) -> PureExpr {
    fact.rewrite_bottom_up(|node| {
        if let PureExpr::Deref(inner) = &node {
            if matches!(
                inner.as_ref(),
                PureExpr::Var(_, Some(ExprSort::Int | ExprSort::Bool | ExprSort::Float))
            ) {
                return inner.as_ref().clone();
            }
        }
        node
    })
}

fn is_simple_ident_local(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first == '_' || first.is_ascii_alphabetic())
        && chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

fn preserve_snapshot_substitution_value(expr: PureExpr) -> PureExpr {
    if transparent_adapter_inner(&expr).is_some() {
        preserve_transparent_adapter_view_witness(expr)
    } else {
        collapse_idempotent_views(expr)
    }
}

fn preserve_snapshot_fact_value(expr: PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| {
        if transparent_adapter_inner(&node).is_some() {
            preserve_transparent_adapter_view_witness(node)
        } else {
            node
        }
    })
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::PureExpr;

    use super::{
        asserted_i32_one_var, is_relacq_permission_recovery_rhs, preserve_snapshot_fact_value,
        preserve_snapshot_substitution_value, relacq_permission_var_for_result,
    };

    #[test]
    fn parses_i32_one_proof_assert_result_var() {
        assert_eq!(
            asserted_i32_one_var(Some("res == 1i32")).as_deref(),
            Some("res")
        );
        assert_eq!(
            asserted_i32_one_var(Some("1 == value")).as_deref(),
            Some("value")
        );
        assert_eq!(asserted_i32_one_var(Some("res == 2i32")), None);
        assert_eq!(asserted_i32_one_var(Some("res.field == 1i32")), None);
    }

    #[test]
    fn recognizes_relacq_permission_recovery_rhs() {
        assert!(is_relacq_permission_recovery_rhs(
            "Ghost::new(Some(at_view.into_inner(sync_view)))"
        ));
        assert!(!is_relacq_permission_recovery_rhs("Ghost::new(None)"));
    }

    #[test]
    fn extracts_relacq_permission_var_from_message_passing_shape() {
        let fn_source = r#"
            move |mut tokens: Ghost<Tokens>| {
                while !atomic.load(ghost! { |c: &LoadCommitter<bool, _>| {
                    inv.open(tokens.reborrow(), |inv: &mut MessagePassingAtomicInv| {
                        if !*snapshot!(c.val()).into_ghost() {
                            return
                        }
                        data_own = Ghost::new(Some(at_view.into_inner(sync_view)))
                    })
                }}) {}
                let res = unsafe { data.get(ghost! { data_own.as_ref().unwrap() }) };
                proof_assert!(res == 1i32)
            }
        "#;
        let file_source = r#"
            enum State {
                Synchronisation(AtView<Box<Perm<PermCell<i32>>>>, Resource<Excl<()>>),
            }
            impl Protocol for MessagePassingAtomicInv {
                fn protocol(self, data: Self::Public) -> bool {
                    pearlite! { State::Synchronisation(data_own, tok_write) =>
                        data_own.val().val()@ == 1
                    }
                }
            }
        "#;

        assert_eq!(
            relacq_permission_var_for_result(fn_source, "res", file_source).as_deref(),
            Some("data_own")
        );
    }

    #[test]
    fn rejects_relacq_shape_without_true_path_assignment_before_get() {
        let fn_source = r#"
            move |mut tokens: Ghost<Tokens>| {
                while !atomic.load(ghost! { |c: &LoadCommitter<bool, _>| {
                    if !*snapshot!(c.val()).into_ghost() { return }
                }}) {}
                let res = unsafe { data.get(ghost! { data_own.as_ref().unwrap() }) };
                data_own = Ghost::new(Some(at_view.into_inner(sync_view)));
                proof_assert!(res == 1i32)
            }
        "#;
        let file_source = "State::Synchronisation(data_own.val().val()@ == 1)";

        assert_eq!(
            relacq_permission_var_for_result(fn_source, "res", file_source),
            None
        );
    }

    #[test]
    fn preserve_snapshot_substitution_value_keeps_copied_adapter_bridge() {
        let copied_intersection = PureExpr::LogicFnCall {
            name: "Copied".to_string(),
            args: vec![PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "xs".to_string(),
                    None,
                )))),
                method: "intersection".to_string(),
                args: vec![PureExpr::View(Arc::new(PureExpr::Var(
                    "ys".to_string(),
                    None,
                )))],
            }],
        };

        let preserved = preserve_snapshot_substitution_value(copied_intersection);

        assert_eq!(
            preserved,
            PureExpr::View(Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                    "xs".to_string(),
                    None,
                )))),
                method: "intersection".to_string(),
                args: vec![PureExpr::View(Arc::new(PureExpr::Var(
                    "ys".to_string(),
                    None,
                )))],
            })),
            "snapshot substitutions should keep a bridged view witness for copied adapters"
        );
    }

    #[test]
    fn preserve_snapshot_substitution_value_keeps_scalar_identity_collapsed() {
        let copied_int = PureExpr::LogicFnCall {
            name: "Copied".to_string(),
            args: vec![PureExpr::Int(5)],
        };

        let preserved = preserve_snapshot_substitution_value(copied_int);

        assert_eq!(preserved, PureExpr::Int(5));
    }

    #[test]
    fn preserve_snapshot_fact_value_keeps_copied_adapter_bridge() {
        let fact = PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            trust_wp_core::formula::BinOp::Eq,
            Arc::new(PureExpr::LogicFnCall {
                name: "Copied".to_string(),
                args: vec![PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                        "xs".to_string(),
                        None,
                    )))),
                    method: "intersection".to_string(),
                    args: vec![PureExpr::View(Arc::new(PureExpr::Var(
                        "ys".to_string(),
                        None,
                    )))],
                }],
            }),
        );

        let preserved = preserve_snapshot_fact_value(fact);

        assert_eq!(
            preserved,
            PureExpr::BinOp(
                Arc::new(PureExpr::Var("result".to_string(), None)),
                trust_wp_core::formula::BinOp::Eq,
                Arc::new(PureExpr::View(Arc::new(PureExpr::MethodCall {
                    receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                        "xs".to_string(),
                        None,
                    )))),
                    method: "intersection".to_string(),
                    args: vec![PureExpr::View(Arc::new(PureExpr::Var(
                        "ys".to_string(),
                        None,
                    )))],
                }))),
            ),
            "snapshot facts should preserve the copied-adapter bridge for set relations"
        );
    }

    use trust_wp_core::formula::{BinOp, ExprSort};

    use super::{is_scalar_view_target, viewed_integer_comparison};

    fn int_var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), Some(ExprSort::Int))
    }

    fn cmp(lhs: PureExpr, op: BinOp, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), op, Arc::new(rhs))
    }

    #[test]
    fn viewed_int_lt_var_var_wraps_both_sides() {
        let expr = cmp(int_var("i"), BinOp::Lt, int_var("n"));
        let viewed = viewed_integer_comparison(&expr).expect("scalar int Lt should view");
        assert_eq!(
            viewed,
            cmp(
                PureExpr::View(Arc::new(int_var("i"))),
                BinOp::Lt,
                PureExpr::View(Arc::new(int_var("n"))),
            )
        );
    }

    #[test]
    fn viewed_int_lt_var_literal_wraps_both_sides() {
        let expr = cmp(int_var("i"), BinOp::Le, PureExpr::Int(8));
        let viewed = viewed_integer_comparison(&expr).expect("int literal RHS should view");
        assert_eq!(
            viewed,
            cmp(
                PureExpr::View(Arc::new(int_var("i"))),
                BinOp::Le,
                PureExpr::View(Arc::new(PureExpr::Int(8))),
            )
        );
    }

    #[test]
    fn viewed_int_returns_none_for_non_comparison_ops() {
        let expr = cmp(int_var("i"), BinOp::Add, int_var("n"));
        assert!(viewed_integer_comparison(&expr).is_none());
    }

    #[test]
    fn viewed_int_returns_none_for_unsorted_var() {
        // Unsorted Var is rejected: we cannot guarantee it is a scalar int.
        let expr = cmp(
            PureExpr::Var("i".to_string(), None),
            BinOp::Lt,
            PureExpr::Var("n".to_string(), None),
        );
        assert!(viewed_integer_comparison(&expr).is_none());
    }

    #[test]
    fn viewed_int_returns_none_for_bool_var() {
        let expr = cmp(
            PureExpr::Var("b".to_string(), Some(ExprSort::Bool)),
            BinOp::Eq,
            PureExpr::Var("b2".to_string(), Some(ExprSort::Bool)),
        );
        assert!(viewed_integer_comparison(&expr).is_none());
    }

    #[test]
    fn viewed_int_idempotent_on_already_viewed() {
        // View(i) cmp View(n) — already in view form; both sides count as
        // scalar view targets so the function still emits a view form
        // (without double-wrapping, since `View(View(_))` is idempotent at the
        // encoder level and `view_or_self` preserves an existing View node).
        let expr = cmp(
            PureExpr::View(Arc::new(int_var("i"))),
            BinOp::Lt,
            PureExpr::View(Arc::new(int_var("n"))),
        );
        let viewed = viewed_integer_comparison(&expr).expect("view form is a valid target");
        assert_eq!(viewed, expr);
    }

    #[test]
    fn is_scalar_view_target_accepts_int_var_and_int_literal() {
        assert!(is_scalar_view_target(&int_var("i")));
        assert!(is_scalar_view_target(&PureExpr::Int(42)));
        assert!(is_scalar_view_target(&PureExpr::View(Arc::new(int_var(
            "i"
        )))));
    }

    #[test]
    fn is_scalar_view_target_rejects_other_shapes() {
        assert!(!is_scalar_view_target(&PureExpr::Var(
            "x".to_string(),
            None
        )));
        assert!(!is_scalar_view_target(&PureExpr::Var(
            "b".to_string(),
            Some(ExprSort::Bool)
        )));
        assert!(!is_scalar_view_target(&cmp(
            int_var("i"),
            BinOp::Lt,
            int_var("n")
        )));
    }
}
