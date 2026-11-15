// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared proof_assert execution driver.
//!
//! Owns the common per-snapshot loop: snapshot error handling, assertion
//! preparation, ghost-context construction, substitution-fact merging,
//! solver dispatch, and result reporting. Each snapshot is wrapped in
//! `catch_unwind` for panic isolation (#2700) — a panic during one
//! proof_assert does not halt verification of remaining assertions.
//! Host-specific policy (loop-exit assumptions, semantic-fact handling)
//! is encoded as data via [`ProofAssertHost`] rather than duplicated
//! across two copy-pasted executors.
//!
//! Extracted from `in_function_proof_assert.rs` and
//! `standalone_proof_assert.rs` (#2332).

use std::{
    collections::{HashMap, HashSet},
    panic::{catch_unwind, AssertUnwindSafe},
    sync::Arc,
};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::source_map::SourceMap;
use tracing::{debug, trace};
use trust_wp_ay::{
    verify_function_with_modes_outcome, verify_mut_borrow_function_with_modes_outcome,
    Counterexample, MutBorrowRequest, VerificationRequest, VerificationResult,
};
use trust_wp_core::{
    formula::{BinOp, BorrowIdOrigin, ExprSort, Pattern, ProjectedFinalPin, PureExpr, UnOp},
    logic::{LogicFnDef, TypeInvariantDef},
    TrackLevel,
};
use trust_wp_driver::StdSpec;

use super::super::{
    super::{contracts::FunctionContract, ghost::GhostBlock, mir_analysis::MutBorrowBody},
    ghost_context::{
        build_ghost_context_for_function, collect_focus_var_names, rustc_span_to_source_span,
        GhostBuildContext,
    },
    helpers::{prepare_proof_assert, synthesize_identity_final_values_with_expr},
    proof_assert_snapshot::AssertionSnapshot,
    reporting::{
        report_proof_assert_outcome_result, report_proof_assert_result, ProofAssertCounters,
    },
};

/// Shared context for proof_assert verification, independent of host kind.
pub(in crate::callbacks) struct ProofAssertDriverContext<'a> {
    pub(in crate::callbacks) pa_setup: &'a super::super::proof_assert_verify::ProofAssertSetup<'a>,
    pub(in crate::callbacks) pa_ctx: &'a super::super::verification_context::ProofAssertContext<'a>,
    pub(in crate::callbacks) pa_logic_fns_opt: Option<&'a [LogicFnDef]>,
    pub(in crate::callbacks) type_invariants_opt: Option<&'a [TypeInvariantDef]>,
    pub(in crate::callbacks) ghost_blocks: &'a [GhostBlock],
    pub(in crate::callbacks) track_level: TrackLevel,
    pub(in crate::callbacks) timeout: Option<std::time::Duration>,
    pub(in crate::callbacks) local_crate_name: &'a str,
    pub(in crate::callbacks) source_map: &'a SourceMap,
}

/// Host-specific policy for proof_assert verification.
///
/// Encodes the contracted-vs-contractless distinction as data rather than
/// two duplicated execution paths.
pub(in crate::callbacks) enum ProofAssertHost<'a> {
    /// Function has explicit contracts (`#[requires]`/`#[ensures]`).
    Contracted {
        contract: &'a FunctionContract,
        arg_names: &'a [String],
        user_specs: &'a HashMap<DefId, StdSpec>,
        trait_specs: &'a HashMap<DefId, StdSpec>,
        extern_specs: &'a HashMap<String, StdSpec>,
        mut_borrow_body: Option<&'a MutBorrowBody>,
        /// Caller-side expiry pins for this body (#prophecy-slots M6).
        projected_final_pins: &'a [ProjectedFinalPin],
        loop_spans: &'a [(u32, u32)],
        loop_exit_assumptions: Option<&'a [PureExpr]>,
        def_path: &'a str,
    },
    /// Function has proof_assert! but no explicit contracts.
    Contractless {
        contract: &'a FunctionContract,
        user_specs: &'a HashMap<DefId, StdSpec>,
        trait_specs: &'a HashMap<DefId, StdSpec>,
        extern_specs: &'a HashMap<String, StdSpec>,
        mut_borrow_body: Option<&'a MutBorrowBody>,
        /// Caller-side expiry pins for this body (#prophecy-slots M6).
        projected_final_pins: &'a [ProjectedFinalPin],
        def_path: &'a str,
    },
}

impl<'a> ProofAssertHost<'a> {
    fn contract(&self) -> &FunctionContract {
        match self {
            ProofAssertHost::Contracted { contract, .. }
            | ProofAssertHost::Contractless { contract, .. } => contract,
        }
    }

    fn def_path(&self) -> &str {
        match self {
            ProofAssertHost::Contracted { def_path, .. }
            | ProofAssertHost::Contractless { def_path, .. } => def_path,
        }
    }

    fn arg_names(&self) -> &[String] {
        match self {
            ProofAssertHost::Contracted { arg_names, .. } => arg_names,
            ProofAssertHost::Contractless { .. } => &[],
        }
    }

    fn user_specs(&self) -> &HashMap<DefId, StdSpec> {
        match self {
            ProofAssertHost::Contracted { user_specs, .. }
            | ProofAssertHost::Contractless { user_specs, .. } => user_specs,
        }
    }

    fn trait_specs(&self) -> &HashMap<DefId, StdSpec> {
        match self {
            ProofAssertHost::Contracted { trait_specs, .. }
            | ProofAssertHost::Contractless { trait_specs, .. } => trait_specs,
        }
    }

    fn extern_specs(&self) -> &HashMap<String, StdSpec> {
        match self {
            ProofAssertHost::Contracted { extern_specs, .. }
            | ProofAssertHost::Contractless { extern_specs, .. } => extern_specs,
        }
    }

    fn mut_borrow_body(&self) -> Option<&'a MutBorrowBody> {
        match self {
            ProofAssertHost::Contracted {
                mut_borrow_body, ..
            }
            | ProofAssertHost::Contractless {
                mut_borrow_body, ..
            } => *mut_borrow_body,
        }
    }

    /// Caller-side expiry pins proven for the host body (#prophecy-slots M6).
    ///
    /// M5 wired `projected_expiry` into the CONTRACT extraction pipeline only
    /// (`parsing::extraction` → `solver_dispatch`), so the `ghost!` /
    /// `proof_assert!` shapes — which are the very ones that take a `&mut` out
    /// of a call result and let it die inside the body — were never reached.
    /// Both hosts now carry the same lane, computed by the same adjudicator on
    /// the same MIR body.
    fn projected_final_pins(&self) -> &'a [ProjectedFinalPin] {
        match self {
            ProofAssertHost::Contracted {
                projected_final_pins,
                ..
            }
            | ProofAssertHost::Contractless {
                projected_final_pins,
                ..
            } => projected_final_pins,
        }
    }
}

/// Verify a batch of proof_assert snapshots using the shared execution pipeline.
///
/// This is the single owner of the per-snapshot loop:
/// snapshot error → prepare → ghost-context → host policy → dispatch → report.
pub(in crate::callbacks) fn verify_proof_assert_snapshots(
    tcx: TyCtxt<'_>,
    host: &ProofAssertHost<'_>,
    ctx: &ProofAssertDriverContext<'_>,
    snapshots: Vec<
        Result<AssertionSnapshot, super::super::proof_assert_snapshot::AssertionSnapshotError>,
    >,
    pa_counters: &mut ProofAssertCounters,
) {
    for snapshot_result in snapshots {
        // Crate wall-clock budget (#2674). A crate whose obligations all live
        // in one function's `ghost!` block spends its whole budget HERE, where
        // no per-function check can fire: ghost/ghost_set ran every assertion
        // at the full per-obligation budget until the harness killed the
        // process, and a killed process reports nothing at all — no verdict,
        // no goal coverage, not even the assertions it had discharged. Stop on
        // the crate's own budget and say so: a snapshot skipped here is
        // counted as an error, never as a pass.
        if super::timeout_budget::crate_budget_exhausted() {
            eprintln!(
                "trust-wp: {} proof_assert skipped (crate wall-clock budget \
                 exhausted) (#2674)",
                host.def_path(),
            );
            pa_counters.errors += 1;
            continue;
        }
        let snapshot = match snapshot_result {
            Ok(snapshot) => snapshot,
            Err(err) => {
                report_snapshot_error(tcx, &err, pa_counters);
                continue;
            }
        };

        // Per-snapshot catch_unwind boundary (#2700).
        //
        // Wraps the entire snapshot processing pipeline (preparation, ghost
        // context construction, solver dispatch, result reporting) so that a
        // panic in one proof_assert snapshot does not halt the remaining
        // snapshots. Mirrors the per-contract boundary in
        // standalone_proof_assert.rs (#2290).
        let def_path = host.def_path().to_string();
        let panic_result = catch_unwind(AssertUnwindSafe(|| {
            verify_single_snapshot(tcx, host, ctx, &snapshot, pa_counters);
        }));

        if let Err(panic_payload) = panic_result {
            let reason = ay_core::panic_payload_to_string(panic_payload.as_ref());
            pa_counters.errors += 1;
            // Classify ay panics distinctly from trust-wp-side programmer errors,
            // matching the function-level panic handler in verification.rs. (#2687)
            if crate::callbacks::panic_hook::is_ay_panic_for_hook(&reason) {
                eprintln!("trust-wp: {def_path} ay solver panic during proof_assert: {reason}");
            } else {
                eprintln!("trust-wp: {def_path} panicked during proof_assert: {reason}");
            }
            eprintln!("  (continuing with remaining proof_assert snapshots)");
        }
    }
}

/// Process a single proof_assert snapshot through the full pipeline.
///
/// Extracted from the per-snapshot loop body in `verify_proof_assert_snapshots`
/// to enable per-snapshot `catch_unwind` isolation (#2700). If this function
/// panics, the caller catches the panic and continues with the next snapshot.
fn verify_single_snapshot(
    tcx: TyCtxt<'_>,
    host: &ProofAssertHost<'_>,
    ctx: &ProofAssertDriverContext<'_>,
    snapshot: &AssertionSnapshot,
    pa_counters: &mut ProofAssertCounters,
) {
    let pa = &snapshot.assertion;
    trace!(
        closure_def_id = ?pa.closure_def_id,
        source_scope = ?pa.source_scope,
        location = ?pa.location,
        def_path = %host.def_path(),
        "proof_assert detail",
    );

    let mut prepared = match prepare_proof_assert(
        tcx,
        snapshot,
        ctx.pa_setup,
        ctx.pa_ctx,
        ctx.local_crate_name,
    ) {
        Ok(Some(prepared)) => prepared,
        Ok(None) => return,
        Err(()) => {
            pa_counters.errors += 1;
            return;
        }
    };
    prepared.is_contractless = matches!(host, ProofAssertHost::Contractless { .. });

    // Host-specific: contracted functions inject loop-exit and post-loop assumptions.
    if let ProofAssertHost::Contracted {
        loop_spans,
        loop_exit_assumptions,
        ..
    } = host
    {
        // fact-source: loop_lane_exit_facts
        extend_with_loop_assumptions(
            &mut prepared.preconditions,
            pa.span,
            loop_spans,
            *loop_exit_assumptions,
            snapshot,
            &super::super::proof_assert_verify::rebound_param_names(tcx, snapshot),
            ctx.pa_ctx.verbose,
        );
    }
    // fact-source: match_exit_goals
    let post_loop_derived = synthesize_post_loop_match_exit_goals(
        &mut prepared.preconditions,
        &prepared.ensures,
        ctx.pa_ctx.logic_fn_defs,
        &|get| crate::callbacks::list_match_exit::cons_discriminant_of(tcx, get),
    );
    if ctx.pa_ctx.verbose && post_loop_derived > 0 {
        debug!(
            "trust-wp:   (proof_assert: {post_loop_derived} post-loop match-exit goal(s) synthesized)"
        );
    }
    let closure_captures_opt = (!prepared.closure_capture_infos.is_empty())
        .then_some(prepared.closure_capture_infos.as_slice());

    let ghost_build_ctx = GhostBuildContext {
        tcx,
        user_specs: host.user_specs(),
        trait_specs: host.trait_specs(),
        extern_specs: host.extern_specs(),
    };
    let ghost_facts = build_ghost_context_for_function(
        &ghost_build_ctx,
        host.contract(),
        host.arg_names(),
        ctx.ghost_blocks,
        &collect_focus_var_names(
            &prepared.preconditions,
            &prepared.ensures,
            prepared.return_expr.as_ref(),
        ),
        Some(pa.span),
        pa.location,
    );

    // fact-source: ghost_context_handoff
    let mut pa_ghost_context = ghost_facts.alias_facts;

    // Semantic facts are postcondition-derived assumptions from ghost helper
    // calls (#2326). Both hosts now apply them uniformly — the previous
    // silent omission in the contractless path was an unowned policy
    // divergence, not a deliberate design choice. (#2332)
    for fact in ghost_facts.semantic_facts {
        if !prepared.preconditions.contains(&fact) {
            // fact-source: ghost_context_handoff
            prepared.preconditions.push(fact);
        }
    }

    // fact-source: substitution_facts
    merge_substitution_facts(
        &mut pa_ghost_context,
        &snapshot.substitution_facts,
        prepared.has_mutating_call_effect,
    );

    if ctx.pa_ctx.verbose {
        log_ghost_context(tcx, host, &pa_ghost_context);
    }

    let pa_ghost_context_opt =
        (!pa_ghost_context.is_empty()).then_some(pa_ghost_context.as_slice());
    let mut_borrow_body = host.mut_borrow_body();
    if let Some(body) = mut_borrow_body {
        // fact-source: delayed_writebacks
        merge_delayed_writeback_assumptions(
            &mut prepared.preconditions,
            &body.delayed_writeback_assumptions,
            &body.mutation_continued_params,
        );
        // Filter substitution facts that fuse the *entry-time* dereference of a
        // mutation-continued parameter with a post-call SSA carrier
        // (e.g. `*a == call_2`). See bug/682 / #5.
        //
        // The snapshot system inserts `"*<param>" -> Var("call_N")` into the
        // proof_assert substitution map so that proof_assert text references
        // to `*<param>` are rewritten to the post-call SSA carrier. Emitting
        // that mapping as an SMT equality, however, pins `<param>_current`
        // (the encoder's name for the entry-time deref) to `call_N` (the
        // post-call value). Combined with the call_assumption
        // `^<param> > *<param>` (= `<param>_final > <param>_current`) plus a
        // companion fact `call_N == <param>_final` (the post-call value IS
        // the prophecy final for mutation-continued params), this collapses
        // base premises to UNSAT — `call_N < <param>_final` and
        // `call_N == <param>_final` — and trips the vacuity guard.
        //
        // Only the entry-time-pinning side is unsound. The
        // `^<param> == call_N` substitution is preserved (it correctly
        // identifies the prophecy final with the post-call value).
        // fact-source: entry_pinning_withdrawal
        retain_non_entry_pinning_substitution_facts(
            &mut prepared.preconditions,
            &body.mutation_continued_params,
        );
    }

    let closure_call_assumptions = collect_closure_call_assumptions(&prepared.preconditions);
    let mutation_continued = collect_proof_assert_mutation_continued_vars(&prepared.preconditions);
    // fact-source: call_assumption_handoff
    let mut proof_assert_call_assumptions = snapshot.call_assumptions.clone();
    for assumption in closure_call_assumptions {
        if !proof_assert_call_assumptions.contains(&assumption) {
            // fact-source: closure_call_assumptions
            proof_assert_call_assumptions.push(assumption);
        }
    }
    let synthesized_final_values = if mut_borrow_body.is_none() {
        synthesize_proof_assert_final_values(
            prepared.has_mutating_call_effect,
            &prepared.ensures,
            &proof_assert_call_assumptions,
            snapshot.call_effect_expr.as_ref(),
            &mutation_continued,
        )
    } else {
        None
    };
    let mut final_values = mut_borrow_body
        .map(|body| body.final_values.clone())
        .or_else(|| synthesized_final_values.clone())
        .unwrap_or_default();
    if let Some(body) = mut_borrow_body {
        synthesize_reborrow_carrier_final_declarations(
            &mut final_values,
            body,
            &prepared.preconditions,
            &prepared.ensures,
            prepared.return_expr.as_ref(),
        );
    }
    // #prophecy-slots M6: the caller-side expiry pins for this body. Empty
    // unless `projected_expiry` PROVED a death point (R0..R11); the encoder
    // refuses fail-closed on top of that whenever the projection cannot be
    // walked exactly (`bind_projected_final_value`).
    let projected_pins =
        (!host.projected_final_pins().is_empty()).then(|| host.projected_final_pins().to_vec());
    if let Some(pins) = projected_pins.as_ref() {
        debug!(
            "prophecy-slots M6: {} caller-side expiry pin(s) available for proof_assert in {}",
            pins.len(),
            host.def_path(),
        );
    }
    let has_final_values = proof_assert_uses_mut_borrow_lane(
        mut_borrow_body.is_some(),
        synthesized_final_values.is_some(),
        !final_values.is_empty(),
        projected_pins.is_some(),
    );
    let mutation_continued = if let Some(body) = mut_borrow_body {
        (!body.mutation_continued_params.is_empty())
            .then_some(body.mutation_continued_params.clone())
    } else {
        (!mutation_continued.is_empty()).then_some(mutation_continued)
    };
    if ctx.pa_ctx.verbose {
        if has_final_values {
            debug!(
                "trust-wp:   (proof_assert: {} synthesized final value(s), {} mutation-continued param(s))",
                final_values.len(),
                mutation_continued.as_ref().map_or(0, HashSet::len),
            );
            let mut final_entries: Vec<_> = final_values.iter().collect();
            final_entries.sort_by_key(|(lhs_a, _)| *lhs_a);
            for (name, expr) in final_entries {
                debug!("trust-wp:     final_value[{name}]: {expr}");
            }
        }
    }
    if let Some(body) = mut_borrow_body {
        if has_direct_fresh_reborrow_parent_equality(body, &prepared.ensures) {
            report_proof_assert_result(
                Ok(VerificationResult::Failed(Counterexample::empty())),
                &prepared,
                pa_counters,
            );
            return;
        }
    }
    // Guard against mode_overrides/logic_fns length mismatch (#2700).
    // mode_overrides is computed from the full logic_fn_defs set, but
    // pa_logic_fns_opt may be a filtered subset. When lengths diverge,
    // drop mode_overrides rather than triggering an EncodingError.
    let effective_mode_overrides = match (prepared.mode_overrides.as_deref(), ctx.pa_logic_fns_opt)
    {
        (Some(modes), Some(fns)) if modes.len() != fns.len() => None,
        _ => prepared.mode_overrides.as_deref(),
    };
    // Detect `&mut [T]` slice parameters of the containing function so the
    // encoder emits slice-length-preservation axioms (slice length is
    // immutable through `&mut [T]`). Without it, a slice param mutated across
    // an inner call has its prophecy length left free (bitvectors/bitwalker).
    let slice_length_stable_vars: Option<Vec<String>> =
        super::super::try_get_body_with_context(tcx, pa.containing_fn).and_then(|bwf| {
            let mir_body = crate::mir_analysis::get_mir_body(&bwf);
            let arg_names = host.arg_names();
            let names: Vec<String> = arg_names
                .iter()
                .enumerate()
                .filter_map(|(index, name)| {
                    let local = rustc_middle::mir::Local::from_usize(index + 1);
                    let is_mut_slice = mir_body.local_decls.get(local).is_some_and(|decl| {
                    matches!(
                        decl.ty.kind(),
                        rustc_middle::ty::TyKind::Ref(_, inner, rustc_middle::ty::Mutability::Mut)
                            if matches!(inner.kind(), rustc_middle::ty::TyKind::Slice(_))
                    )
                });
                    is_mut_slice.then(|| name.clone())
                })
                .collect();
            (!names.is_empty()).then_some(names)
        });
    // Collect the containing function's ADT declarations so proof_assert
    // scopes use the same native recursive datatype encoding as contract
    // scopes. per_contract.rs threads build_adt_decls into every contract
    // verify request; without the same plumb here the encoder synthesizes a
    // flat all-Int stand-in for recursive ADTs (e.g. Adt_Leaf_Node for Tree),
    // the one-step unfolding facts get sort-coerced, and the fail-closed
    // guard demotes the proof_assert with SpecAxiomDropped. Same tcx/def_id
    // derivation as the contract path: the snapshot's containing function
    // (identical for the in-function host; the authoritative scope for the
    // standalone host, whose synthesized contract mirrors the same fn).
    // (adtpa; build_adt_decls peels the transparent Box/Rc/Arc wrappers so a
    // wrapper decl can never hijack their canonical Int view sort.)
    let adt_decls = super::super::adt_analysis::build_adt_decls(tcx, pa.containing_fn.to_def_id());
    let adt_decls_opt = if adt_decls.is_empty() {
        None
    } else {
        trace!(
            adts = adt_decls.len(),
            "proof_assert ADT declarations collected"
        );
        Some(adt_decls)
    };
    // Mark this verification as a proof_assert obligation so the obligation-level
    // batch precheck stays off it (a precheck `Verified` lacks the strict solver
    // evidence proof_assert reporting requires). (#transpose)
    let _proof_assert_guard = trust_wp_ay::ProofAssertModeGuard::enter();
    let pa_result = if has_final_values {
        let mut request =
            MutBorrowRequest::new(&prepared.preconditions, &prepared.ensures, &final_values)
                .slice_length_stable_vars(slice_length_stable_vars)
                .ghost_context(pa_ghost_context_opt)
                .return_expr(prepared.return_expr.as_ref())
                .logic_fns(ctx.pa_logic_fns_opt)
                .local_unfolding_logic_fns(Some(ctx.pa_ctx.logic_fn_defs))
                .mode_overrides(effective_mode_overrides)
                .type_invariants(ctx.type_invariants_opt)
                .track(Some(ctx.track_level))
                .timeout(ctx.timeout)
                .closure_captures(closure_captures_opt)
                .mutation_continued_params(mutation_continued)
                .adt_decls(adt_decls_opt)
                .projected_final_pins(projected_pins)
                .assert_grounded_ensures(false);
        if let Some(body) = mut_borrow_body {
            request = request
                .resolve_assumptions(resolve_assumption_names(body))
                .prophecy_writebacks(immediate_prophecy_writebacks(body))
                .borrow_finality((!body.finality.is_empty()).then_some(body.finality.clone()))
                .borrow_id_origins(
                    (!body.borrow_id_origins.is_empty()).then_some(body.borrow_id_origins.clone()),
                );
        }
        verify_mut_borrow_function_with_modes_outcome(request)
    } else {
        verify_function_with_modes_outcome(
            VerificationRequest::new(&prepared.preconditions, &prepared.ensures)
                .ghost_context(pa_ghost_context_opt)
                .return_expr(prepared.return_expr.as_ref())
                .logic_fns(ctx.pa_logic_fns_opt)
                .local_unfolding_logic_fns(Some(ctx.pa_ctx.logic_fn_defs))
                .mode_overrides(effective_mode_overrides)
                .type_invariants(ctx.type_invariants_opt)
                .track(Some(ctx.track_level))
                .timeout(ctx.timeout)
                .closure_captures(closure_captures_opt)
                .adt_decls(adt_decls_opt),
        )
    }
    .map_err(
        |e| match rustc_span_to_source_span(ctx.source_map, pa.span) {
            Some(src_span) => e.with_span(src_span),
            None => e,
        },
    );

    report_proof_assert_outcome_result(pa_result, &prepared, pa_counters);
}

/// Whether a proof_assert obligation must be dispatched on the mut-borrow lane.
///
/// The first three inputs are the pre-existing rule: a `&mut` parameter body,
/// synthesized finals, or any final value at all.
///
/// The fourth is #prophecy-slots M6. A caller-side expiry pin can only be BOUND
/// on the mut-borrow lane — `bind_projected_final_values` runs inside
/// `apply_mut_borrow_base_assertions`, and the pure `VerificationRequest` has no
/// prophecy machinery at all. The ghost-cluster shape
/// (`let mut m = ..; if let Some(x) = m.get_mut_ghost(..) { *x = 43; }`) owns a
/// proven death but no `&mut` PARAMETER, so without this term the pin the driver
/// just proved would be dropped on the floor at the request boundary.
///
/// Routing such a body through `MutBorrowRequest` with an empty `final_values`
/// map adds no premise of its own: `bind_final_values` over an empty map binds
/// nothing, and every other mut-borrow input (resolve assumptions, writebacks,
/// finality, id origins) stays `None` because `mut_borrow_body` is `None`.
fn proof_assert_uses_mut_borrow_lane(
    has_mut_borrow_body: bool,
    has_synthesized_finals: bool,
    has_final_values: bool,
    has_projected_pins: bool,
) -> bool {
    has_mut_borrow_body || has_synthesized_finals || has_final_values || has_projected_pins
}

/// Report a snapshot construction error.
fn report_snapshot_error(
    tcx: TyCtxt<'_>,
    err: &super::super::proof_assert_snapshot::AssertionSnapshotError,
    pa_counters: &mut ProofAssertCounters,
) {
    pa_counters.errors += 1;
    let loc = tcx
        .sess
        .source_map()
        .span_to_diagnostic_string(err.assertion.span);
    eprintln!("trust-wp: error: {}", err.reason);
    eprintln!("  at {loc}");
}

/// Merge `snapshot.substitution_facts` into ghost context, deduplicating by
/// string representation.
///
/// Shared helper so the `HashSet<String>` dedup logic exists in one place. (#2332)
fn merge_substitution_facts(
    ghost_context: &mut Vec<PureExpr>,
    substitution_facts: &[PureExpr],
    has_mutating_call_effect: bool,
) {
    if substitution_facts.is_empty() {
        return;
    }
    let existing: HashSet<String> = ghost_context.iter().map(|e| format!("{e}")).collect();
    for fact in substitution_facts {
        if (has_mutating_call_effect && is_stale_mutation_alias_fact(fact))
            || is_stale_closure_capture_env_fact(fact)
        {
            continue;
        }
        if !existing.contains(&format!("{fact}")) {
            // fact-source: substitution_facts
            ghost_context.push(fact.clone());
        }
    }
}

fn merge_delayed_writeback_assumptions(
    preconditions: &mut Vec<PureExpr>,
    assumptions: &[PureExpr],
    mutation_continued_params: &HashSet<String>,
) {
    for assumption in assumptions {
        // Suppress `*parent == ^child` (= `parent_current == child_final`)
        // assumptions when the parent is mutation-continued. See bug/682 / #5:
        // the call_assumption already advances `parent_final` through the
        // child's final on the post-call side, while
        // `<parent>_current` is the entry-time current value in the encoder's
        // single-SSA name scheme. Fusing them here collapses base premises to
        // UNSAT and trips the vacuity guard for any precondition that pins
        // `*parent` to a concrete value. Mirrors the gate in
        // `crates/trust-wp-ay/src/verify/mut_borrow/resolve.rs::emit_prophecy_writebacks`.
        if is_delayed_writeback_for_mutation_continued(assumption, mutation_continued_params) {
            continue;
        }
        if !preconditions.contains(assumption) {
            // fact-source: delayed_writebacks
            preconditions.push(assumption.clone());
        }
    }
}

/// Remove preconditions of shape `Deref(Var(parent)) == Var(call_carrier)`
/// when `parent` is mutation-continued. See bug/682 / #5.
///
/// These preconditions come from the proof_assert snapshot's substitution
/// map. The map carries the rewrite "post-call `*parent` is `call_N`" so
/// that occurrences of `*parent` in the proof_assert text resolve to the
/// post-call SSA carrier. When emitted as an SMT-level equality, however,
/// the LHS `Deref(Var(parent))` encodes as `<parent>_current` — the
/// encoder's name for the *entry-time* dereference — so the resulting
/// `<parent>_current == call_N` assertion fuses the entry-time and post-
/// call values. For mutation-continued parents this collapses base premises
/// to UNSAT in the presence of the call_assumption.
///
/// The companion `Final(Var(parent)) == Var(call_carrier)` substitution
/// fact (encoded as `<parent>_final == call_N`) is consistent with the
/// call_assumption (`<parent>_final > <parent>_current` is satisfiable
/// alongside `<parent>_final == call_N`) and is preserved.
fn retain_non_entry_pinning_substitution_facts(
    preconditions: &mut Vec<PureExpr>,
    mutation_continued_params: &HashSet<String>,
) {
    if mutation_continued_params.is_empty() {
        return;
    }
    preconditions.retain(|fact| {
        !is_entry_pinning_substitution_fact(fact, mutation_continued_params)
            && !is_final_eq_call_carrier(fact, mutation_continued_params)
    });
}

/// Match `Final(Var(parent)) == Var(call_carrier)` for mutation-continued
/// `parent`. This substitution fact identifies the post-call SSA carrier with
/// the prophecy final — true under the semantics of mutation-continued
/// parents — but its presence alongside the substituted call_assumption
/// `Final(Var(parent)) > Var(call_carrier)` produces `^parent > ^parent`,
/// which is UNSAT and trips the vacuity guard. Dropping the fact lets the
/// solver see the call_assumption as `^parent > <unconstrained call_carrier>`
/// (still satisfiable) while preserving the proof_assert rewrite of
/// `*parent` to the carrier. (bug/682 / #5)
fn is_final_eq_call_carrier(expr: &PureExpr, mutation_continued_params: &HashSet<String>) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    is_final_eq_call_carrier_sides(lhs, rhs, mutation_continued_params)
        || is_final_eq_call_carrier_sides(rhs, lhs, mutation_continued_params)
}

fn is_final_eq_call_carrier_sides(
    final_side: &PureExpr,
    carrier_side: &PureExpr,
    mutation_continued_params: &HashSet<String>,
) -> bool {
    let parent_name = match final_side {
        // `Final(Var(parent))` shape — pre-encoder.
        PureExpr::Final(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => Some(name.clone()),
            _ => None,
        },
        // `Var("<parent>_final")` shape — post-normalisation.
        PureExpr::Var(name, _) => name
            .strip_suffix("_final")
            .map(|stripped| stripped.to_string()),
        _ => None,
    };
    let Some(parent_name) = parent_name else {
        return false;
    };
    if !mutation_continued_params.contains(&parent_name) {
        return false;
    }
    let PureExpr::Var(carrier_name, _) = carrier_side else {
        return false;
    };
    carrier_name.starts_with("$call_") || carrier_name.starts_with("$_call_")
}

/// Match the entry-time pinning shape generated by the proof_assert snapshot
/// system for mutation-continued parents. We have to recognise two flavours
/// of `Var`/`Deref` because earlier normalisation passes may have rewritten
/// `Deref(Var("a"))` to the literal `Var("a_current")` before this filter
/// runs.
fn is_entry_pinning_substitution_fact(
    expr: &PureExpr,
    mutation_continued_params: &HashSet<String>,
) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    is_entry_pinning_sides(lhs, rhs, mutation_continued_params)
        || is_entry_pinning_sides(rhs, lhs, mutation_continued_params)
}

fn is_entry_pinning_sides(
    entry_side: &PureExpr,
    carrier_side: &PureExpr,
    mutation_continued_params: &HashSet<String>,
) -> bool {
    let parent_name = match entry_side {
        // `Deref(Var(parent))` shape — unnormalised.
        PureExpr::Deref(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => Some(name.clone()),
            _ => None,
        },
        // `Var("<parent>_current")` shape — normalised by the encoder-facing
        // pipeline.
        PureExpr::Var(name, _) => name
            .strip_suffix("_current")
            .map(|stripped| stripped.to_string()),
        _ => None,
    };
    let Some(parent_name) = parent_name else {
        return false;
    };
    if !mutation_continued_params.contains(&parent_name) {
        return false;
    }
    let PureExpr::Var(carrier_name, _) = carrier_side else {
        return false;
    };
    carrier_name.starts_with("$call_") || carrier_name.starts_with("$_call_")
}

/// Match the `*parent == ^child` shape emitted by
/// `build_delayed_writeback_assumptions` for two-phase reborrows where the
/// parent, or the root of its reborrow chain, is mutation-continued. The `^parent == ^child` propagation (also
/// emitted by the same builder when `child` is final) is consistent with the
/// call_assumption and is NOT matched here.
fn is_delayed_writeback_for_mutation_continued(
    expr: &PureExpr,
    mutation_continued_params: &HashSet<String>,
) -> bool {
    if mutation_continued_params.is_empty() {
        return false;
    }
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    let parent_name = match lhs.as_ref() {
        PureExpr::Deref(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => Some(name.clone()),
            _ => None,
        },
        _ => None,
    };
    let is_final_var = matches!(
        rhs.as_ref(),
        PureExpr::Final(inner) if matches!(inner.as_ref(), PureExpr::Var(_, _))
    );
    parent_name.is_some_and(|name| {
        is_final_var
            && (mutation_continued_params.contains(&name)
                || mutation_continued_params.contains(trust_wp_core::formula::reborrow_root(&name)))
    })
}

fn collect_closure_call_assumptions(preconditions: &[PureExpr]) -> Vec<PureExpr> {
    preconditions
        .iter()
        .filter(|expr| {
            matches!(
                expr,
                PureExpr::MethodCall { method, .. }
                    if method == "postcondition"
                        || method == "postcondition_mut"
                        || method == "postcondition_once"
            )
        })
        .cloned()
        .collect()
}

fn resolve_assumption_names(body: &MutBorrowBody) -> Option<Vec<String>> {
    body.resolve_results.as_ref().map(|resolve_results| {
        resolve_results
            .has_precise_resolve
            .iter()
            .filter(|(_, &has)| has)
            .map(|(name, _)| name.clone())
            .collect()
    })
}

fn immediate_prophecy_writebacks(body: &MutBorrowBody) -> Option<HashMap<String, String>> {
    let writebacks: HashMap<String, String> = body
        .resolve_results
        .as_ref()?
        .writebacks
        .iter()
        .filter(|writeback| writeback.activation.is_none())
        .map(|writeback| (writeback.child_name.clone(), writeback.parent_name.clone()))
        .collect();
    (!writebacks.is_empty()).then_some(writebacks)
}

fn synthesize_reborrow_carrier_final_declarations(
    final_values: &mut HashMap<String, PureExpr>,
    body: &MutBorrowBody,
    preconditions: &[PureExpr],
    ensures: &[PureExpr],
    return_expr: Option<&PureExpr>,
) {
    if body.borrow_id_origins.is_empty() {
        return;
    }

    let mut carrier_sorts = HashMap::new();
    collect_reborrow_carrier_sorts(preconditions, &body.borrow_id_origins, &mut carrier_sorts);
    collect_reborrow_carrier_sorts(ensures, &body.borrow_id_origins, &mut carrier_sorts);
    if let Some(return_expr) = return_expr {
        collect_reborrow_carrier_sorts(
            std::slice::from_ref(return_expr),
            &body.borrow_id_origins,
            &mut carrier_sorts,
        );
    }

    for (name, sort) in carrier_sorts {
        final_values
            .entry(name.clone())
            .or_insert_with(|| PureExpr::Final(Arc::new(PureExpr::Var(name, Some(sort)))));
    }
}

fn collect_reborrow_carrier_sorts(
    exprs: &[PureExpr],
    borrow_id_origins: &HashMap<String, BorrowIdOrigin>,
    carrier_sorts: &mut HashMap<String, ExprSort>,
) {
    for expr in exprs {
        expr.for_each_recursive(|node| {
            let PureExpr::Var(name, Some(sort @ ExprSort::MutRef(_))) = node else {
                return;
            };
            if borrow_id_origins.contains_key(name) {
                carrier_sorts
                    .entry(name.clone())
                    .or_insert_with(|| sort.clone());
            }
        });
    }
}

fn has_direct_fresh_reborrow_parent_equality(body: &MutBorrowBody, ensures: &[PureExpr]) -> bool {
    ensures.iter().any(|ensure| {
        let PureExpr::BinOp(left, BinOp::Eq, right) = ensure else {
            return false;
        };
        let Some(left_name) = var_name(left) else {
            return false;
        };
        let Some(right_name) = var_name(right) else {
            return false;
        };
        is_fresh_child_parent_pair(&body.borrow_id_origins, left_name, right_name)
            || is_fresh_child_parent_pair(&body.borrow_id_origins, right_name, left_name)
    })
}

fn var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        _ => None,
    }
}

fn is_fresh_child_parent_pair(
    borrow_id_origins: &HashMap<String, BorrowIdOrigin>,
    child_name: &str,
    parent_name: &str,
) -> bool {
    matches!(
        borrow_id_origins.get(child_name),
        Some(BorrowIdOrigin::Fresh { parent }) if parent == parent_name
    )
}

#[cfg(test)]
fn proof_assert_goals_directly_assumed(preconditions: &[PureExpr], ensures: &[PureExpr]) -> bool {
    !ensures.is_empty()
        && ensures
            .iter()
            .all(|ensure| proof_assert_goal_directly_assumed(preconditions, ensure))
}

#[cfg(test)]
fn proof_assert_goal_directly_assumed(preconditions: &[PureExpr], ensure: &PureExpr) -> bool {
    preconditions.iter().any(|pre| expr_matches(pre, ensure))
        || positive_scaled_term_goal_supported(preconditions, ensure)
}

#[cfg(test)]
fn positive_scaled_term_goal_supported(preconditions: &[PureExpr], ensure: &PureExpr) -> bool {
    let Some((term, scale)) = positive_scaled_gt_zero_goal(ensure) else {
        return false;
    };
    if scale <= 0 {
        return false;
    }
    preconditions.iter().any(|pre| term_gt_zero_fact(pre, term))
        || type_invariant_implies_positive_len(preconditions, term)
}

#[cfg(test)]
fn positive_scaled_gt_zero_goal(expr: &PureExpr) -> Option<(&PureExpr, i64)> {
    let PureExpr::BinOp(lhs, BinOp::Lt, rhs) = expr else {
        return None;
    };
    if !matches!(lhs.as_ref(), PureExpr::Int(0)) {
        return None;
    }
    match rhs.as_ref() {
        PureExpr::BinOp(left, BinOp::Mul, right) => {
            if let PureExpr::Int(value) = right.as_ref() {
                Some((left.as_ref(), *value))
            } else if let PureExpr::Int(value) = left.as_ref() {
                Some((right.as_ref(), *value))
            } else {
                None
            }
        }
        _ => None,
    }
}

#[cfg(test)]
fn term_gt_zero_fact(fact: &PureExpr, term: &PureExpr) -> bool {
    match fact {
        PureExpr::BinOp(lhs, BinOp::Lt, rhs) => {
            matches!(lhs.as_ref(), PureExpr::Int(0)) && proof_expr_equiv(rhs, term)
        }
        PureExpr::BinOp(lhs, BinOp::Gt, rhs) => {
            proof_expr_equiv(lhs, term) && matches!(rhs.as_ref(), PureExpr::Int(0))
        }
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            term_gt_zero_fact(lhs, term) || term_gt_zero_fact(rhs, term)
        }
        _ => false,
    }
}

#[cfg(test)]
fn type_invariant_implies_positive_len(preconditions: &[PureExpr], term: &PureExpr) -> bool {
    let Some(root) = len_of_first_field_root(term) else {
        return false;
    };
    preconditions.iter().any(|pre| {
        matches!(
            pre,
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } if args.is_empty()
                && method.contains("__trust_wp_invariant")
                && deref_root_var(receiver).is_some_and(|candidate| candidate == root)
        )
    })
}

#[cfg(test)]
fn len_of_first_field_root(expr: &PureExpr) -> Option<&str> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if method != "len" || !args.is_empty() {
        return None;
    }
    let PureExpr::View(view_inner) = receiver.as_ref() else {
        return None;
    };
    let PureExpr::LogicFnCall { name, args } = view_inner.as_ref() else {
        return None;
    };
    if name != "__trust_wp_tuple_get_0" {
        return None;
    }
    match args.as_slice() {
        [PureExpr::Var(root, _)] => Some(root.as_str()),
        _ => None,
    }
}

#[cfg(test)]
fn deref_root_var(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Deref(inner) => deref_root_var(inner),
        PureExpr::Var(name, _) => Some(name.as_str()),
        _ => None,
    }
}

fn synthesize_post_loop_match_exit_goals(
    preconditions: &mut Vec<PureExpr>,
    ensures: &[PureExpr],
    logic_fns: &[LogicFnDef],
    cons_discriminant: &dyn Fn(&LogicFnDef) -> Option<i64>,
) -> usize {
    let mut synthesized = Vec::new();
    for ensure in ensures {
        let supported = post_loop_match_exit_goal_is_supported(
            ensure,
            preconditions,
            logic_fns,
            cons_discriminant,
        );
        if supported
            && !preconditions.iter().any(|pre| expr_matches(pre, ensure))
            && !synthesized.iter().any(|pre| expr_matches(pre, ensure))
        {
            synthesized.push(ensure.clone());
        }
    }
    let count = synthesized.len();
    // fact-source: match_exit_goals
    preconditions.extend(synthesized);
    count
}

fn post_loop_match_exit_goal_is_supported(
    ensure: &PureExpr,
    preconditions: &[PureExpr],
    logic_fns: &[LogicFnDef],
    cons_discriminant: &dyn Fn(&LogicFnDef) -> Option<i64>,
) -> bool {
    let Some(goal) = forall_implication_equality(ensure) else {
        return false;
    };

    preconditions.iter().any(|candidate| {
        let Some(invariant) = forall_implication_equality(candidate) else {
            return false;
        };
        if invariant.var != goal.var
            || invariant.var_sort != goal.var_sort
            || !proof_expr_equiv(invariant.antecedent, goal.antecedent)
        {
            return false;
        }
        let Some(match_info) = match_invariant_none_branch_for_goal(&invariant, &goal) else {
            return false;
        };
        // The exit fact says the receiver is `Nil` only for the discriminant
        // its enum gives `Cons` (D-237).
        crate::callbacks::list_match_exit::list_exit_discriminant(
            logic_fns,
            match_info.method,
            list_get_definition_has_nil_none_cons_recursive,
            cons_discriminant,
        )
        .is_some_and(|cons| has_completed_list_cons_exit(preconditions, match_info.receiver, cons))
    })
}

#[derive(Clone, Copy)]
struct ForallImplicationEquality<'a> {
    var: &'a str,
    var_sort: &'a Option<ExprSort>,
    antecedent: &'a PureExpr,
    lhs: &'a PureExpr,
    rhs: &'a PureExpr,
}

fn forall_implication_equality(expr: &PureExpr) -> Option<ForallImplicationEquality<'_>> {
    let PureExpr::Forall {
        var,
        var_sort,
        body,
        ..
    } = expr
    else {
        return None;
    };
    let PureExpr::BinOp(antecedent, BinOp::Implies, consequent) = body.as_ref() else {
        return None;
    };
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = consequent.as_ref() else {
        return None;
    };
    Some(ForallImplicationEquality {
        var,
        var_sort,
        antecedent,
        lhs,
        rhs,
    })
}

struct MatchExitInfo<'a> {
    receiver: &'a PureExpr,
    method: &'a str,
}

fn match_invariant_none_branch_for_goal<'a>(
    invariant: &'a ForallImplicationEquality<'a>,
    goal: &ForallImplicationEquality<'_>,
) -> Option<MatchExitInfo<'a>> {
    if proof_expr_equiv(invariant.lhs, goal.lhs) {
        if let Some(info) =
            option_identity_match_none_branch(invariant.rhs, goal.rhs, invariant.var)
        {
            return Some(info);
        }
    }
    if proof_expr_equiv(invariant.rhs, goal.rhs) {
        if let Some(info) =
            option_identity_match_none_branch(invariant.lhs, goal.lhs, invariant.var)
        {
            return Some(info);
        }
    }
    if proof_expr_equiv(invariant.lhs, goal.rhs) {
        if let Some(info) =
            option_identity_match_none_branch(invariant.rhs, goal.lhs, invariant.var)
        {
            return Some(info);
        }
    }
    if proof_expr_equiv(invariant.rhs, goal.lhs) {
        option_identity_match_none_branch(invariant.lhs, goal.rhs, invariant.var)
    } else {
        None
    }
}

fn option_identity_match_none_branch<'a>(
    match_expr: &'a PureExpr,
    expected_none_body: &PureExpr,
    quantified_var: &str,
) -> Option<MatchExitInfo<'a>> {
    let PureExpr::Match { scrutinee, arms } = match_expr else {
        return None;
    };
    let (receiver, method, args) = logic_or_method_call(scrutinee.as_ref())?;
    if method != "get" || args.len() != 1 || !is_var_named_loose(&args[0], quantified_var) {
        return None;
    }

    let mut saw_none = false;
    let mut saw_some_identity = false;
    for arm in arms {
        match &arm.pattern {
            Pattern::Constructor { name, inner }
                if short_constructor_name(name) == "None" && inner.is_none() =>
            {
                if !proof_expr_equiv(&arm.body, expected_none_body) {
                    return None;
                }
                saw_none = true;
            }
            Pattern::Constructor {
                name,
                inner: Some(inner),
            } if short_constructor_name(name) == "Some" => {
                let Pattern::Binding(binding) = inner.as_ref() else {
                    return None;
                };
                if !is_some_constructor_of_var(&arm.body, binding) {
                    return None;
                }
                saw_some_identity = true;
            }
            _ => return None,
        }
    }

    (saw_none && saw_some_identity).then_some(MatchExitInfo { receiver, method })
}

fn logic_or_method_call(expr: &PureExpr) -> Option<(&PureExpr, &str, &[PureExpr])> {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => Some((receiver.as_ref(), method.as_str(), args.as_slice())),
        PureExpr::LogicFnCall { name, args } if args.len() >= 2 => {
            Some((&args[0], name.as_str(), &args[1..]))
        }
        _ => None,
    }
}

fn has_completed_list_cons_exit(
    preconditions: &[PureExpr],
    receiver: &PureExpr,
    cons_discriminant: i64,
) -> bool {
    preconditions
        .iter()
        .any(|pre| is_not_discriminant_value(pre, receiver, cons_discriminant))
}

fn is_not_discriminant_value(expr: &PureExpr, receiver: &PureExpr, discriminant: i64) -> bool {
    match expr {
        PureExpr::UnOp(UnOp::Not, inner) => is_discriminant_equality(inner, receiver, discriminant),
        PureExpr::BinOp(lhs, BinOp::Ne, rhs) => {
            discriminant_call_matches(lhs, receiver, discriminant, rhs)
                || discriminant_call_matches(rhs, receiver, discriminant, lhs)
        }
        _ => false,
    }
}

fn is_discriminant_equality(expr: &PureExpr, receiver: &PureExpr, discriminant: i64) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    discriminant_call_matches(lhs, receiver, discriminant, rhs)
        || discriminant_call_matches(rhs, receiver, discriminant, lhs)
}

fn discriminant_call_matches(
    maybe_call: &PureExpr,
    receiver: &PureExpr,
    discriminant: i64,
    maybe_value: &PureExpr,
) -> bool {
    matches!(maybe_value, PureExpr::Int(value) if *value == discriminant)
        && matches!(
            maybe_call,
            PureExpr::MethodCall {
                receiver: call_receiver,
                method,
                args,
            } if method == "discriminant" && args.is_empty() && proof_expr_equiv(call_receiver, receiver)
        )
}

fn list_get_definition_has_nil_none_cons_recursive(def: &LogicFnDef) -> bool {
    if !def.is_recursive() || !def.requires().is_empty() {
        return false;
    }
    let Some(self_param) = def.params().first() else {
        return false;
    };
    let PureExpr::Match { scrutinee, arms } = def.body() else {
        return false;
    };
    if !matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == self_param) {
        return false;
    }
    if arms.len() != 2 {
        return false;
    }

    let mut saw_nil_none = false;
    let mut saw_cons = false;
    for arm in arms {
        let Pattern::Constructor { name, .. } = &arm.pattern else {
            return false;
        };
        match short_constructor_name(name) {
            "Nil" => {
                if !is_none_constructor(&arm.body) {
                    return false;
                }
                saw_nil_none = true;
            }
            "Cons" => saw_cons = true,
            _ => return false,
        }
    }
    saw_nil_none && saw_cons
}

fn short_constructor_name(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

fn is_none_constructor(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(name, _) => short_constructor_name(name) == "None",
        PureExpr::LogicFnCall { name, args } => {
            args.is_empty() && short_constructor_name(name) == "None"
        }
        _ => false,
    }
}

fn is_some_constructor_of_var(expr: &PureExpr, var: &str) -> bool {
    matches!(
        expr,
        PureExpr::LogicFnCall { name, args }
            if short_constructor_name(name) == "Some"
                && matches!(args.as_slice(), [arg] if is_var_named_loose(arg, var))
    )
}

fn is_var_named_loose(expr: &PureExpr, expected: &str) -> bool {
    match expr {
        PureExpr::Var(name, _) => name == expected,
        PureExpr::View(inner) => is_var_named_loose(inner, expected),
        _ => false,
    }
}

fn proof_expr_equiv(lhs: &PureExpr, rhs: &PureExpr) -> bool {
    if lhs == rhs {
        return true;
    }
    match (lhs, rhs) {
        (PureExpr::Var(lhs_name, _), PureExpr::Var(rhs_name, _)) => lhs_name == rhs_name,
        (PureExpr::View(inner), PureExpr::Var(name, _))
        | (PureExpr::Var(name, _), PureExpr::View(inner)) => is_var_named_loose(inner, name),
        (PureExpr::View(lhs_inner), PureExpr::View(rhs_inner))
        | (PureExpr::Old(lhs_inner), PureExpr::Old(rhs_inner))
        | (PureExpr::Deref(lhs_inner), PureExpr::Deref(rhs_inner))
        | (PureExpr::Final(lhs_inner), PureExpr::Final(rhs_inner)) => {
            proof_expr_equiv(lhs_inner, rhs_inner)
        }
        (PureExpr::BinOp(lhs_l, lhs_op, lhs_r), PureExpr::BinOp(rhs_l, rhs_op, rhs_r)) => {
            lhs_op == rhs_op && proof_expr_equiv(lhs_l, rhs_l) && proof_expr_equiv(lhs_r, rhs_r)
        }
        (PureExpr::UnOp(lhs_op, lhs_inner), PureExpr::UnOp(rhs_op, rhs_inner)) => {
            lhs_op == rhs_op && proof_expr_equiv(lhs_inner, rhs_inner)
        }
        (
            PureExpr::MethodCall {
                receiver: lhs_receiver,
                method: lhs_method,
                args: lhs_args,
            },
            PureExpr::MethodCall {
                receiver: rhs_receiver,
                method: rhs_method,
                args: rhs_args,
            },
        ) => {
            lhs_method == rhs_method
                && proof_expr_equiv(lhs_receiver, rhs_receiver)
                && expr_slices_equiv(lhs_args, rhs_args)
        }
        (
            PureExpr::LogicFnCall {
                name: lhs_name,
                args: lhs_args,
            },
            PureExpr::LogicFnCall {
                name: rhs_name,
                args: rhs_args,
            },
        ) => {
            // Two logic functions that share a last path segment are two
            // functions (D-237).
            lhs_name == rhs_name && expr_slices_equiv(lhs_args, rhs_args)
        }
        (
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            },
            PureExpr::LogicFnCall {
                name,
                args: logic_args,
            },
        )
        | (
            PureExpr::LogicFnCall {
                name,
                args: logic_args,
            },
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            },
        ) => {
            short_constructor_name(name) == method
                && logic_args
                    .split_first()
                    .is_some_and(|(logic_receiver, logic_tail)| {
                        proof_expr_equiv(receiver, logic_receiver)
                            && expr_slices_equiv(args, logic_tail)
                    })
        }
        _ => false,
    }
}

fn expr_slices_equiv(lhs: &[PureExpr], rhs: &[PureExpr]) -> bool {
    lhs.len() == rhs.len()
        && lhs
            .iter()
            .zip(rhs)
            .all(|(lhs, rhs)| proof_expr_equiv(lhs, rhs))
}

fn expr_matches(lhs: &PureExpr, rhs: &PureExpr) -> bool {
    lhs == rhs || symmetric_equality_matches(lhs, rhs)
}

fn symmetric_equality_matches(lhs: &PureExpr, rhs: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs_left, BinOp::Eq, lhs_right) = lhs else {
        return false;
    };
    let PureExpr::BinOp(rhs_left, BinOp::Eq, rhs_right) = rhs else {
        return false;
    };
    lhs_left.as_ref() == rhs_right.as_ref() && lhs_right.as_ref() == rhs_left.as_ref()
}

fn is_stale_mutation_alias_fact(expr: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    is_self_final_alias(lhs, rhs) || is_self_final_alias(rhs, lhs)
}

fn is_stale_closure_capture_env_fact(expr: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return false;
    };
    is_stale_double_final_capture_alias(lhs, rhs) || is_stale_double_final_capture_alias(rhs, lhs)
}

fn is_stale_double_final_capture_alias(capture_candidate: &PureExpr, rhs: &PureExpr) -> bool {
    let PureExpr::Var(_, _) = capture_candidate else {
        return false;
    };
    let PureExpr::LogicFnCall { name, args } = rhs else {
        return false;
    };
    if name != "__trust_wp_tuple1" {
        return false;
    }
    args.iter().any(contains_nested_final)
}

fn contains_nested_final(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Final(inner) => {
            matches!(inner.as_ref(), PureExpr::Final(_)) || contains_nested_final(inner)
        }
        PureExpr::BinOp(lhs, _, rhs) => contains_nested_final(lhs) || contains_nested_final(rhs),
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::View(inner) => contains_nested_final(inner),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            contains_nested_final(cond)
                || contains_nested_final(then_expr)
                || contains_nested_final(else_expr)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            triggers.iter().flatten().any(contains_nested_final) || contains_nested_final(body)
        }
        PureExpr::Match { scrutinee, arms } => {
            contains_nested_final(scrutinee)
                || arms.iter().any(|arm| contains_nested_final(&arm.body))
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            contains_nested_final(receiver) || args.iter().any(contains_nested_final)
        }
        PureExpr::Closure { body, .. } => contains_nested_final(body),
        PureExpr::Let { value, body, .. } => {
            contains_nested_final(value) || contains_nested_final(body)
        }
        PureExpr::LetAssume { assumption, body } => {
            contains_nested_final(assumption) || contains_nested_final(body)
        }
        PureExpr::LetObligation { obligation, body } => {
            contains_nested_final(obligation) || contains_nested_final(body)
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => false,
        #[allow(unreachable_patterns)]
        _ => false,
    }
}

fn is_self_final_alias(pre: &PureExpr, post: &PureExpr) -> bool {
    let PureExpr::Var(pre_name, _) = pre else {
        return false;
    };
    let PureExpr::Final(inner) = post else {
        return false;
    };
    matches!(inner.as_ref(), PureExpr::Var(post_name, _) if post_name == pre_name)
}

fn collect_proof_assert_mutation_continued_vars(preconditions: &[PureExpr]) -> HashSet<String> {
    let mut mutation_continued = HashSet::new();
    for expr in preconditions {
        if let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr {
            collect_non_identity_final_eq(lhs, rhs, &mut mutation_continued);
            collect_non_identity_final_eq(rhs, lhs, &mut mutation_continued);
        }
        // Also collect base variables of (possibly nested) `Final` chains
        // appearing anywhere in the fact — e.g. `call_9 == (^call_1).len()`
        // or `set == ^^^call_1`. Ghost-collection helper postconditions
        // (insert_ghost/remove_ghost) reference multi-step prophecy states
        // `^call_1`, `^^call_1`, ... of a ghost local without ever producing
        // a top-level `Final(x) == rhs` equality, so the equality scan above
        // misses them. Without the mutation-continued marking, the final
        // values map stays empty, `preserve_temporal_wrappers_for_mut_borrow`
        // never strips the datatype annotation, and the encoder's
        // plain-datatype `Final` collapse (#2675, #2700) folds `^call_1` into
        // `call_1` — turning `(^self).len() == self.len() + 1` facts into the
        // self-contradiction `len(call_1) == len(call_1) + 1` (base premises
        // UNSAT → vacuity guard → Unknown). (#2712, ghost_set regression)
        let mut bound = Vec::new();
        collect_final_chain_carrier_vars(expr, &mut bound, &mut mutation_continued);
    }
    mutation_continued
}

/// Collect base variable names of `Final`-wrapped chains (`^x`, `^^x`, ...,
/// also through `View`) anywhere inside `expr`, skipping quantifier-bound
/// variables. Marking such a variable as mutation-continued only *removes*
/// assumed identities (`x_final == x`) — a strictly weaker assumption set —
/// so this is sound; it never adds facts.
fn collect_final_chain_carrier_vars(
    expr: &PureExpr,
    bound: &mut Vec<String>,
    out: &mut HashSet<String>,
) {
    match expr {
        PureExpr::Final(inner) => {
            if let Some(name) = final_chain_base_var_name(inner) {
                if !bound.iter().any(|b| b == &name) {
                    out.insert(name);
                }
            }
            collect_final_chain_carrier_vars(inner, bound, out);
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::View(inner) => collect_final_chain_carrier_vars(inner, bound, out),
        PureExpr::BinOp(lhs, _, rhs) => {
            collect_final_chain_carrier_vars(lhs, bound, out);
            collect_final_chain_carrier_vars(rhs, bound, out);
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_final_chain_carrier_vars(cond, bound, out);
            collect_final_chain_carrier_vars(then_expr, bound, out);
            collect_final_chain_carrier_vars(else_expr, bound, out);
        }
        PureExpr::Forall {
            var,
            body,
            triggers,
            ..
        }
        | PureExpr::Exists {
            var,
            body,
            triggers,
            ..
        } => {
            bound.push(var.clone());
            for trigger_expr in triggers.iter().flatten() {
                collect_final_chain_carrier_vars(trigger_expr, bound, out);
            }
            collect_final_chain_carrier_vars(body, bound, out);
            bound.pop();
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_final_chain_carrier_vars(scrutinee, bound, out);
            for arm in arms {
                collect_final_chain_carrier_vars(&arm.body, bound, out);
            }
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            collect_final_chain_carrier_vars(receiver, bound, out);
            for arg in args {
                collect_final_chain_carrier_vars(arg, bound, out);
            }
        }
        PureExpr::LogicFnCall { args, .. } => {
            for arg in args {
                collect_final_chain_carrier_vars(arg, bound, out);
            }
        }
        PureExpr::Let { var, value, body } => {
            collect_final_chain_carrier_vars(value, bound, out);
            bound.push(var.clone());
            collect_final_chain_carrier_vars(body, bound, out);
            bound.pop();
        }
        PureExpr::LetAssume { assumption, body } => {
            collect_final_chain_carrier_vars(assumption, bound, out);
            collect_final_chain_carrier_vars(body, bound, out);
        }
        PureExpr::LetObligation { obligation, body } => {
            collect_final_chain_carrier_vars(obligation, bound, out);
            collect_final_chain_carrier_vars(body, bound, out);
        }
        PureExpr::Closure { params, body } => {
            let added = params.len();
            bound.extend(params.iter().map(|(name, _)| name.clone()));
            collect_final_chain_carrier_vars(body, bound, out);
            bound.truncate(bound.len() - added);
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {}
        #[allow(unreachable_patterns)]
        _ => {}
    }
}

/// Resolve the base variable of a `Final` chain body: digs through nested
/// `Final` / `View` wrappers to a `Var` and returns its normalized name.
fn final_chain_base_var_name(expr: &PureExpr) -> Option<String> {
    match expr {
        PureExpr::Var(name, _) => Some(normalize_wrapped_var_name(name)),
        PureExpr::Final(inner) | PureExpr::View(inner) => final_chain_base_var_name(inner),
        _ => None,
    }
}

fn collect_non_identity_final_eq(
    final_side: &PureExpr,
    other_side: &PureExpr,
    mutation_continued: &mut HashSet<String>,
) {
    let Some(name) = wrapped_final_var_name(final_side) else {
        return;
    };
    if wrapped_var_name(other_side).as_deref() == Some(&name) {
        return;
    }
    mutation_continued.insert(name);
}

fn synthesize_proof_assert_final_values(
    has_mutating_call_effect: bool,
    ensures: &[PureExpr],
    call_assumptions: &[PureExpr],
    call_effect_expr: Option<&PureExpr>,
    mutation_continued: &HashSet<String>,
) -> Option<HashMap<String, PureExpr>> {
    let mut synthesized_final_values = if has_mutating_call_effect {
        HashMap::new()
    } else {
        synthesize_identity_final_values_with_expr(
            false,
            ensures,
            call_assumptions,
            call_effect_expr,
        )
        .unwrap_or_default()
    };
    for name in mutation_continued {
        synthesized_final_values
            .entry(name.clone())
            .or_insert_with(|| PureExpr::Var(name.clone(), None));
    }
    if synthesized_final_values.is_empty() && !has_mutating_call_effect {
        None
    } else {
        Some(synthesized_final_values)
    }
}

fn wrapped_final_var_name(expr: &PureExpr) -> Option<String> {
    match expr {
        PureExpr::Final(inner) => wrapped_var_name(inner),
        PureExpr::View(inner) => wrapped_final_var_name(inner),
        PureExpr::Var(name, _) if is_derived_final_name(name) => {
            Some(normalize_wrapped_var_name(name))
        }
        _ => None,
    }
}

fn wrapped_var_name(expr: &PureExpr) -> Option<String> {
    match expr {
        PureExpr::Var(name, _) => Some(normalize_wrapped_var_name(name)),
        PureExpr::View(inner) => wrapped_var_name(inner),
        _ => None,
    }
}

fn is_derived_final_name(name: &str) -> bool {
    name.starts_with("final_") || name.ends_with("_final")
}

fn normalize_wrapped_var_name(name: &str) -> String {
    let mut normalized = name;
    loop {
        if let Some(stripped) = normalized.strip_prefix("final_") {
            normalized = stripped;
            continue;
        }
        if let Some(stripped) = normalized.strip_suffix("_view") {
            normalized = stripped;
            continue;
        }
        if let Some(stripped) = normalized.strip_suffix("_current") {
            normalized = stripped;
            continue;
        }
        if let Some(stripped) = normalized.strip_suffix("_final") {
            normalized = stripped;
            continue;
        }
        break;
    }
    normalized.to_string()
}

/// Extend preconditions with loop-exit and post-loop assumptions (contracted host only).
///
/// A loop-exit fact holds of the names at the loop's exit, and it is read at
/// the assertion through the assertion's substitution. A parameter in
/// `rebound` may have been re-bound since, which would make the fact a premise
/// about its new binding (an entry precondition the loop lane carried across
/// the loop, read after drop glue wrote the parameter: `after_loop` in
/// proof_assert_entry_requires_pins_param_after_drop_glue.rs), so the facts
/// naming one are withdrawn (D-140).
fn extend_with_loop_assumptions(
    preconditions: &mut Vec<PureExpr>,
    pa_span: rustc_span::Span,
    loop_spans: &[(u32, u32)],
    loop_exit_assumptions: Option<&[PureExpr]>,
    snapshot: &AssertionSnapshot,
    rebound: &crate::mir_analysis::InvalidatedEntryNames,
    verbose: bool,
) {
    // Inject loop-exit assumptions for proof_asserts after all loops, only
    // where every path to the assertion left each loop through its exit arm,
    // and never over a name written since or bound to two locals (D-189).
    let Some(stale) = snapshot.exit_fact_stale_names.as_ref() else {
        return;
    };
    if super::proof_assert_loop_assumptions::proof_assert_after_all_loops(pa_span, loop_spans) {
        if let Some(assumptions) = loop_exit_assumptions {
            let mut assumptions: Vec<PureExpr> = assumptions
                .iter()
                .filter(|fact| !fact.free_vars().iter().any(|name| stale.contains(name)))
                .cloned()
                .collect();
            super::super::proof_assert_verify::drop_stale_param_facts(&mut assumptions, rebound);
            for assumption in
                super::proof_assert_loop_assumptions::rewrite_post_loop_proof_assert_assumptions(
                    &assumptions,
                    &snapshot.substitutions,
                )
            {
                if !preconditions.contains(&assumption) {
                    // fact-source: loop_lane_exit_facts
                    preconditions.push(assumption);
                }
            }
        }
    }

    if verbose && !snapshot.post_loop_assumptions.is_empty() {
        debug!(
            "trust-wp:   (proof_assert: {} closure-local post-loop assumption(s) prepared)",
            snapshot.post_loop_assumptions.len()
        );
    }
}

/// Verbose ghost-context logging (contractless host only in the old code;
/// now available for both hosts via the driver).
fn log_ghost_context(tcx: TyCtxt<'_>, host: &ProofAssertHost<'_>, ghost_context: &[PureExpr]) {
    let fn_path = tcx.def_path_str(host.contract().def_id);
    debug!(
        "trust-wp:   (proof_assert in {fn_path}: ghost_context={})",
        ghost_context.len(),
    );
    for (i, gc) in ghost_context.iter().enumerate() {
        debug!("trust-wp:     ghost_context[{i}]: {gc}");
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, sync::Arc};

    use trust_wp_core::formula::ExprSort;

    use super::{
        collect_proof_assert_mutation_continued_vars, is_delayed_writeback_for_mutation_continued,
        proof_assert_goals_directly_assumed, BinOp, PureExpr,
    };

    /// The post-loop match-exit lane: a loop invariant `forall i. A ==> m.at(i)
    /// == match l.get(i) { None => d, Some(v) => Some(v) }` and the exit fact
    /// `discriminant(l) != K` make the goal `forall i. A ==> m.at(i) == d` a
    /// premise, where `K` must say `l` is not `Cons` (D-237).
    mod match_exit {
        use std::sync::Arc;

        use trust_wp_core::{
            formula::{ExprSort, MatchArm, Pattern},
            logic::LogicFnDef,
        };

        use super::{
            super::{proof_expr_equiv, synthesize_post_loop_match_exit_goals},
            BinOp, PureExpr,
        };

        fn var(name: &str) -> PureExpr {
            PureExpr::Var(name.to_string(), None)
        }

        fn method(receiver: PureExpr, name: &str, args: Vec<PureExpr>) -> PureExpr {
            PureExpr::MethodCall {
                receiver: Arc::new(receiver),
                method: name.to_string(),
                args,
            }
        }

        fn bin(lhs: PureExpr, op: BinOp, rhs: PureExpr) -> PureExpr {
            PureExpr::BinOp(Arc::new(lhs), op, Arc::new(rhs))
        }

        fn forall_eq(rhs: PureExpr) -> PureExpr {
            PureExpr::Forall {
                var: "i".to_string(),
                var_sort: Some(ExprSort::Int),
                body: Arc::new(bin(
                    bin(PureExpr::Int(0), BinOp::Le, var("i")),
                    BinOp::Implies,
                    bin(method(var("m"), "at", vec![var("i")]), BinOp::Eq, rhs),
                )),
                triggers: vec![],
            }
        }

        fn list_get() -> LogicFnDef {
            let body = PureExpr::Match {
                scrutinee: Arc::new(var("self")),
                arms: vec![
                    MatchArm {
                        pattern: Pattern::Constructor {
                            name: "L::Nil".to_string(),
                            inner: None,
                        },
                        body: var("None"),
                    },
                    MatchArm {
                        pattern: Pattern::Constructor {
                            name: "L::Cons".to_string(),
                            inner: Some(Box::new(Pattern::Wildcard)),
                        },
                        body: method(var("self"), "get", vec![var("i")]),
                    },
                ],
            };
            let mut def = LogicFnDef::new(
                "get".to_string(),
                "crate::L::get".to_string(),
                vec!["self".to_string(), "i".to_string()],
                body,
            );
            def.set_is_recursive(true);
            def
        }

        fn premises() -> Vec<PureExpr> {
            let invariant = forall_eq(PureExpr::Match {
                scrutinee: Arc::new(method(var("l"), "get", vec![var("i")])),
                arms: vec![
                    MatchArm {
                        pattern: Pattern::Constructor {
                            name: "None".to_string(),
                            inner: None,
                        },
                        body: var("d"),
                    },
                    MatchArm {
                        pattern: Pattern::Constructor {
                            name: "Some".to_string(),
                            inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                        },
                        body: PureExpr::LogicFnCall {
                            name: "Some".to_string(),
                            args: vec![var("v")],
                        },
                    },
                ],
            });
            let exited = bin(
                method(var("l"), "discriminant", vec![]),
                BinOp::Ne,
                PureExpr::Int(1),
            );
            vec![invariant, exited]
        }

        fn synthesized(cons: Option<i64>, logic_fns: &[LogicFnDef]) -> usize {
            let mut preconditions = premises();
            synthesize_post_loop_match_exit_goals(
                &mut preconditions,
                &[forall_eq(var("d"))],
                logic_fns,
                &|_| cons,
            )
        }

        #[test]
        fn the_exit_fact_reads_as_nil_where_one_is_the_cons_discriminant() {
            assert_eq!(synthesized(Some(1), &[list_get()]), 1);
        }

        /// `enum L { Cons(..), Nil }`: `discriminant(l) != 1` says `l` is a
        /// `Cons`, whose `get` is not `None`. The lane took `1` for `Cons`
        /// whatever the enum said and stated the goal.
        #[test]
        fn the_exit_fact_is_not_read_as_nil_where_cons_is_the_first_variant() {
            assert_eq!(synthesized(Some(0), &[list_get()]), 0);
        }

        #[test]
        fn an_enum_that_cannot_be_named_states_nothing() {
            assert_eq!(synthesized(None, &[list_get()]), 0);
        }

        /// A user logic function named `discriminant` is spelled as the MIR
        /// discriminant read is, so its calls say nothing about the variant.
        #[test]
        fn a_logic_fn_named_discriminant_states_nothing() {
            let user = LogicFnDef::new(
                "discriminant".to_string(),
                "crate::L::discriminant".to_string(),
                vec!["self".to_string()],
                PureExpr::Int(1),
            );
            assert_eq!(synthesized(Some(1), &[list_get(), user]), 0);
        }

        #[test]
        fn logic_fns_sharing_a_last_segment_are_not_one_function() {
            let call = |name: &str| PureExpr::LogicFnCall {
                name: name.to_string(),
                args: vec![var("x")],
            };
            assert!(!proof_expr_equiv(&call("a::f"), &call("b::f")));
            assert!(proof_expr_equiv(&call("a::f"), &call("a::f")));
        }
    }

    /// `keep(v, &mut *p)` before an assertion: the outer reborrow's
    /// `_current` is `p`'s entry value, so `*p$rb9 == ^p$rb9$rb8` of a
    /// mutation-continued `p` let `proof_assert!(*p == before)` hold of a
    /// callee that stores 7 through it (D-107).
    #[test]
    fn a_writeback_into_a_reborrow_of_a_mutation_continued_param_is_dropped() {
        let var = |name: &str| PureExpr::Var(name.to_string(), None);
        let writeback = |parent: PureExpr, child: &str| {
            PureExpr::BinOp(
                Arc::new(parent),
                BinOp::Eq,
                Arc::new(PureExpr::Final(Arc::new(var(child)))),
            )
        };
        let continued = HashSet::from(["p".to_string()]);
        assert!(is_delayed_writeback_for_mutation_continued(
            &writeback(PureExpr::Deref(Arc::new(var("p$rb9"))), "p$rb9$rb8"),
            &continued,
        ));
        assert!(!is_delayed_writeback_for_mutation_continued(
            &writeback(PureExpr::Final(Arc::new(var("p$rb9"))), "p$rb9$rb8"),
            &continued,
        ));
        assert!(!is_delayed_writeback_for_mutation_continued(
            &writeback(PureExpr::Deref(Arc::new(var("v$rb7"))), "v$rb7$rb6"),
            &continued,
        ));
    }

    fn seq_var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), Some(ExprSort::Seq))
    }

    fn int(n: i64) -> PureExpr {
        PureExpr::Int(n)
    }

    fn eq(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
    }

    fn final_expr(expr: PureExpr) -> PureExpr {
        PureExpr::Final(Arc::new(expr))
    }

    fn view_expr(expr: PureExpr) -> PureExpr {
        PureExpr::View(Arc::new(expr))
    }

    fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: method.to_string(),
            args,
        }
    }

    #[test]
    fn mutation_continued_collection_tracks_non_identity_final_equalities() {
        let preconditions = vec![eq(
            final_expr(seq_var("call_4")),
            method_call(seq_var("call_4"), "push_back", vec![int(30)]),
        )];

        let tracked = collect_proof_assert_mutation_continued_vars(&preconditions);

        assert_eq!(tracked, HashSet::from(["call_4".to_string()]));
    }

    #[test]
    fn mutation_continued_collection_tracks_derived_final_carrier_names() {
        let preconditions = vec![eq(
            view_expr(seq_var("final_call_4_view")),
            method_call(
                view_expr(seq_var("call_4_view")),
                "push_back",
                vec![int(30)],
            ),
        )];

        let tracked = collect_proof_assert_mutation_continued_vars(&preconditions);

        assert_eq!(tracked, HashSet::from(["call_4".to_string()]));
    }

    #[test]
    fn proof_assert_final_values_keep_mutation_continued_entries() {
        let mutation_continued = HashSet::from(["call_4".to_string()]);

        let final_values =
            super::synthesize_proof_assert_final_values(true, &[], &[], None, &mutation_continued)
                .expect(
                    "mutation-continued vars should keep the mut-borrow final-values map alive",
                );

        assert!(
            final_values.contains_key("call_4"),
            "mutation-continued vars should keep a caller-side final value binding alive"
        );
    }

    #[test]
    fn proof_assert_mutating_call_effect_keeps_empty_final_values_branch_alive() {
        let final_values =
            super::synthesize_proof_assert_final_values(true, &[], &[], None, &HashSet::new())
                .expect("mutating call effect should keep the mut-borrow branch alive");

        assert!(
            final_values.is_empty(),
            "mutating call effect without tracked continuation should keep an empty final-values map"
        );
    }

    #[test]
    fn merge_substitution_facts_drops_double_final_closure_capture_alias() {
        let stable_alias = eq(
            PureExpr::Var("stable".to_string(), None),
            final_expr(PureExpr::Var("stable".to_string(), None)),
        );
        let substitution_facts = vec![
            eq(PureExpr::Var("x".to_string(), None), int(10)),
            stable_alias.clone(),
            eq(
                PureExpr::Var("c".to_string(), None),
                PureExpr::LogicFnCall {
                    name: "__trust_wp_tuple1".to_string(),
                    args: vec![final_expr(final_expr(PureExpr::Var("x".to_string(), None)))],
                },
            ),
            eq(
                final_expr(PureExpr::Var("x".to_string(), None)),
                PureExpr::BinOp(
                    Arc::new(PureExpr::Var("x".to_string(), None)),
                    BinOp::Add,
                    Arc::new(int(1)),
                ),
            ),
        ];
        let mut ghost_context = Vec::new();

        super::merge_substitution_facts(&mut ghost_context, &substitution_facts, false);

        let rendered: Vec<String> = ghost_context.iter().map(ToString::to_string).collect();
        assert!(
            rendered.iter().any(|text| text.contains("x == 10")),
            "driver should preserve ordinary substitution facts: {rendered:?}"
        );
        assert!(
            rendered.iter().any(|text| text.contains("^x == (x + 1)")),
            "driver should preserve useful mutating-call facts: {rendered:?}"
        );
        assert!(
            ghost_context.contains(&stable_alias),
            "driver should preserve self-final aliases for non-mutating calls: {rendered:?}"
        );
        assert!(
            rendered
                .iter()
                .all(|text| !text.contains("c == __trust_wp_tuple1(^^x)")),
            "driver should drop the stale double-final closure capture alias from ghost context: {rendered:?}"
        );

        let mut mutating_ghost_context = Vec::new();
        super::merge_substitution_facts(&mut mutating_ghost_context, &substitution_facts, true);
        assert!(
            !mutating_ghost_context.contains(&stable_alias),
            "driver should drop self-final aliases when a real mutating call effect is present"
        );
    }

    #[test]
    fn direct_assumption_shortcut_accepts_exact_goal() {
        let goal = eq(seq_var("x_rb2"), seq_var("x"));

        assert!(proof_assert_goals_directly_assumed(
            std::slice::from_ref(&goal),
            std::slice::from_ref(&goal),
        ));
    }

    #[test]
    fn direct_assumption_shortcut_accepts_symmetric_equality() {
        let precondition = eq(seq_var("x_rb2"), seq_var("x"));
        let ensure = eq(seq_var("x"), seq_var("x_rb2"));

        assert!(proof_assert_goals_directly_assumed(
            &[precondition],
            &[ensure],
        ));
    }

    #[test]
    fn direct_assumption_shortcut_rejects_missing_goal() {
        let precondition = eq(seq_var("x_rb2"), seq_var("x"));
        let ensure = eq(seq_var("y_rb2"), seq_var("y"));

        assert!(!proof_assert_goals_directly_assumed(
            &[precondition],
            &[ensure],
        ));
    }

    // ── #prophecy-slots M6: proof_assert lane selection ─────────────────────

    /// ★PIN: the pre-M6 rule is preserved exactly. A body with no `&mut`
    /// parameter, no synthesized finals and no final values stays on the pure
    /// `VerificationRequest` lane — M6 must not move ordinary proof_asserts.
    #[test]
    fn plain_proof_assert_body_stays_off_the_mut_borrow_lane() {
        assert!(!super::proof_assert_uses_mut_borrow_lane(
            false, false, false, false
        ));
    }

    /// ★PIN: a proven caller-side expiry pin routes the obligation onto the
    /// mut-borrow lane. This is the M6 wiring: `bind_projected_final_values`
    /// runs only inside `apply_mut_borrow_base_assertions`, so a pin on the
    /// pure lane would be silently discarded at the request boundary — the
    /// ghost-cluster shape (`if let Some(x) = m.get_mut_ghost(..)`) has no
    /// `&mut` parameter and would otherwise never reach the encoder.
    #[test]
    fn a_projected_expiry_pin_routes_onto_the_mut_borrow_lane() {
        assert!(super::proof_assert_uses_mut_borrow_lane(
            false, false, false, true
        ));
    }

    /// ★PIN: each pre-existing reason still selects the lane on its own, so
    /// the M6 term is strictly additive.
    #[test]
    fn each_legacy_reason_still_selects_the_mut_borrow_lane() {
        assert!(super::proof_assert_uses_mut_borrow_lane(
            true, false, false, false
        ));
        assert!(super::proof_assert_uses_mut_borrow_lane(
            false, true, false, false
        ));
        assert!(super::proof_assert_uses_mut_borrow_lane(
            false, false, true, false
        ));
    }
}
