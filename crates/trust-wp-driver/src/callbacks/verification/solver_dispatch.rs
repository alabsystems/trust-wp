// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SMT solver dispatch and per-function solver context (#1526 Phase 5).
//!
//! Groups the solver parameter structs and the three-way dispatch logic
//! (`verify_function_with_modes_outcome` vs
//! `verify_mut_borrow_function_with_modes_outcome`)
//! into a single module.

use std::{
    collections::{HashMap, HashSet},
    time::Duration,
};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use tracing::trace;
use trust_wp_ay::{
    verify_function_with_modes_outcome, verify_mut_borrow_function_with_modes_outcome,
    EncodingError, MutBorrowRequest, UnknownReason, VerificationOutcome, VerificationRequest,
    VerificationResult,
};
use trust_wp_core::{
    closure::ClosureCaptureInfo,
    formula::PureExpr,
    logic::{AdtDecls, LogicMode, TypeInvariantDef},
    TrackLevel,
};
use trust_wp_driver::StdSpec;

use super::super::{
    super::{contracts::FunctionContract, ghost::GhostBlock},
    closure_enrichment::synthesized_final_values_from_current_closure,
    ghost_context::{build_ghost_context_for_function, collect_focus_var_names, GhostBuildContext},
    helpers::{
        diagnose_identity_final_value_synthesis_skip_with_expr,
        synthesize_identity_final_values_with_expr,
    },
};

/// Shared solver parameters for SMT dispatch (#1526 Phase 5).
///
/// Groups the 8 optional/configuration parameters that are identical across
/// all three dispatch branches, reducing `dispatch_smt_verification` to 6 args.
pub(super) struct SolverParams<'a> {
    pub(super) ghost_context_opt: Option<&'a [PureExpr]>,
    pub(super) logic_fns_opt: Option<&'a [trust_wp_core::logic::LogicFnDef]>,
    /// Paths of the logic functions whose postconditions nobody proved, so
    /// whose axioms neutralization WITHDREW from every downstream query. A
    /// model is only a counterexample if it is not standing on one of these.
    pub(super) unverified_axioms: &'a HashSet<String>,
    pub(super) mode_overrides_opt: Option<&'a [LogicMode]>,
    pub(super) type_invariants_opt: Option<&'a [TypeInvariantDef]>,
    pub(super) type_constants: Option<&'a HashMap<String, PureExpr>>,
    pub(super) closure_captures_opt: Option<&'a [ClosureCaptureInfo]>,
    pub(super) track_level: TrackLevel,
    pub(super) timeout: Option<Duration>,
    /// Per-ADT field range constraints for unsigned/signed integer fields (#2097).
    pub(super) adt_field_ranges: Option<trust_wp_core::logic::AdtFieldRanges>,
    /// Rustc-backed ADT declarations for native datatype registration. (#1982)
    pub(super) adt_decls: Option<AdtDecls>,
    /// Whether to use native BV theory for bitwise operations. (#2666)
    pub(super) bitwise_proof: bool,
}

/// Ghost context construction parameters (#2657).
///
/// Bundles the specification maps and ghost blocks that are constant across
/// a single per-function solver context build, keeping
/// `build_per_function_solver_context_with_captures` under clippy's
/// `too_many_arguments` threshold.
pub(super) struct GhostContextParams<'a, 'tcx> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) ghost_blocks: &'a [GhostBlock],
    pub(super) user_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) trait_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) extern_specs: &'a HashMap<String, StdSpec>,
}

/// Per-function solver context: owned data that feeds into `SolverParams` (#1526).
///
/// Collects the closure capture infos, ghost context assumptions, and synthesized
/// identity final values for a single function. These are all computed once per
/// function and consumed only by the solver dispatch.
pub(super) struct PerFunctionSolverContext {
    pub(super) closure_capture_infos: Vec<ClosureCaptureInfo>,
    pub(super) ghost_context: Vec<PureExpr>,
    pub(super) synthesized_final_values: Option<HashMap<String, PureExpr>>,
}

impl PerFunctionSolverContext {
    pub(super) fn ghost_context_opt(&self) -> Option<&[PureExpr]> {
        (!self.ghost_context.is_empty()).then_some(self.ghost_context.as_slice())
    }

    pub(super) fn closure_captures_opt(&self) -> Option<&[ClosureCaptureInfo]> {
        (!self.closure_capture_infos.is_empty()).then_some(self.closure_capture_infos.as_slice())
    }
}

/// Build the per-function solver context from pre-collected closure captures,
/// ghost context, and synthesized identity final values (#1526, #2151).
///
/// Closure capture infos are collected early (before enrichment) so that
/// synthesized ensures from body effect analysis can participate in
/// existential enrichment. The pre-collected captures are passed here to
/// avoid redundant MIR traversal.
pub(super) fn build_per_function_solver_context_with_captures(
    ghost_params: &GhostContextParams<'_, '_>,
    contract: &FunctionContract,
    parsed: &super::super::parsing::ParsedContract,
    effective_requires: &[PureExpr],
    effective_ensures: &[PureExpr],
    closure_capture_infos: Vec<ClosureCaptureInfo>,
) -> PerFunctionSolverContext {
    let tcx = ghost_params.tcx;
    let ghost_blocks = ghost_params.ghost_blocks;
    let user_specs = ghost_params.user_specs;
    let trait_specs = ghost_params.trait_specs;
    let extern_specs = ghost_params.extern_specs;

    if !closure_capture_infos.is_empty() {
        trace!(
            count = closure_capture_infos.len(),
            "closure capture info(s) for structural sort registration",
        );
        for ci in &closure_capture_infos {
            trace!(
                def_id = %ci.def_id(),
                param_name = ?ci.param_name(),
                captures = %ci.captures()
                    .iter()
                    .map(|field| field.name())
                    .collect::<Vec<_>>()
                    .join(", "),
                "closure capture detail",
            );
        }
    }

    // Synthesize identity final values for &mut params (#520, #530).
    let mut synthesized_final_values = synthesize_identity_final_values_with_expr(
        parsed.mut_borrow.mut_borrow_body.is_some(),
        effective_ensures,
        &parsed.call_assumptions,
        parsed.result_expr.as_ref(),
    );
    let closure_final_values =
        synthesized_final_values_from_current_closure(&closure_capture_infos);
    if !closure_final_values.is_empty() {
        synthesized_final_values
            .get_or_insert_with(HashMap::new)
            .extend(closure_final_values);
    }
    if synthesized_final_values.is_none() {
        if let Some(reason) = diagnose_identity_final_value_synthesis_skip_with_expr(
            parsed.mut_borrow.mut_borrow_body.is_some(),
            effective_ensures,
            &parsed.call_assumptions,
            parsed.result_expr.as_ref(),
        ) {
            trace!(?reason, "identity final value synthesis skipped");
        }
    }

    // Build ghost context for function (#1572).
    let ghost_build_ctx = GhostBuildContext {
        tcx,
        user_specs,
        trait_specs,
        extern_specs,
    };
    let ghost_facts = build_ghost_context_for_function(
        &ghost_build_ctx,
        contract,
        &parsed.arg_names,
        ghost_blocks,
        &collect_focus_var_names(
            effective_requires,
            effective_ensures,
            parsed.result_expr.as_ref(),
        ),
        None,
        None,
    );
    let ghost_context = ghost_facts.alias_facts;
    if !ghost_context.is_empty() {
        trace!(
            count = ghost_context.len(),
            "ghost context assumption(s) injected"
        );
    }

    PerFunctionSolverContext {
        closure_capture_infos,
        ghost_context,
        synthesized_final_values,
    }
}

/// Dispatch a single contract to the ay solver (#1526 Phase 5).
///
/// Selects the correct verification API based on whether the function has explicit
/// mutable borrow analysis, synthesized final values, or is a pure function.
/// The three-way dispatch deduplicates the builder-pattern request construction.
pub(super) fn dispatch_smt_verification(
    parsed: &super::super::parsing::ParsedContract,
    effective_requires: &[PureExpr],
    effective_ensures: &[PureExpr],
    synthesized_final_values: Option<&HashMap<String, PureExpr>>,
    params: &SolverParams<'_>,
    is_ghost: bool,
    unsoundness_before: trust_wp_ay::unsoundness::Snapshot,
) -> Result<VerificationOutcome, EncodingError> {
    // #prophecy-slots M5: caller-side expiry pins. Empty unless the driver
    // PROVED a death point (`projected_expiry` R0..R11); the encoder refuses
    // fail-closed on top of that if the projection cannot be walked exactly.
    let projected_pins = (!parsed.mut_borrow.projected_final_pins.is_empty())
        .then(|| parsed.mut_borrow.projected_final_pins.clone());

    // D-27: `contract_transform` appends `parsed.call_obligations` to the
    // function's goals, and every extractor lane that cannot model a construct
    // fails closed by pushing `false` into them (an unspecified callee, a
    // dropped spec clause, an exhausted walk, ...). The marker stays — it is
    // what stops the function being proved — but a SAT model for a goal set
    // containing `false` refutes a clause TRUST-WP wrote, so the boundary
    // withholds the refutation. Read from `call_obligations`, never from
    // `effective_ensures`: a user's own `#[ensures(false)]` is a clause the
    // program really can violate and must keep its FAILED.
    //
    // The question is a COUNT, and only SUBTRACTION is safe. Both kinds of
    // `false` — the marker and a clause somebody wrote — are spelled
    // `PureExpr::Bool(false)`, so the total cannot be refined by looking at
    // it; what can be known is how many of them came from a lane that knows
    // its own provenance. An injection lane this crate forgets to name still
    // lands in the total and still arms the gate.
    let injected_fail_closed_goal = injected_fail_closed_goal_count(parsed) > 0;

    let outcome = if let Some(ref mut_borrow) = parsed.mut_borrow.mut_borrow_body {
        // Phase 5b (#2124): SSA-rename sequential mutation call_assumptions.
        // This transforms Final^k chains into SSA intermediates so the solver
        // can chain mutations: v_current → v_ssa_1 → ... → v_final.
        let mut ssa_requires = effective_requires.to_vec();
        let did_ssa_rename =
            super::contract_transform::ssa_rename_call_assumptions(&mut ssa_requires);
        if did_ssa_rename {
            tracing::debug!(
                count = ssa_requires.len(),
                "Phase 5b: SSA-renamed call_assumptions for mut borrow verification"
            );
        }
        let effective_requires = &ssa_requires;

        // Extract resolve assumption names from dataflow analysis (#2124).
        let resolve_names = mut_borrow.resolve_results.as_ref().map(|rr| {
            rr.has_precise_resolve
                .iter()
                .filter(|(_, &has)| has)
                .map(|(name, _)| name.clone())
                .collect::<Vec<_>>()
        });
        // Extract immediate prophecy writeback pairs from resolve metadata.
        // Two-phase writebacks are delayed into call_assumptions by the driver
        // and must not be forwarded through the immediate ay writeback path.
        let prophecy_writebacks = mut_borrow.resolve_results.as_ref().and_then(|rr| {
            let writebacks: std::collections::HashMap<String, String> = rr
                .writebacks
                .iter()
                .filter(|writeback| writeback.activation.is_none())
                .map(|writeback| (writeback.child_name.clone(), writeback.parent_name.clone()))
                .collect();
            if writebacks.is_empty() {
                None
            } else {
                Some(writebacks)
            }
        });
        // Extract per-reborrow finality from backward dataflow analysis (#2181).
        let borrow_finality = if mut_borrow.finality.is_empty() {
            None
        } else {
            Some(mut_borrow.finality.clone())
        };
        let borrow_id_origins = if mut_borrow.borrow_id_origins.is_empty() {
            None
        } else {
            Some(mut_borrow.borrow_id_origins.clone())
        };
        // Extract mutation-continued params (#2124 Phase 5b): parameters that
        // received mutation calls but couldn't be symbolically advanced. The
        // identity assertion `v_final == v_current` is suppressed in the ay layer,
        // and resolve assertions must also skip these params to avoid contradicting
        // call_assumptions that constrain v_final to the post-mutation state.
        let mutation_continued = if mut_borrow.mutation_continued_params.is_empty() {
            None
        } else {
            let mut params = mut_borrow.mutation_continued_params.clone();
            if let Some(synth_fv) = synthesized_final_values {
                for name in synth_fv.keys() {
                    params.remove(name);
                }
            }
            (!params.is_empty()).then_some(params)
        };
        let final_values = if let Some(synth_fv) = synthesized_final_values {
            let mut merged = mut_borrow.final_values.clone();
            merged.extend(
                synth_fv
                    .iter()
                    .map(|(name, value)| (name.clone(), value.clone())),
            );
            merged
        } else {
            mut_borrow.final_values.clone()
        };
        verify_mut_borrow_function_with_modes_outcome(
            MutBorrowRequest::new(effective_requires, effective_ensures, &final_values)
                .ghost_context(params.ghost_context_opt)
                .return_expr(parsed.result_expr.as_ref())
                .logic_fns(params.logic_fns_opt)
                .mode_overrides(params.mode_overrides_opt)
                .type_invariants(params.type_invariants_opt)
                .track(Some(params.track_level))
                .timeout(params.timeout)
                .type_constants(params.type_constants)
                .closure_captures(params.closure_captures_opt)
                .total_int_arithmetic(is_ghost)
                .adt_field_ranges(params.adt_field_ranges.clone())
                .adt_decls(params.adt_decls.clone())
                .bitwise_proof(params.bitwise_proof)
                .resolve_assumptions(resolve_names)
                .prophecy_writebacks(prophecy_writebacks)
                .borrow_finality(borrow_finality)
                .borrow_id_origins(borrow_id_origins)
                .mutation_continued_params(mutation_continued)
                .projected_final_pins(projected_pins.clone())
                .unsoundness_snapshot(Some(unsoundness_before))
                .injected_fail_closed_goal(injected_fail_closed_goal),
        )
    } else if let Some(synth_fv) = synthesized_final_values {
        verify_mut_borrow_function_with_modes_outcome(
            MutBorrowRequest::new(effective_requires, effective_ensures, synth_fv)
                .ghost_context(params.ghost_context_opt)
                .return_expr(parsed.result_expr.as_ref())
                .logic_fns(params.logic_fns_opt)
                .mode_overrides(params.mode_overrides_opt)
                .type_invariants(params.type_invariants_opt)
                .track(Some(params.track_level))
                .timeout(params.timeout)
                .type_constants(params.type_constants)
                .closure_captures(params.closure_captures_opt)
                .total_int_arithmetic(is_ghost)
                .adt_field_ranges(params.adt_field_ranges.clone())
                .adt_decls(params.adt_decls.clone())
                .bitwise_proof(params.bitwise_proof)
                .projected_final_pins(projected_pins.clone())
                .unsoundness_snapshot(Some(unsoundness_before))
                .injected_fail_closed_goal(injected_fail_closed_goal),
        )
    } else {
        verify_function_with_modes_outcome(
            VerificationRequest::new(effective_requires, effective_ensures)
                .ghost_context(params.ghost_context_opt)
                .return_expr(parsed.result_expr.as_ref())
                .logic_fns(params.logic_fns_opt)
                .mode_overrides(params.mode_overrides_opt)
                .type_invariants(params.type_invariants_opt)
                .track(Some(params.track_level))
                .timeout(params.timeout)
                .type_constants(params.type_constants)
                .closure_captures(params.closure_captures_opt)
                .total_int_arithmetic(is_ghost)
                .adt_field_ranges(params.adt_field_ranges.clone())
                .adt_decls(params.adt_decls.clone())
                .bitwise_proof(params.bitwise_proof)
                .unsoundness_snapshot(Some(unsoundness_before))
                .injected_fail_closed_goal(injected_fail_closed_goal),
        )
    };
    withhold_refutation_resting_on_a_withdrawn_axiom(
        outcome,
        params,
        &solver_facing_exprs(
            parsed,
            effective_requires,
            effective_ensures,
            synthesized_final_values,
        ),
    )
}

/// The formulas this dispatch actually hands the solver.
///
/// The premises and goals carry the contract's own clauses and everything
/// `transform_contract` folded into them, but the returned value's model and
/// the final values of the mutable parameters travel as separate arguments and
/// are substituted into the goals by the encoder. A logic call that appears
/// only there is still a symbol the query depends on, so it belongs in any
/// question about what the query reaches.
fn solver_facing_exprs<'a>(
    parsed: &'a super::super::parsing::ParsedContract,
    effective_requires: &'a [PureExpr],
    effective_ensures: &'a [PureExpr],
    synthesized_final_values: Option<&'a HashMap<String, PureExpr>>,
) -> Vec<&'a PureExpr> {
    let mut exprs: Vec<&PureExpr> = effective_requires.iter().chain(effective_ensures).collect();
    exprs.extend(parsed.result_expr.iter());
    exprs.extend(
        parsed
            .result_expr_spanned
            .iter()
            .map(|spanned| &spanned.expr),
    );
    if let Some(mut_borrow) = parsed.mut_borrow.mut_borrow_body.as_ref() {
        exprs.extend(mut_borrow.final_values.values());
    }
    exprs.extend(
        synthesized_final_values
            .into_iter()
            .flat_map(HashMap::values),
    );
    exprs
}

/// Refuse rather than refute when the model rests on a WITHDRAWN axiom.
///
/// Sibling of the D-27 gate above, and the same argument one step further out.
/// There the withheld refutation was of a `false` goal trust-wp itself wrote;
/// here it is of a goal whose premises trust-wp itself took away.
/// Neutralization strips an unproved logic function to a bare declaration, so
/// the solver is free to model the missing law as FALSE and hand back a
/// "counterexample" to a contract that is perfectly true — a trait law its
/// only impl honours, refuted at the hop that uses it
/// (`l_law_control_honoured_law_is_not_refuted.rs`).
///
/// `FAILED` asserts a violating state exists. When the state exists only
/// because a fact was withdrawn, the honest claim is that trust-wp cannot
/// decide the obligation without the axiom it refused to grant, so the verdict
/// carries the standard withheld-refutation spelling and the run exits as a
/// refusal. Narrowing only: it can turn a refutation into an inconclusive and
/// nothing else, so no obligation becomes provable by passing through here.
fn withhold_refutation_resting_on_a_withdrawn_axiom(
    outcome: Result<VerificationOutcome, EncodingError>,
    params: &SolverParams<'_>,
    obligations: &[&PureExpr],
) -> Result<VerificationOutcome, EncodingError> {
    outcome.map(|mut outcome| {
        if !matches!(outcome.result, VerificationResult::Failed(_)) {
            return outcome;
        }
        let Some(axiom) = super::prep::neutralized_axiom_reached(
            params.logic_fns_opt.unwrap_or(&[]),
            params.unverified_axioms,
            obligations.iter().copied(),
        ) else {
            return outcome;
        };
        outcome.result = VerificationResult::Unknown(UnknownReason::SolverMessage(format!(
            "{}: the obligation depends on `{axiom}`, an unproved axiom trust-wp withdrew; \
             a model that violates a withdrawn fact refutes nothing",
            trust_wp_ay::REFUTATION_AUTHORITY_MESSAGE
        )));
        outcome
    })
}

/// How many of a function's call obligations are a fail-closed `false` the
/// DRIVER injected because it could not model a construct (D-27).
///
/// Two subtrahends, both counted where their provenance is known:
///
/// * a body with no reachable `Return` (`fn f() { panic!() }`) subsumes the
///   whole count. Its only goal is "this body is unreachable" — the goal
///   Creusot states too, and one trust-wp genuinely refutes — so there is no
///   user-facing claim for a marker to manufacture. Counting instead of
///   subsuming is what made `panic!("msg")` stop reporting FAILED: that
///   spelling lowers through a returning `Arguments::new_const` with no spec,
///   so the panic prologue injects a marker of its own and `2 > 1` withholds a
///   real refutation (`i3_body_panic_unconditional.rs` pins the carve-out).
/// * a callee's own `#[requires(false)]` substituted at a call site is a
///   clause SOMEBODY WROTE and keeps its FAILED — the same distinction the
///   ensures side draws by reading `parsed.call_obligations` rather than
///   `effective_ensures`.
///
/// And a marker that restates the unreachability goal of the panic arm it sits
/// in is not counted (`trust_wp_ay::unpaired_fail_closed_marker_count`): the
/// same prologue marker, inside a reachable `panic!("msg")` ARM, sits under the
/// arm's guard, and counting it would withhold that arm's real refutation.
/// Which markers the user wrote is known only as a number, so the count is the
/// smaller of the unpaired markers and all markers less the written ones: each
/// bounds the injected unpaired markers from above, so neither can hide one.
fn injected_fail_closed_goal_count(parsed: &super::super::parsing::ParsedContract) -> usize {
    let total = trust_wp_ay::fail_closed_marker_count(&parsed.call_obligations);
    let unpaired = trust_wp_ay::unpaired_fail_closed_marker_count(&parsed.call_obligations);
    let count = if parsed.panic_unreachability_obligations > 0 {
        0
    } else {
        unpaired.min(total.saturating_sub(parsed.user_written_false_obligations))
    };
    if std::env::var_os("TRUST_WP_AUTHORITY_TRACE").is_some() {
        eprintln!(
            "[TWP_AUTH] injected fail-closed goal count: total={total} unpaired={unpaired} \
             panic_unreachability={} user_written={} -> injected={count}",
            parsed.panic_unreachability_obligations, parsed.user_written_false_obligations
        );
    }
    count
}
