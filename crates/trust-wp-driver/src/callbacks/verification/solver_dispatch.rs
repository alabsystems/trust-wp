// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SMT solver dispatch and per-function solver context (#1526 Phase 5).
//!
//! Groups the solver parameter structs and the three-way dispatch logic
//! (`verify_function_with_modes_outcome` vs
//! `verify_mut_borrow_function_with_modes_outcome`)
//! into a single module.

use std::{collections::HashMap, time::Duration};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use tracing::trace;
use trust_wp_ay::{
    verify_function_with_modes_outcome, verify_mut_borrow_function_with_modes_outcome,
    EncodingError, MutBorrowRequest, VerificationOutcome, VerificationRequest,
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

    if let Some(ref mut_borrow) = parsed.mut_borrow.mut_borrow_body {
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
                .unsoundness_snapshot(Some(unsoundness_before)),
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
                .unsoundness_snapshot(Some(unsoundness_before)),
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
                .unsoundness_snapshot(Some(unsoundness_before)),
        )
    }
}
