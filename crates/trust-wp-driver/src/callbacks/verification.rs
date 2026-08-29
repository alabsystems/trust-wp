// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! AY verification of function contracts.
//!
//! Contains the main `verify_contracts` function that orchestrates verification
//! of all discovered contracts. SMT-LIB2 emission lives in `smt_output.rs`.

use std::{
    collections::HashSet,
    panic::{catch_unwind, AssertUnwindSafe},
    time::Duration,
};

// Submodule re-exports for extracted Phase 5 components (#1526).
use contract_transform::TransformedContract;
// SMT output generation extracted to `smt_output.rs` (#1526).

// Reporting functions and counter types extracted to `reporting.rs` (#1526).
use rustc_middle::ty::TyCtxt;
use skip_decision::{check_contract_skip, SkipDecision};
use tracing::{info_span, trace, warn};
use trusted_contract_validation::validate_trusted_contract_references;

use super::{
    super::contracts::FunctionContract,
    helpers::{build_proof_assert_setup, expr_contains_old},
    is_ay_panic_for_hook,
    reporting::{ProofAssertCounters, VerificationCounters},
    trait_refinement::check_logic_fn_trait_refinement,
};

/// Emit diagnostic traces for contract transformation results (#1526).
///
/// Logs postcondition transformation details (mut-ref params, old() usage),
/// call-site assumption counts, and call-site obligation counts.
pub(super) fn trace_transformation_results(
    tc: &TransformedContract,
    parsed: &super::parsing::ParsedContract,
    def_path: &str,
) {
    if !tc.mut_ref_params.is_empty() {
        trace!("postcondition transformation for {:?}", tc.mut_ref_params);
    } else if tc.closure_capture_fields.is_empty()
        && tc.effective_ensures.iter().any(expr_contains_old)
    {
        warn!(
            def_path = %def_path,
            "has old() but no mut_ref_params detected (postcondition transformation may be incomplete)"
        );
    }
    if !parsed.call_assumptions.is_empty() {
        trace!(
            count = parsed.call_assumptions.len(),
            "call-site assumption(s) from predicate postconditions"
        );
    }
    if !parsed.call_obligations.is_empty() {
        trace!(
            count = parsed.call_obligations.len(),
            "call-site precondition obligation(s) added to verification goals"
        );
    }
}

/// Emit diagnostic traces for body extraction and result expression (#1526, #1476).
///
/// Logs the extracted result expression, call assumption/obligation details,
/// and warns when body extraction failed but postconditions are present —
/// either referencing `result` (unconstrained) or parameters (unprovable).
pub(super) fn trace_extraction_results(
    parsed: &super::parsing::ParsedContract,
    contract: &FunctionContract,
    def_path: &str,
) {
    trace!(def_path = %def_path, result_expr = ?parsed.result_expr, "body extraction");
    if !parsed.call_assumptions.is_empty() {
        trace!(
            def_path = %def_path,
            call_assumptions = ?parsed.call_assumptions,
            "call assumptions",
        );
    }
    if !parsed.call_obligations.is_empty() {
        trace!(
            def_path = %def_path,
            call_obligations = ?parsed.call_obligations,
            "call obligations",
        );
    }
    if parsed.result_expr.is_none() && !contract.ensures.is_empty() {
        let ensures_mentions_result = contract.ensures.iter().any(|s| s.contains("result"));
        if ensures_mentions_result {
            warn!(
                def_path = %def_path,
                "body extraction returned None but postcondition references `result` — result will be unconstrained",
            );
        } else {
            // Postconditions that reference parameters (e.g. `*v`, `old(*v)`)
            // may also be unprovable without a body (#1476).
            warn!(
                def_path = %def_path,
                ensures_count = contract.ensures.len(),
                "body extraction returned None — postconditions may be unprovable without extracted body",
            );
        }
    }
}

/// Verify all contracts using ay directly
#[tracing::instrument(name = "trust_wp::verify_contracts", level = "info", skip_all, fields(contracts = contracts.len(), track_level = ?config.track_level))]
pub(super) fn verify_contracts(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
    config: &super::verification_context::VerificationRunConfig<'_>,
) -> super::reporting::VerificationSummary {
    let ghost_blocks = config.ghost_blocks;
    let type_invariant_defs = config.type_invariant_defs;
    let trait_specs = config.trait_specs;
    let extern_specs = config.extern_specs;
    let verbose = config.verbose;
    let track_level = config.track_level;
    let timeout = config.timeout;
    let mut counters = VerificationCounters::default();
    let mut unverified_axioms: HashSet<String> = HashSet::new();

    let prep = prepare_verification(
        tcx,
        contracts,
        config,
        &mut counters,
        &mut unverified_axioms,
    );
    // Full logic-function set for path/skip metadata and name normalization.
    let full_logic_fns = prep.logic_fns(config);
    // Downstream-safe set with unverified axioms neutralized (opaque, no
    // ensures) — for all solver paths (#1878).
    let logic_fns = prep.downstream_logic_fns(config);
    let type_invariants_opt = prep.type_invariants_opt;
    let logic_fn_paths = &prep.logic_fn_paths;
    let logic_fn_has_ensures = &prep.logic_fn_has_ensures;
    let user_specs = &prep.user_specs;

    let trusted_contract_errors = validate_trusted_contract_references(tcx, contracts);
    if !trusted_contract_errors.is_empty() {
        for error in &trusted_contract_errors {
            tcx.dcx()
                .span_err(tcx.def_span(error.contract_def_id), error.message.clone());
        }
        counters.errors += trusted_contract_errors.len();
        let pa_counters = ProofAssertCounters::default();
        return print_verification_summary(&counters, &pa_counters, &unverified_axioms, verbose);
    }

    // Pass the full logic-function set for path maps and the downgraded
    // user_specs (with unverified ensures cleared) for assumption injection (#1878).
    let (pa_setup, pa_setup_warnings) =
        build_proof_assert_setup(tcx, contracts, full_logic_fns, user_specs);
    counters.warnings += pa_setup_warnings;
    // ProofAssertContext uses the full set for name resolution in proof_assert
    // expressions. Solver-facing paths use the filtered `logic_fns` instead.
    let pa_ctx = super::verification_context::ProofAssertContext {
        logic_fn_defs: full_logic_fns,
        type_invariant_defs,
        trait_specs,
        extern_specs,
        verbose,
    };
    let pa_logic_fns_opt = (!logic_fns.is_empty()).then_some(logic_fns);
    let mut pa_counters = ProofAssertCounters::default();

    let adaptive_timeout = adaptive_timeout(
        tcx,
        contracts,
        logic_fn_paths,
        logic_fn_has_ensures,
        timeout,
    );
    let stop_after_first_adaptive_error =
        should_stop_after_first_adaptive_error(timeout, adaptive_timeout);
    let adaptive_config = super::verification_context::VerificationRunConfig {
        timeout: adaptive_timeout,
        ..*config
    };

    let shared = SharedVerificationState {
        tcx,
        config: adaptive_config,
        prep: &prep,
        logic_fns,
        pa_setup: &pa_setup,
        pa_ctx,
        pa_logic_fns_opt,
        unverified_axioms: &unverified_axioms,
    };

    let crate_start = std::time::Instant::now();
    let crate_wall_budget = crate_wall_budget(timeout);

    for contract in contracts {
        let def_path = tcx.def_path_str(contract.def_id);

        // Crate-level wall-clock budget check (#2674): skip remaining
        // verifiable functions when the budget is exhausted. Trusted and
        // axiom-only functions are still processed (instant, no solver).
        if let Some(budget) = crate_wall_budget {
            if crate_start.elapsed() >= budget {
                eprintln!(
                    "trust-wp: {def_path} skipped (crate wall-clock budget exhausted: \
                     {}s elapsed, {}s budget) (#2674)",
                    crate_start.elapsed().as_secs(),
                    budget.as_secs(),
                );
                counters.errors += 1;
                continue;
            }
        }

        // Consolidated skip-decision check (#1526 Phase 5).
        match check_contract_skip(tcx, contract, logic_fn_paths, logic_fn_has_ensures) {
            SkipDecision::Trusted => {
                counters.trusted += 1;
                eprintln!("trust-wp: {def_path} trusted (skipped)");
                continue;
            }
            SkipDecision::LogicFnAxiom => {
                eprintln!(
                    "trust-wp: {} is a logic function (definition registered)",
                    tcx.def_path_str(contract.def_id)
                );
                // Even though the body is not verified, trait refinement
                // obligations still apply to logic function impls (#2686).
                check_logic_fn_trait_refinement(
                    tcx,
                    contract,
                    config,
                    &prep.trait_contract_map,
                    logic_fns,
                    &unverified_axioms,
                    &mut counters,
                );
                continue;
            }
            SkipDecision::LogicFnEnsures => {
                eprintln!(
                    "trust-wp: {} is a logic function (postcondition will be verified)",
                    tcx.def_path_str(contract.def_id)
                );
                // Even though the body is not verified here (postcondition
                // verified in separate pass), trait refinement obligations
                // still apply to logic function impls (#2686).
                check_logic_fn_trait_refinement(
                    tcx,
                    contract,
                    config,
                    &prep.trait_contract_map,
                    logic_fns,
                    &unverified_axioms,
                    &mut counters,
                );
                continue;
            }
            SkipDecision::BodylessTraitMethod => {
                counters.skipped += 1;
                eprintln!(
                    "trust-wp: {} is a trait method declaration (spec only, not verified)",
                    tcx.def_path_str(contract.def_id)
                );
                continue;
            }
            SkipDecision::Verify => {}
        }

        let _fn_span = info_span!(
            "trust_wp::verify_function",
            def_path = %def_path,
            trusted = contract.trusted,
            has_invariants = !contract.invariants.is_empty(),
            has_variants = !contract.variants.is_empty(),
        )
        .entered();

        let prior_failed = counters.failed;
        let prior_errors = counters.errors;
        let panic_result = catch_unwind(AssertUnwindSafe(|| {
            verify_single_contract(
                &shared,
                contract,
                &def_path,
                &mut counters,
                &mut pa_counters,
            );
        })); // end catch_unwind (#1975)

        if let Err(panic_payload) = panic_result {
            let reason = ay_core::panic_payload_to_string(panic_payload.as_ref());
            counters.panics += 1;
            // Classify the panic origin (#2687): ay internal panics (sort
            // mismatches, prefetch OOB, Tseitin assertions) get a distinct
            // diagnostic message so the harness classifier can distinguish
            // them from trust-wp-side programmer errors. ay panics are expected
            // during incremental solving and do not indicate trust-wp bugs.
            if is_ay_panic_for_hook(&reason) {
                eprintln!("trust-wp: {def_path} ay solver panic during verification: {reason}");
            } else {
                eprintln!("trust-wp: {def_path} panicked during verification: {reason}");
            }
            eprintln!("  (continuing with remaining functions)");
        }

        if stop_after_first_adaptive_error
            && contract_added_failure_or_error(&counters, prior_failed, prior_errors)
        {
            eprintln!(
                "trust-wp: stopping remaining contract verification after first \
                 adaptive-budget failure/error (#3771)"
            );
            break;
        }
    }

    // Proof_assert-only function pass (#1581).
    let standalone_env = StandaloneProofAssertEnv {
        pa_setup: &pa_setup,
        pa_ctx: &pa_ctx,
        pa_logic_fns_opt,
        type_invariants_opt,
        ghost_blocks,
        user_specs,
        track_level,
        timeout,
    };
    verify_standalone_proof_asserts(
        tcx,
        contracts,
        logic_fn_paths,
        &standalone_env,
        &mut pa_counters,
    );

    print_verification_summary(&counters, &pa_counters, &unverified_axioms, verbose)
}

fn should_stop_after_first_adaptive_error(
    base_timeout: Option<Duration>,
    adaptive_timeout: Option<Duration>,
) -> bool {
    matches!(
        (base_timeout, adaptive_timeout),
        (Some(base), Some(adaptive)) if adaptive < base
    )
}

fn contract_added_failure_or_error(
    counters: &VerificationCounters,
    prior_failed: usize,
    prior_errors: usize,
) -> bool {
    counters.failed > prior_failed || counters.errors > prior_errors
}

use per_contract::{verify_single_contract, SharedVerificationState};
#[cfg(test)]
pub(super) use prep::{downgrade_unverified_logic_specs, filter_downstream_logic_fns};
pub(super) use prep::{prepare_verification, PreparedVerification};
pub(super) use smt_output::{
    build_smt_artifacts, emit_smt_artifacts_to_stdout, write_smt_artifacts_to_dir,
};
use standalone_proof_assert::{verify_standalone_proof_asserts, StandaloneProofAssertEnv};
use summary::print_verification_summary;
use timeout_budget::{adaptive_timeout, crate_wall_budget};

mod clause_enrichment;
pub(in crate::callbacks) mod contract_transform;
mod in_function_proof_assert;
mod logic_fn_verify;
mod loop_contract;
mod nested_reborrow_transfer;
mod per_contract;
mod post_loop_final_values;
mod prep;
mod proof_assert_driver;
mod proof_assert_loop_assumptions;
mod recursive_induction;
mod recursive_verify;
mod skip_decision;
mod smt_output;
mod solver_dispatch;
mod standalone_proof_assert;
mod store_prophecy_repair;
mod summary;
mod timeout_budget;
mod trusted_contract_validation;

#[cfg(test)]
mod tests;
