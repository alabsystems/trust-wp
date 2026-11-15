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
};

use contract_transform::TransformedContract;
use rustc_middle::ty::TyCtxt;
use skip_decision::{check_contract_skip, SkipDecision};
use tracing::{info_span, trace, warn};
use trusted_contract_validation::validate_trusted_contract_references;

use super::{
    super::contracts::FunctionContract,
    helpers::{build_proof_assert_setup, expr_contains_old},
    reporting::{ProofAssertCounters, VerificationCounters},
    trait_refinement::verify_trait_impl_refinements,
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
        counters.errors = counters
            .errors
            .saturating_add(trusted_contract_errors.len());
        let pa_counters = ProofAssertCounters::default();
        return print_verification_summary(&counters, &pa_counters, &unverified_axioms, verbose);
    }

    // Pass the full logic-function set for path maps and the downgraded
    // user_specs (with unverified ensures cleared) for assumption injection (#1878).
    let (pa_setup, pa_setup_warnings) =
        build_proof_assert_setup(tcx, contracts, full_logic_fns, user_specs);
    counters.warnings = counters.warnings.saturating_add(pa_setup_warnings);
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

    let adaptive_budget = adaptive_timeout(
        tcx,
        contracts,
        logic_fn_paths,
        logic_fn_has_ensures,
        timeout,
    );
    let adaptive_timeout = adaptive_budget.timeout;
    let stop_after_first_adaptive_error =
        should_stop_after_first_adaptive_error(timeout, adaptive_budget);
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
    // Reserved before admitting the next obligation, and published for the
    // whole run because the obligations that overrun a crate are not always
    // contracts. See `watchdog_envelope` and `publish_crate_deadline`.
    let admission_reserve = watchdog_envelope(adaptive_timeout);
    let _crate_deadline_guard =
        publish_crate_deadline(crate_wall_budget, crate_start, admission_reserve);

    // Trait-contract credit ledger (trait-contract-assumed-without-discharge).
    let mut trait_credit_join = TraitCreditJoin::default();
    let mut adaptive_stop = AdaptiveStop::default();
    trait_credit_join.register_own_contracts(tcx, contracts, logic_fn_paths, logic_fn_has_ensures);

    for contract in contracts {
        if adaptive_stop.passes_over(tcx, trait_specs, contract.def_id) {
            continue;
        }
        let def_path = tcx.def_path_str(contract.def_id);

        // Crate-level wall-clock budget check (#2674): skip remaining
        // verifiable functions when the budget is exhausted. Trusted
        // functions are still processed (instant, no solver).
        if !admit_within_crate_budget(&def_path, crate_start.elapsed()) {
            counters.errors += 1;
            continue;
        }

        trait_credit_join.reach(contract.def_id);
        // Consolidated skip-decision check (#1526 Phase 5).
        match check_contract_skip(tcx, contract, logic_fn_paths, logic_fn_has_ensures) {
            SkipDecision::Trusted => {
                counters.trusted += 1;
                eprintln!("trust-wp: {def_path} trusted (skipped)");
                continue;
            }
            decision @ (SkipDecision::LogicFnAxiom | SkipDecision::LogicFnEnsures) => {
                let what = if matches!(decision, SkipDecision::LogicFnAxiom) {
                    "definition registered"
                } else {
                    "postcondition will be verified"
                };
                eprintln!("trust-wp: {def_path} is a logic function ({what})");
                // Trait refinement for logic impls runs in the standalone
                // refinement pass below (#2686). The trait contract such an
                // impl owes is settled here, never by silence.
                let undischarged = &prep.undischarged_logic_impls;
                trait_credit_join.end_logic_item(tcx, trait_specs, contract.def_id, undischarged);
                continue;
            }
            SkipDecision::CoroutineBody => {
                skip_decision::refuse_coroutine_body(&def_path, &mut counters);
                trait_credit_join.refused(tcx, trait_specs, contract.def_id);
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
        // Trait-contract credit (trait-contract-assumed-without-discharge):
        // bank this item's credit with the contracted trait methods its
        // verification conditions were handed, so the demotion pass below can
        // withdraw it if it rests, directly or through calls, on a contract an
        // impl never discharged.
        let credit_before = CounterSnapshot::take(&counters, &pa_counters);
        trait_credit_join.begin_item();
        let panic_result = catch_unwind(AssertUnwindSafe(|| {
            probe_panic_hook(&def_path);
            function_verdict::verify_function(
                &shared,
                contract,
                &def_path,
                &mut counters,
                &mut pa_counters,
            );
        })); // end catch_unwind (#1975)
             // FAIL-CLOSED GUARD (#1975): the panic must be RECORDED. `counters.panics`
             // is the only trace a panicked item leaves; without it a crashed proof
             // reads as a pass. It is deliberately recorded BEFORE the trait-credit
             // join, so that `end_item` sees the panic delta and refuses to treat a
             // panicked impl body as having discharged the trait contract it inherited.
        report_verification_panic(&def_path, panic_result, &mut counters);
        super::function_credit::discard_held_credits(&mut counters);
        trait_credit_join.end_item(
            tcx,
            trait_specs,
            contract.def_id,
            &def_path,
            &credit_before,
            &counters,
            &pa_counters,
        );

        adaptive_stop.after_contract(stop_after_first_adaptive_error, &counters, prior_failed);
    }
    trait_credit_join.record_unexamined(tcx, trait_specs);

    // Standalone trait refinement pass: one verdict for every trait impl
    // method, independent of whether its body was verified.
    verify_trait_impl_refinements(
        tcx,
        contracts,
        config,
        &prep.trait_contract_map,
        logic_fns,
        &mut counters,
        trait_credit_join.undischarged_mut(),
    );

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
        &mut counters,
        &mut pa_counters,
        &mut trait_credit_join,
    );

    let join = &mut trait_credit_join;
    escape_credit_join::demote(tcx, config, join, &mut counters, &mut pa_counters);

    print_verification_summary(&counters, &pa_counters, &unverified_axioms, verbose)
}

use fail_fast_policy::{should_stop_after_first_adaptive_error, AdaptiveStop};
use panic_guard::{probe_panic_hook, report_verification_panic};
use per_contract::SharedVerificationState;
#[cfg(test)]
pub(super) use prep::{downgrade_unverified_logic_specs, filter_downstream_logic_fns};
pub(super) use prep::{neutralized_axiom_reached, prepare_verification, PreparedVerification};
pub(super) use smt_output::{
    build_smt_artifacts, emit_smt_artifacts_to_stdout, write_smt_artifacts_to_dir,
};
use standalone_proof_assert::{verify_standalone_proof_asserts, StandaloneProofAssertEnv};
use summary::print_verification_summary;
use timeout_budget::{
    adaptive_timeout, admit_within_crate_budget, crate_wall_budget, publish_crate_deadline,
    watchdog_envelope,
};
use trait_credit_join::{CounterSnapshot, TraitCreditJoin};

mod clause_enrichment;
mod compound_newtype_guard;
pub(in crate::callbacks) mod contract_transform;
mod credit_graph;
mod escape_credit_join;
pub(super) mod fail_fast_policy;
mod field_order_guard;
mod function_verdict;
mod in_function_proof_assert;
mod logic_fn_verify;
mod loop_contract;
mod nested_reborrow_transfer;
mod panic_guard;
mod partial_verdict;
mod per_contract;
mod post_loop_final_values;
mod prep;
mod proof_assert_driver;
mod proof_assert_loop_assumptions;
mod recursive_induction;
mod recursive_verify;
pub(in crate::callbacks) mod skip_decision;
mod smt_output;
mod solver_dispatch;
mod stale_call_final;
mod standalone_proof_assert;
mod store_prophecy_repair;
mod summary;
mod timeout_budget;
mod trait_credit_join;
mod trusted_contract_validation;

#[cfg(test)]
mod tests;
