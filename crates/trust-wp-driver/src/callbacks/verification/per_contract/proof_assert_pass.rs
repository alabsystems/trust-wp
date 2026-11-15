// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The in-function `proof_assert!` pass, shared by both exits of
//! `verify_single_contract`.
//!
//! Both the function-level path and the loop lane's `Handled` return owe the
//! body's assertions a verdict (D-38), and they differ only in the loop-exit
//! premise they can offer.

use rustc_span::source_map::SourceMap;
use trust_wp_core::{formula::PureExpr, logic::TypeInvariantDef};

use super::super::{
    super::{
        super::contracts::FunctionContract, parsing::ParsedContract, reporting::ProofAssertCounters,
    },
    in_function_proof_assert::{verify_in_function_proof_asserts, InFunctionProofAssertContext},
    SharedVerificationState,
};

/// Everything the assertion pass needs that is not already reachable through
/// `shared` or `parsed`.
pub(super) struct ProofAssertPass<'a> {
    pub(super) contract: &'a FunctionContract,
    pub(super) parsed: &'a ParsedContract,
    pub(super) def_path: &'a str,
    pub(super) local_crate_name: &'a str,
    pub(super) source_map: &'a SourceMap,
    pub(super) type_invariants_opt: Option<&'a [TypeInvariantDef]>,
    /// `invariants ∧ ¬condition ∧ frame_constraints` at loop exit, when a loop
    /// lane proved them; `None` when there is nothing proven to offer.
    pub(super) loop_exit_assumptions: Option<&'a [PureExpr]>,
}

pub(super) fn run_in_function_proof_asserts(
    shared: &SharedVerificationState<'_, '_>,
    pass: &ProofAssertPass<'_>,
    pa_counters: &mut ProofAssertCounters,
) {
    let verdicts_before = adjudicated_count(pa_counters);
    verify_in_function_proof_asserts(
        shared.tcx,
        &InFunctionProofAssertContext {
            contract: pass.contract,
            arg_names: &pass.parsed.arg_names,
            loop_spans: &pass.parsed.loop_fields.all_loop_spans,
            loop_exit_assumptions: pass.loop_exit_assumptions,
            ghost_blocks: shared.config.ghost_blocks,
            user_specs: &shared.prep.user_specs,
            trait_specs: shared.config.trait_specs,
            extern_specs: shared.config.extern_specs,
            mut_borrow_body: pass.parsed.mut_borrow.mut_borrow_body.as_ref(),
            // The SAME pins the contract obligation used (`solver_dispatch`),
            // reused rather than recomputed — identical
            // body, identical `arg_names`, identical adjudication.
            projected_final_pins: &pass.parsed.mut_borrow.projected_final_pins,
            pa_setup: shared.pa_setup,
            pa_ctx: &shared.pa_ctx,
            pa_logic_fns_opt: shared.pa_logic_fns_opt,
            type_invariants_opt: pass.type_invariants_opt,
            local_crate_name: pass.local_crate_name,
            source_map: pass.source_map,
            track_level: shared.config.track_level,
            timeout: shared.config.timeout,
            def_path: pass.def_path,
        },
        pa_counters,
    );
    // A clause-free function can reach BOTH assertion passes: the main
    // contract loop admits it as a target for its body obligations and runs
    // this pass, and the standalone pass then walks the same MIR again. Each
    // source `proof_assert!` would get two identical verdicts for one
    // obligation, so the goal inventory's single assertion reads as a
    // count mismatch against the driver's two — one obligation, proved once,
    // counted twice.
    //
    // Claimed only when this pass actually answered something. A pass that
    // produced no verdict leaves the function to the standalone pass rather
    // than silencing its assertions altogether.
    if adjudicated_count(pa_counters) > verdicts_before {
        pa_counters
            .assertions_adjudicated
            .insert(pass.contract.def_id);
    }
}

/// Every outcome that counts as "this assertion got an answer".
fn adjudicated_count(pa_counters: &ProofAssertCounters) -> usize {
    pa_counters.verified
        + pa_counters.failed
        + pa_counters.errors
        + pa_counters.inconclusive
        + pa_counters.evidence_gaps
        + pa_counters.refutations_withheld
}
