// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Standalone proof_assert verification (no explicit contracts).
//!
//! Functions that contain `proof_assert!` but have no `requires`/`ensures`/
//! `invariants`/`variants` are verified here. Extracted from `verification.rs`
//! (#1669).
//!
//! The per-snapshot execution loop is now owned by
//! `proof_assert_driver::verify_proof_assert_snapshots`. This module keeps
//! only the contract filtering, catch_unwind boundary, MIR discovery, and
//! snapshot building. (#2332)

use std::{
    collections::{HashMap, HashSet},
    panic::{catch_unwind, AssertUnwindSafe},
};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use tracing::debug;
use trust_wp_core::{
    logic::{LogicFnDef, TypeInvariantDef},
    TrackLevel,
};
use trust_wp_driver::StdSpec;

use super::super::{
    super::{
        contracts::FunctionContract,
        ghost::GhostBlock,
        mir_analysis::{extract_mut_borrow_body, get_mir_body},
        proof_assert::find_proof_asserts_in_mir,
    },
    proof_assert_extract::get_arg_names_for_proof_assert_body,
    proof_assert_snapshot::build_assertion_snapshots_for_function,
    reporting::ProofAssertCounters,
    try_get_body_with_context,
};

/// Read-only context for standalone proof_assert verification.
///
/// Bundles the shared environment that is threaded unchanged through
/// both the per-contract loop and inner verification, keeping function
/// signatures under clippy's `too_many_arguments` threshold. (#2657)
pub(in crate::callbacks) struct StandaloneProofAssertEnv<'a> {
    pub(in crate::callbacks) pa_setup: &'a super::super::proof_assert_verify::ProofAssertSetup<'a>,
    pub(in crate::callbacks) pa_ctx: &'a super::super::verification_context::ProofAssertContext<'a>,
    pub(in crate::callbacks) pa_logic_fns_opt: Option<&'a [LogicFnDef]>,
    pub(in crate::callbacks) type_invariants_opt: Option<&'a [TypeInvariantDef]>,
    pub(in crate::callbacks) ghost_blocks: &'a [GhostBlock],
    pub(in crate::callbacks) user_specs: &'a HashMap<DefId, StdSpec>,
    pub(in crate::callbacks) track_level: TrackLevel,
    pub(in crate::callbacks) timeout: Option<std::time::Duration>,
}

/// Verify proof_assert-only functions (no explicit contracts).
///
/// Functions that contain `proof_assert!` but have no `requires`/`ensures`/`invariants`/`variants`
/// are added to the contracts list by `discover_proof_assert_functions()`. The main contract
/// loop skips them because `parse_and_extract_contract` returns `None` for empty-contract
/// functions. This separate pass detects proof_asserts in MIR and verifies each one. (#1581)
pub(in crate::callbacks) fn verify_standalone_proof_asserts(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
    logic_fn_paths: &HashSet<String>,
    env: &StandaloneProofAssertEnv<'_>,
    pa_counters: &mut ProofAssertCounters,
) {
    for contract in contracts {
        // Only process proof_assert-only functions (no explicit clauses)
        if !contract.requires.is_empty()
            || !contract.ensures.is_empty()
            || !contract.invariants.is_empty()
            || !contract.variants.is_empty()
        {
            continue;
        }

        // Skip trusted and logic functions (already handled above)
        if contract.trusted {
            continue;
        }
        let def_path = tcx.def_path_str(contract.def_id);
        if logic_fn_paths.contains(&def_path)
            || super::super::super::logic::has_logic_marker(tcx.get_all_attrs(contract.def_id))
        {
            continue;
        }

        // Per-contract catch_unwind boundary (#2290).
        //
        // Mirrors the main verification loop pattern (#1975). Wraps MIR body
        // access, snapshot building, and verification so that a panic in one
        // proof_assert-only function does not halt remaining assertions.
        let panic_result = catch_unwind(AssertUnwindSafe(|| {
            verify_single_standalone_contract(tcx, contract, &def_path, env, pa_counters);
        }));

        if let Err(panic_payload) = panic_result {
            let reason = ay_core::panic_payload_to_string(panic_payload.as_ref());
            pa_counters.errors += 1;
            // Classify ay panics distinctly from trust-wp-side programmer errors,
            // matching the function-level panic handler in verification.rs. (#2687)
            if crate::callbacks::panic_hook::is_ay_panic_for_hook(&reason) {
                eprintln!(
                    "trust-wp: {def_path} ay solver panic during standalone proof_assert: {reason}"
                );
            } else {
                eprintln!("trust-wp: {def_path} panicked during standalone proof_assert: {reason}");
            }
            eprintln!("  (continuing with remaining proof_assert functions)");
        }
    }
}

/// Verify a single proof_assert-only contract.
///
/// Discovers proof_asserts in MIR, builds snapshots, then delegates to the
/// shared driver for per-snapshot verification. (#2332)
fn verify_single_standalone_contract(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    def_path: &str,
    env: &StandaloneProofAssertEnv<'_>,
    pa_counters: &mut ProofAssertCounters,
) {
    let Some(body_with_facts) = try_get_body_with_context(contract.local_def_id) else {
        return;
    };
    let mir_body = get_mir_body(body_with_facts);
    let fn_proof_asserts = find_proof_asserts_in_mir(tcx, mir_body, contract.local_def_id);
    if fn_proof_asserts.is_empty() {
        return;
    }
    let arg_names = get_arg_names_for_proof_assert_body(tcx, contract.local_def_id);
    let mut_borrow_body = extract_mut_borrow_body(
        tcx,
        mir_body,
        Some(body_with_facts),
        &arg_names,
        env.user_specs,
        env.pa_ctx.trait_specs,
        env.pa_ctx.extern_specs,
    );

    // #prophecy-slots M6: prove the caller-side death points for `&mut` borrows
    // that arrive inside a call result.
    //
    // M5 wired this lane into the CONTRACT extraction pipeline only
    // (`parsing::extraction::extract_contract_body`). A contractless
    // proof_assert body never enters that pipeline at all, so the whole
    // `ghost!` / `proof_assert!` cluster — the shapes that actually take a
    // `&mut` out of a call result and let it expire inside the body
    // (`if let Some(x) = map.get_mut_ghost(&1) { *x = 43; }`) — was not even
    // reached. Same adjudicator, same MIR body, same `arg_names` the rest of
    // this function uses: no parallel implementation.
    let projected_expiry = crate::mir_analysis::projected_expiry::collect_projected_expiry_pins(
        tcx, mir_body, &arg_names,
    );
    if !projected_expiry.is_empty() {
        debug!(
            pins = projected_expiry.pins.len(),
            def_path = %def_path,
            "projected_expiry: PROVEN caller-side expiry pin(s) (standalone proof_assert)",
        );
    }
    if !projected_expiry.disarms.is_empty() {
        debug!(
            disarms = ?projected_expiry.disarms,
            def_path = %def_path,
            "projected_expiry: candidate shape(s) disarmed (standalone proof_assert)",
        );
    }
    let projected_final_pins = projected_expiry.pins;

    let local_crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string();
    debug!(
        count = fn_proof_asserts.len(),
        def_path = %def_path,
        "verifying standalone proof_assert(s) (no contracts)",
    );

    let snapshots = build_assertion_snapshots_for_function(
        tcx,
        &fn_proof_asserts,
        env.ghost_blocks,
        &env.pa_setup.user_specs,
        env.pa_ctx,
        &local_crate_name,
    );

    let host = super::proof_assert_driver::ProofAssertHost::Contractless {
        contract,
        user_specs: env.user_specs,
        trait_specs: env.pa_ctx.trait_specs,
        extern_specs: env.pa_ctx.extern_specs,
        mut_borrow_body: mut_borrow_body.as_ref(),
        projected_final_pins: &projected_final_pins,
        def_path,
    };
    let driver_ctx = super::proof_assert_driver::ProofAssertDriverContext {
        pa_setup: env.pa_setup,
        pa_ctx: env.pa_ctx,
        pa_logic_fns_opt: env.pa_logic_fns_opt,
        type_invariants_opt: env.type_invariants_opt,
        ghost_blocks: env.ghost_blocks,
        track_level: env.track_level,
        timeout: env.timeout,
        local_crate_name: &local_crate_name,
        source_map: tcx.sess.source_map(),
    };

    super::proof_assert_driver::verify_proof_assert_snapshots(
        tcx,
        &host,
        &driver_ctx,
        snapshots,
        pa_counters,
    );
}
