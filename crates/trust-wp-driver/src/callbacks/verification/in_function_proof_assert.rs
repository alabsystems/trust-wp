// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! In-function proof_assert verification for functions with explicit contracts.
//!
//! When a function has both contracts (`#[requires]`/`#[ensures]`) AND `proof_assert!`
//! calls, the contract verification happens first (in the main loop), and then this
//! module verifies each proof_assert in that function's MIR body. Extracted from
//! `verification.rs` (#1526).
//!
//! Contrast with `standalone_proof_assert.rs`, which handles functions that have
//! proof_assert! but NO explicit contracts.

use std::collections::HashMap;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::source_map::SourceMap;
use tracing::trace;
use trust_wp_core::{
    logic::{LogicFnDef, TypeInvariantDef},
    TrackLevel,
};
use trust_wp_driver::StdSpec;

use super::super::{
    super::{
        contracts::FunctionContract,
        ghost::GhostBlock,
        mir_analysis::{get_mir_body, MutBorrowBody},
        proof_assert::find_proof_asserts_in_mir,
    },
    proof_assert_snapshot::build_assertion_snapshots_for_function,
    reporting::ProofAssertCounters,
    try_get_body_with_context,
};

/// Context for verifying proof_asserts within a function that has explicit contracts.
pub(in crate::callbacks) struct InFunctionProofAssertContext<'a> {
    pub(in crate::callbacks) contract: &'a FunctionContract,
    pub(in crate::callbacks) arg_names: &'a [String],
    pub(in crate::callbacks) loop_spans: &'a [(u32, u32)],
    pub(in crate::callbacks) loop_exit_assumptions: Option<&'a [trust_wp_core::formula::PureExpr]>,
    pub(in crate::callbacks) ghost_blocks: &'a [GhostBlock],
    pub(in crate::callbacks) user_specs: &'a HashMap<DefId, StdSpec>,
    pub(in crate::callbacks) trait_specs: &'a HashMap<DefId, StdSpec>,
    pub(in crate::callbacks) extern_specs: &'a HashMap<String, StdSpec>,
    pub(in crate::callbacks) mut_borrow_body: Option<&'a MutBorrowBody>,
    /// Caller-side expiry pins proven for this body (#prophecy-slots M6).
    /// Supplied by the contract extraction that already ran for this function.
    pub(in crate::callbacks) projected_final_pins:
        &'a [trust_wp_core::formula::ProjectedFinalPin],
    pub(in crate::callbacks) pa_setup: &'a super::super::proof_assert_verify::ProofAssertSetup<'a>,
    pub(in crate::callbacks) pa_ctx: &'a super::super::verification_context::ProofAssertContext<'a>,
    pub(in crate::callbacks) pa_logic_fns_opt: Option<&'a [LogicFnDef]>,
    pub(in crate::callbacks) type_invariants_opt: Option<&'a [TypeInvariantDef]>,
    pub(in crate::callbacks) local_crate_name: &'a str,
    pub(in crate::callbacks) source_map: &'a SourceMap,
    pub(in crate::callbacks) track_level: TrackLevel,
    pub(in crate::callbacks) timeout: Option<std::time::Duration>,
    pub(in crate::callbacks) def_path: &'a str,
}

/// Verify proof_asserts in a function's MIR body (#1572).
///
/// Detects `proof_assert!` calls in the function's MIR, builds assertion snapshots,
/// and delegates per-snapshot verification to the shared driver. Updates
/// `pa_counters` with results.
pub(in crate::callbacks) fn verify_in_function_proof_asserts(
    tcx: TyCtxt<'_>,
    ctx: &InFunctionProofAssertContext<'_>,
    pa_counters: &mut ProofAssertCounters,
) {
    let Some(body_with_facts) = try_get_body_with_context(tcx, ctx.contract.local_def_id) else {
        return;
    };
    let mir_body = get_mir_body(&body_with_facts);
    let fn_proof_asserts = find_proof_asserts_in_mir(tcx, mir_body, ctx.contract.local_def_id);
    if fn_proof_asserts.is_empty() {
        return;
    }

    trace!(
        count = fn_proof_asserts.len(),
        def_path = %ctx.def_path,
        "proof_assert(s) detected",
    );

    let snapshots = build_assertion_snapshots_for_function(
        tcx,
        &fn_proof_asserts,
        ctx.ghost_blocks,
        &ctx.pa_setup.user_specs,
        ctx.pa_ctx,
        ctx.local_crate_name,
    );

    let host = super::proof_assert_driver::ProofAssertHost::Contracted {
        contract: ctx.contract,
        arg_names: ctx.arg_names,
        user_specs: ctx.user_specs,
        trait_specs: ctx.trait_specs,
        extern_specs: ctx.extern_specs,
        mut_borrow_body: ctx.mut_borrow_body,
        projected_final_pins: ctx.projected_final_pins,
        loop_spans: ctx.loop_spans,
        loop_exit_assumptions: ctx.loop_exit_assumptions,
        def_path: ctx.def_path,
    };
    let driver_ctx = super::proof_assert_driver::ProofAssertDriverContext {
        pa_setup: ctx.pa_setup,
        pa_ctx: ctx.pa_ctx,
        pa_logic_fns_opt: ctx.pa_logic_fns_opt,
        type_invariants_opt: ctx.type_invariants_opt,
        ghost_blocks: ctx.ghost_blocks,
        track_level: ctx.track_level,
        timeout: ctx.timeout,
        local_crate_name: ctx.local_crate_name,
        source_map: ctx.source_map,
    };

    super::proof_assert_driver::verify_proof_assert_snapshots(
        tcx,
        &host,
        &driver_ctx,
        snapshots,
        pa_counters,
    );
}
