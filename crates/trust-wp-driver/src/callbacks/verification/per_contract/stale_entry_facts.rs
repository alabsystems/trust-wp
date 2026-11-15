// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Entry facts a loop has invalidated, dropped from the ENSURES lane (D-38).
//!
//! A `#[requires]` clause describes the pointee of a by-reference parameter AT
//! ENTRY, and the encoder names the entry pointee and the current pointee with
//! the SAME symbol (`a_current`). A straight-line write is walked by the
//! extraction, which records the written value against that symbol; a write
//! inside a loop body is not walked at all, so without this pass the entry fact
//! survives the loop and discharges a postcondition the loop has already
//! falsified:
//!
//! ```text
//! #[requires((*a)@ == 0)]
//! #[ensures(result@ == 0)]
//! pub fn f(a: &mut u32) -> u32 {
//!     let mut i = 0u32;
//!     #[invariant(i@ <= 3)] while i < 3 { *a = 7; i += 1; }
//!     *a                              // 7 — and `verified ✓` on wp-campaign
//! }
//! ```
//!
//! The `proof_assert` lane drops the same family of facts at its own program
//! point. The two lanes differ only in that PROGRAM POINT: an assertion sits
//! at a block, and one placed BEFORE the loop correctly keeps the entry fact
//! (`s53_pa_before_loop_keeps_entry_fact_control.rs`); a postcondition is
//! checked where the function RETURNS, and no such "before" position exists
//! for it (`s59_ens_stale_param_pointee_after_loop.rs`).

use tracing::trace;
use trust_wp_core::formula::PureExpr;

use super::{
    super::super::{
        super::{contracts::FunctionContract, mir_analysis::InvalidatedEntryNames},
        parsing::{get_arg_names_from_def_id, ParsedContract},
    },
    state::SharedVerificationState,
};

/// Drop the `#[requires]`-derived entry facts that a loop may have invalidated
/// by the time this function returns. Returns how many were dropped.
///
/// `effective_requires` is laid out as
/// `[base requires][call-assumption-derived][mut-ref groundings and `inv`s]`.
/// Only the first and last partitions are touched: those are the user's entry
/// facts and the facts built from them. The call-assumption partition holds the
/// BODY's own facts — the loop write-site lane (`WriteSites`) owns those, and
/// the ones recorded for calls AFTER the loop are not stale at all.
///
/// Dropping premises can only lose a proof, never create one.
pub(super) fn drop_loop_invalidated_entry_facts(
    shared: &SharedVerificationState<'_, '_>,
    contract: &FunctionContract,
    parsed: &ParsedContract,
    def_path: &str,
    effective_requires: &mut Vec<PureExpr>,
    base_requires_count: usize,
    call_assumption_derived_count: usize,
) -> usize {
    let invalidated = loop_invalidated_param_names(shared.tcx, contract, parsed);
    if invalidated.is_empty() {
        return 0;
    }
    let call_region_end = base_requires_count.saturating_add(call_assumption_derived_count);
    let before = effective_requires.len();
    let mut index = 0usize;
    effective_requires.retain(|fact| {
        let position = index;
        index += 1;
        if position >= base_requires_count && position < call_region_end {
            return true;
        }
        !invalidated.invalidates(fact.free_vars().iter().map(String::as_str))
    });
    let dropped = before - effective_requires.len();
    if dropped > 0 {
        // `trace!`, never `eprintln!`: the goal-coverage gate parses the
        // driver's own output stream, and an unrecognised `trust-wp:` line
        // marks every item of the crate UNCOVERED: a note on stderr here costs
        // `should_succeed/bug/1562.rs` its only covered item.
        trace!(
            def_path,
            dropped,
            params = ?invalidated.params,
            unnamed = invalidated.unnamed,
            "wp-s59: entry facts dropped — a loop may write the pointee on a path to an exit"
        );
    }
    dropped
}

/// Source names of by-reference parameters whose ENTRY facts a loop may have
/// invalidated by the time this function RETURNS.
///
/// The ensures lane's program point is the function's exits, not a statement
/// inside the body. The function-level VC is one formula covering every exit, so
/// a premise stale at ANY reachable exit has to go.
///
/// Reporting a name only removes premises, so an imprecise answer costs
/// provability, never soundness. A body whose MIR is unavailable reports
/// nothing — there is then no loop analysis to act on at all — and a body with
/// no `Return` terminator reports every parameter any loop writes.
fn loop_invalidated_param_names(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    contract: &FunctionContract,
    parsed: &ParsedContract,
) -> InvalidatedEntryNames {
    let Some(body_with_facts) =
        crate::callbacks::try_get_body_with_context(tcx, contract.local_def_id)
    else {
        return InvalidatedEntryNames::default();
    };
    let body = crate::mir_analysis::get_mir_body(&body_with_facts);
    let invalidated = crate::mir_analysis::params_invalidated_by_loops_at_exits(body);
    if invalidated.is_empty() {
        return InvalidatedEntryNames::default();
    }
    let arg_names =
        get_arg_names_from_def_id(tcx, contract.def_id).unwrap_or_else(|| parsed.arg_names.clone());
    crate::mir_analysis::name_invalidated_args(
        &invalidated,
        tcx.is_closure_like(contract.def_id),
        &arg_names,
    )
}
