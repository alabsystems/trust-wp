// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! One function's verdict: every lane's credit, settled against the function's
//! own `proof_assert!`s. See `callbacks::function_credit` for the rule.

use super::{
    super::{
        super::contracts::FunctionContract,
        function_credit::{hold_function_credits, settle_function_credits, AssertionTally},
        reporting::{ProofAssertCounters, VerificationCounters},
    },
    per_contract::{verify_single_contract, SharedVerificationState},
};

/// Verify one function and report ONE verdict for it.
///
/// `verify_single_contract` runs every lane that may credit the function and
/// then, last, the in-function assertion pass. The credits are held across
/// all of it, and the assertion verdicts that pass records are exactly the
/// function's own: it walks this function's MIR only (a closure is a function
/// of its own, with its own pass). A panic anywhere in between leaves the
/// hold unsettled for the caller to discard, so a crashed function is never
/// credited.
pub(super) fn verify_function(
    shared: &SharedVerificationState<'_, '_>,
    contract: &FunctionContract,
    def_path: &str,
    counters: &mut VerificationCounters,
    pa_counters: &mut ProofAssertCounters,
) {
    hold_function_credits(counters);
    let assertions_before = AssertionTally::take(pa_counters);
    verify_single_contract(shared, contract, def_path, counters, pa_counters);
    let own = AssertionTally::take(pa_counters).since(assertions_before);
    let loc = shared
        .tcx
        .sess
        .source_map()
        .span_to_diagnostic_string(shared.tcx.def_span(contract.def_id));
    settle_function_credits(counters, contract.def_id, def_path, &loc, own);
}
