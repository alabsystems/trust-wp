// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The #3771 adaptive-budget fail-fast policy: when may one contract's result
//! abandon the rest of the crate?
//!
//! Kept apart from the root module so the predicates and what the loop still
//! verifies once the stop fires carry their reasoning next to each other, and
//! the root module stays inside its LOC budget.

use std::{collections::HashMap, time::Duration};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use trust_wp_driver::StdSpec;

use super::{super::reporting::VerificationCounters, trait_credit_join::owed_trait_contract};

/// May one contract's failure abandon the rest of the crate?
///
/// The stop exists to protect the crate wall-clock budget, so it is only
/// justified where the budget is actually at risk. `adaptive_timeout` splits
/// that budget (5 x base) across the verifiable functions; while the quotient
/// survives the 15s floor the split is SELF-FINANCING — `count x share <=
/// 5 x base` — and every function burning its whole share is exactly what the
/// split already paid for. A function that times out there is spending the
/// share allotted to it, not overdrawing the crate, so it is no evidence at
/// all about the siblings behind it.
///
/// Stopping on such a timeout abandons every sibling behind it: on
/// `checked_ops` one function timing out at its own share leaves the rest of
/// the row's Creusot goal-bearing items unreported.
///
/// So the stop needs `oversubscribed` too (D-29): the floor lifted the shares
/// above the quotient, the crate cannot afford to attempt them all, and a
/// contract that just consumed a share is evidence of the overrun. The
/// loop-top crate wall-clock check remains the MEASURED backstop in every
/// case, and it reports each function it cannot afford as an error — so
/// declining to stop here never turns an unexamined obligation into a pass.
pub(super) fn should_stop_after_first_adaptive_error(
    base_timeout: Option<Duration>,
    adaptive: super::timeout_budget::AdaptiveBudget,
) -> bool {
    adaptive.oversubscribed
        && matches!(
            (base_timeout, adaptive.timeout),
            (Some(base), Some(adapted)) if adapted < base
        )
}

/// Did this contract produce a result that justifies abandoning the rest of the
/// crate under a reduced adaptive budget?
///
/// Exactly one thing does: a **validated FAILED**. Nothing else.
///
/// The stop exists to protect the crate wall budget, on the theory that a
/// contract which failed or errored is evidence the remaining ones will not fit
/// either. For a refutation that is at least arguable. For everything else it
/// is not true, and stopping on it hides real proofs:
///
/// * an INCONCLUSIVE consumes no budget and decides nothing;
/// * a refutation WITHHELD for want of a validated model, or for refuting a
///   `false` trust-wp itself injected (D-27), is not a failure at all;
/// * a proof-TRUSTED error is a proof ay could not render into the pinned
///   calculus, not a defect in the user's program;
/// * a TIMEOUT is the one case where the budget theory sounds right and is
///   most wrong: the per-item budget already expired, so the item has stopped
///   spending, and stopping the crate buys nothing but silence.
///
/// Stopping on anything weaker hides every contract behind a single
/// inconclusive item (`bug/final_borrows` after `index_mut_slice`, for one).
///
/// `counters.failed` is the right signal because a `Failed` cannot reach it
/// unvalidated: every lane that increments it takes its verdict from an ay
/// public boundary, and both boundaries run the refutation-authority gates
/// (`apply_mandatory_refutation_authority`,
/// `apply_injected_goal_refutation_authority`) before returning. The two
/// exceptions are decidable structural determinations, not solver claims — a
/// structural variant that provably does not decrease, and a literal
/// user-authored `#[ensures(false)]` — and both are genuine failures.
///
/// FAIL-OPEN ON PURPOSE, and this is the one place in the driver where that is
/// the correct direction: the cost of continuing is wall-clock, and the cost of
/// stopping is unexamined obligations reported as if they had been examined.
/// Nothing here can make an item PASS — every abandoned item was already
/// counted as unverified.
pub(super) fn contract_added_validated_failure(
    counters: &VerificationCounters,
    prior_failed: usize,
) -> bool {
    counters.failed > prior_failed
}

/// The stop, once fired: which contracts the loop still verifies.
///
/// The stop gives up an item's OWN verdict, which is all most items owe. An
/// implementation of a contracted trait method owes more: every caller handed
/// the trait contract rests on it, and one left unexamined pays for nothing
/// (trait_impl_unexamined_after_fail_fast_stop.rs, D-94). So after the stop
/// the loop still verifies those, under the same crate wall-clock admission as
/// before, and passes over everything else.
#[derive(Default)]
pub(super) struct AdaptiveStop {
    fired: bool,
}

impl AdaptiveStop {
    /// Whether the loop passes over `def_id` without examining it.
    pub(super) fn passes_over(
        &self,
        tcx: TyCtxt<'_>,
        trait_specs: &HashMap<DefId, StdSpec>,
        def_id: DefId,
    ) -> bool {
        self.fired && owed_trait_contract(tcx, trait_specs, def_id).is_none()
    }

    /// Fire the stop, once, when it is `enabled` for this crate and the
    /// contract just verified added a validated failure.
    pub(super) fn after_contract(
        &mut self,
        enabled: bool,
        counters: &VerificationCounters,
        prior_failed: usize,
    ) {
        if !self.fired && enabled && contract_added_validated_failure(counters, prior_failed) {
            eprintln!(
                "trust-wp: stopping remaining contract verification after first \
                 adaptive-budget VALIDATED failure (#3771); implementations of \
                 contracted trait methods are still verified"
            );
            self.fired = true;
        }
    }
}
