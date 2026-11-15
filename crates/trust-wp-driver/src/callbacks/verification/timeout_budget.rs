// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Crate-level timeout shaping for verification runs.

use std::{
    cell::Cell,
    collections::HashSet,
    time::{Duration, Instant},
};

use rustc_middle::ty::TyCtxt;

use crate::{
    callbacks::verification::skip_decision::{check_contract_skip, SkipDecision},
    contracts::FunctionContract,
};

/// The crate's adaptive per-function budget, plus whether the split it
/// produced actually fits inside the crate wall-clock budget.
pub(super) struct AdaptiveBudget {
    /// The per-function solver budget every contract in this crate is run with.
    pub(super) timeout: Option<Duration>,
    /// Do the per-function shares add up to MORE than the crate budget?
    ///
    /// `adaptive_timeout` divides the crate budget (5 x base) by the number of
    /// verifiable functions and then clamps the quotient UP to a 15s floor.
    /// While the quotient survives that clamp the split is SELF-FINANCING:
    /// every function may burn its whole share and the total still fits the
    /// crate budget, so one function burning its share is not evidence that
    /// the crate is about to overrun. Only the floor breaks that — once it
    /// lifts the shares above the quotient, `count x share > 5 x base` and the
    /// crate genuinely cannot afford to attempt them all.
    pub(super) oversubscribed: bool,
}

impl AdaptiveBudget {
    fn unreduced(timeout: Option<Duration>) -> Self {
        Self {
            timeout,
            oversubscribed: false,
        }
    }
}

pub(super) fn adaptive_timeout(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
    logic_fn_paths: &HashSet<String>,
    logic_fn_has_ensures: &HashSet<String>,
    timeout: Option<Duration>,
) -> AdaptiveBudget {
    let Some(base_timeout) = timeout else {
        return AdaptiveBudget::unreduced(None);
    };
    let verifiable_count = contracts
        .iter()
        .filter(|c| {
            matches!(
                check_contract_skip(tcx, c, logic_fn_paths, logic_fn_has_ensures),
                SkipDecision::Verify | SkipDecision::LogicFnEnsures
            )
        })
        .count();
    if verifiable_count <= 4 {
        // At most 4 x base, which already fits the 5 x base crate budget.
        return AdaptiveBudget::unreduced(timeout);
    }

    let total_budget_secs = base_timeout.as_secs().saturating_mul(5);
    let per_fn_secs = total_budget_secs / (verifiable_count as u64);
    // The 15s per-function floor only applies while it fits inside the crate's
    // own budget: `clamp` panics when `min > max`, which a `-t` below the floor
    // would otherwise trigger on every crate with more than four verifiable
    // functions.
    let floor_secs = 15.min(base_timeout.as_secs());
    let adapted = Duration::from_secs(per_fn_secs.clamp(floor_secs, base_timeout.as_secs()));
    let committed_secs = adapted.as_secs().saturating_mul(verifiable_count as u64);
    let oversubscribed = committed_secs > total_budget_secs;
    if adapted < base_timeout {
        eprintln!(
            "trust-wp: info: adaptive timeout: {verifiable_count} verifiable \
             functions, reducing per-function timeout from {}s to {}s \
             (crate budget: {total_budget_secs}s, committed: {committed_secs}s\
             {}) (#2674)",
            base_timeout.as_secs(),
            adapted.as_secs(),
            if oversubscribed {
                " — OVERSUBSCRIBED"
            } else {
                ""
            },
        );
    }
    AdaptiveBudget {
        timeout: Some(adapted),
        oversubscribed,
    }
}

pub(super) fn crate_wall_budget(timeout: Option<Duration>) -> Option<Duration> {
    timeout.map(|t| t.saturating_mul(5))
}

/// The wall-clock envelope ONE obligation may still occupy after it is
/// admitted: the in-process watchdog aborts a stuck solve at 1.5 x its solver
/// budget plus a grace (`trust-wp-ay`'s `hard_timeout_for`). Mirrored here so
/// the contract loop can reserve it before admitting the next function.
///
/// Without a solver budget there is no envelope to reserve (the watchdog falls
/// back to its own default) and this is zero, which restores the unreserved
/// admission rule exactly.
pub(super) fn watchdog_envelope(per_function_timeout: Option<Duration>) -> Duration {
    per_function_timeout
        .map(|t| t.saturating_add(t / 2))
        .unwrap_or_default()
}

thread_local! {
    /// The running crate's wall-clock deadline and the envelope one admitted
    /// obligation may still occupy after it.
    static CRATE_DEADLINE: Cell<Option<(Instant, Duration)>> = const { Cell::new(None) };
}

/// Publish the crate's wall-clock budget for the whole verification run.
///
/// The contract loop can check its own budget directly, but the obligations
/// that actually overrun a crate are not always contracts: a crate whose work
/// lives in `ghost!` blocks spends all of it inside ONE function's
/// proof_assert snapshots, where a per-function check can never fire. The
/// snapshot loop is several call frames down a path that carries host and
/// context structs shared by two callers, so the deadline is published for the
/// run rather than threaded through both. Restored on drop, so a nested or
/// repeated run cannot inherit a stale deadline.
#[must_use = "the deadline is cleared when the guard is dropped"]
pub(in crate::callbacks) struct CrateDeadlineGuard(Option<(Instant, Duration)>);

impl Drop for CrateDeadlineGuard {
    fn drop(&mut self) {
        CRATE_DEADLINE.with(|cell| cell.set(self.0));
    }
}

pub(in crate::callbacks) fn publish_crate_deadline(
    budget: Option<Duration>,
    start: Instant,
    reserve: Duration,
) -> CrateDeadlineGuard {
    let previous = CRATE_DEADLINE.with(|cell| cell.replace(budget.map(|b| (start + b, reserve))));
    CrateDeadlineGuard(previous)
}

/// Is there no room left to admit another obligation?
///
/// False whenever no budget was published (no `--timeout`), which leaves an
/// unbudgeted run exactly as unbounded as it was.
pub(in crate::callbacks) fn crate_budget_exhausted() -> bool {
    CRATE_DEADLINE.with(|cell| {
        cell.get()
            .is_some_and(|(deadline, reserve)| Instant::now() + reserve >= deadline)
    })
}

/// Admit the next contract, or report that the crate budget cannot afford it.
///
/// `false` means the caller must count an error and continue: a function the
/// budget declines to admit is reported against its own item and never
/// silently dropped, so the goal-coverage gate reads it as uncovered.
pub(in crate::callbacks) fn admit_within_crate_budget(def_path: &str, elapsed: Duration) -> bool {
    if !crate_budget_exhausted() {
        return true;
    }
    eprintln!(
        "trust-wp: {def_path} skipped (crate wall-clock budget exhausted: \
         {}s elapsed) (#2674)",
        elapsed.as_secs(),
    );
    false
}
