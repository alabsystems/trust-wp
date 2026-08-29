// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Crate-level timeout shaping for verification runs.

use std::{collections::HashSet, time::Duration};

use rustc_middle::ty::TyCtxt;

use crate::{
    callbacks::verification::skip_decision::{check_contract_skip, SkipDecision},
    contracts::FunctionContract,
};

pub(super) fn adaptive_timeout(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
    logic_fn_paths: &HashSet<String>,
    logic_fn_has_ensures: &HashSet<String>,
    timeout: Option<Duration>,
) -> Option<Duration> {
    let base_timeout = timeout?;
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
        return timeout;
    }

    let total_budget_secs = base_timeout.as_secs().saturating_mul(5);
    let per_fn_secs = total_budget_secs / (verifiable_count as u64);
    // The 15s per-function floor only applies while it fits inside the crate's
    // own budget: `clamp` panics when `min > max`, which a `-t` below the floor
    // would otherwise trigger on every crate with more than four verifiable
    // functions.
    let floor_secs = 15.min(base_timeout.as_secs());
    let adapted = Duration::from_secs(per_fn_secs.clamp(floor_secs, base_timeout.as_secs()));
    if adapted < base_timeout {
        eprintln!(
            "trust-wp: info: adaptive timeout: {verifiable_count} verifiable \
             functions, reducing per-function timeout from {}s to {}s \
             (crate budget: {total_budget_secs}s) (#2674)",
            base_timeout.as_secs(),
            adapted.as_secs(),
        );
    }
    Some(adapted)
}

pub(super) fn crate_wall_budget(timeout: Option<Duration>) -> Option<Duration> {
    timeout.map(|t| t.saturating_mul(5))
}
