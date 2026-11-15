// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::time::Duration;

use crate::callbacks::{
    reporting::VerificationCounters,
    verification::{
        fail_fast_policy::{
            contract_added_validated_failure, should_stop_after_first_adaptive_error,
        },
        timeout_budget::AdaptiveBudget,
    },
};

fn budget(adapted: Option<Duration>, oversubscribed: bool) -> AdaptiveBudget {
    AdaptiveBudget {
        timeout: adapted,
        oversubscribed,
    }
}

#[test]
fn adaptive_fail_fast_only_when_timeout_was_reduced() {
    assert!(should_stop_after_first_adaptive_error(
        Some(Duration::from_mins(1)),
        budget(Some(Duration::from_secs(42)), true),
    ));
    assert!(!should_stop_after_first_adaptive_error(
        Some(Duration::from_mins(1)),
        budget(Some(Duration::from_mins(1)), true),
    ));
    assert!(!should_stop_after_first_adaptive_error(
        None,
        budget(None, true)
    ));
}

/// A reduced budget alone is not licence to abandon the crate: while the
/// shares still fit the crate budget the split financed every one of them, so
/// one contract burning its share says nothing about its siblings.
#[test]
fn adaptive_fail_fast_needs_an_oversubscribed_split() {
    // checked_ops: 12 verifiable functions, 17s share, 215s crate budget —
    // 204s committed, so the split pays for itself and the stop must not fire.
    assert!(!should_stop_after_first_adaptive_error(
        Some(Duration::from_secs(43)),
        budget(Some(Duration::from_secs(17)), false),
    ));
    // result/own: 18 functions held at the 15s floor — 270s committed against
    // a 215s budget, so the crate really cannot attempt them all.
    assert!(should_stop_after_first_adaptive_error(
        Some(Duration::from_secs(43)),
        budget(Some(Duration::from_secs(15)), true),
    ));
}

/// THE TEETH. A validated refutation still abandons the rest of the crate —
/// removing this is the one way D-29 could be wrong.
#[test]
fn a_validated_failure_still_stops_the_run() {
    let mut counters = VerificationCounters::default();
    assert!(!contract_added_validated_failure(&counters, 0));

    counters.failed = 1;
    assert!(!contract_added_validated_failure(&counters, 1));
    assert!(contract_added_validated_failure(&counters, 0));
}

/// A withheld refutation is not a failure: it consumed no budget and decided
/// nothing, so stopping on it would abandon every provable sibling behind it
/// (D-29).
#[test]
fn a_withheld_refutation_does_not_stop_the_run() {
    let counters = VerificationCounters {
        errors: 1,
        refutations_withheld: 1,
        ..VerificationCounters::default()
    };
    assert!(!contract_added_validated_failure(&counters, 0));
}

/// Neither does an inconclusive, a proof-trusted error, a timeout, an encoding
/// error or a panic — every one of them lands in `errors`, and none of them is
/// a statement about the user's program.
#[test]
fn no_inconclusive_stops_the_run() {
    for errors in 1..=5 {
        let counters = VerificationCounters {
            errors,
            ..VerificationCounters::default()
        };
        assert!(
            !contract_added_validated_failure(&counters, 0),
            "{errors} error(s) with no validated failure must not stop the crate"
        );
    }

    let panicked = VerificationCounters {
        errors: 1,
        panics: 1,
        ..VerificationCounters::default()
    };
    assert!(!contract_added_validated_failure(&panicked, 0));

    let demoted = VerificationCounters {
        errors: 1,
        demoted: 1,
        ..VerificationCounters::default()
    };
    assert!(!contract_added_validated_failure(&demoted, 0));
}

/// A validated failure recorded by an EARLIER contract must not stop the run
/// at this one: only the delta counts.
#[test]
fn only_this_contracts_validated_failure_counts() {
    let counters = VerificationCounters {
        failed: 1,
        errors: 3,
        ..VerificationCounters::default()
    };
    assert!(!contract_added_validated_failure(&counters, 1));
    assert!(contract_added_validated_failure(&counters, 0));
}

/// The stop is FAIL-OPEN, and that is the correct direction here: continuing
/// costs wall-clock, stopping costs unexamined obligations reported as if they
/// had been examined. Nothing it lets through can make an item pass — an
/// abandoned item was already counted unverified either way.
#[test]
fn errors_alongside_a_validated_failure_still_stop_the_run() {
    let counters = VerificationCounters {
        failed: 1,
        errors: 2,
        refutations_withheld: 1,
        ..VerificationCounters::default()
    };
    assert!(contract_added_validated_failure(&counters, 0));
}
