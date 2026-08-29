// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::time::Duration;

use crate::callbacks::{
    reporting::VerificationCounters,
    verification::{contract_added_failure_or_error, should_stop_after_first_adaptive_error},
};

#[test]
fn adaptive_fail_fast_only_when_timeout_was_reduced() {
    assert!(should_stop_after_first_adaptive_error(
        Some(Duration::from_mins(1)),
        Some(Duration::from_secs(42)),
    ));
    assert!(!should_stop_after_first_adaptive_error(
        Some(Duration::from_mins(1)),
        Some(Duration::from_mins(1)),
    ));
    assert!(!should_stop_after_first_adaptive_error(None, None));
}

#[test]
fn contract_delta_detects_new_failure_or_error() {
    let mut counters = VerificationCounters::default();
    assert!(!contract_added_failure_or_error(&counters, 0, 0));

    counters.errors = 1;
    assert!(contract_added_failure_or_error(&counters, 0, 0));
    assert!(!contract_added_failure_or_error(&counters, 0, 1));

    counters.failed = 1;
    assert!(contract_added_failure_or_error(&counters, 0, 1));
}
