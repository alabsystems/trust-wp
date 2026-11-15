// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The main verification loop's fail-closed panic guard (#1975).
//!
//! `verify_contracts` wraps every item's verification in `catch_unwind` so one
//! panicking function does not abort the whole crate. That containment is only
//! sound because the panic is RECORDED: `counters.panics` is the sole trace a
//! panicked item leaves, and it is what turns the run's verdict non-zero
//! (`reporting::exit_code`, `rustc_process_exit_code`, `is_assumed_only`,
//! `is_axiom_deps_only`, `summary::print_verification_summary`) and what lets
//! the trait-credit join withdraw a grant whose impl body never finished
//! (`trait_credit_join::end_item`).
//!
//! Swallowing the payload without the counter turns a crashed proof into a
//! silent pass — a crate-level FALSE ACCEPT. The guard lives in its own module
//! so that a line-budget refactor of `verification.rs` moves it instead of
//! deleting it, and so that it can be tested directly.

use crate::callbacks::{is_ay_panic_for_hook, reporting::VerificationCounters};

/// Record one item's `catch_unwind` outcome.
///
/// `Ok` is the ordinary path and does nothing. `Err` increments
/// `counters.panics` and prints the two operator-facing lines, classifying ay
/// solver panics separately (#2687) so the harness classifier can tell them
/// apart from trust-wp-side programmer errors.
///
/// ACCEPTANCE-NARROWING ONLY: this function can raise `counters.panics` and
/// can never lower any counter, so it has no path that turns a rejection into
/// an acceptance.
pub(super) fn report_verification_panic(
    def_path: &str,
    panic_result: std::thread::Result<()>,
    counters: &mut VerificationCounters,
) {
    let Err(panic_payload) = panic_result else {
        return;
    };
    let reason = ay_core::panic_payload_to_string(panic_payload.as_ref());
    counters.panics += 1;
    // Classify the panic origin (#2687): ay internal panics (sort
    // mismatches, prefetch OOB, Tseitin assertions) get a distinct
    // diagnostic message so the harness classifier can distinguish
    // them from trust-wp-side programmer errors. ay panics are expected
    // during incremental solving and do not indicate trust-wp bugs.
    if is_ay_panic_for_hook(&reason) {
        eprintln!("trust-wp: {def_path} ay solver panic during verification: {reason}");
    } else {
        eprintln!("trust-wp: {def_path} panicked during verification: {reason}");
    }
    eprintln!("  (continuing with remaining functions)");
}

/// Fault injection for the guard's own end-to-end test (debug builds only).
///
/// `TRUST_WP_PROBE_PANIC=<needle>` makes the main loop panic on every item
/// whose `def_path` contains `<needle>`, from INSIDE the `catch_unwind` the
/// guard wraps around it, standing in for the ay solver panics the guard
/// exists to contain. It is compiled out of release
/// builds, and its only effect in a debug build is to make verification of a
/// named item panic — the fail-closed direction, never an acceptance.
#[cfg(debug_assertions)]
pub(super) fn probe_panic_hook(def_path: &str) {
    if let Ok(needle) = std::env::var("TRUST_WP_PROBE_PANIC") {
        if !needle.is_empty() && def_path.contains(&needle) {
            panic!("probe injected panic");
        }
    }
}

#[cfg(not(debug_assertions))]
pub(super) fn probe_panic_hook(_def_path: &str) {}

#[cfg(test)]
mod tests {
    use super::*;

    fn caught(f: impl FnOnce()) -> std::thread::Result<()> {
        let prior = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        std::panic::set_hook(prior);
        r
    }

    #[test]
    fn ok_outcome_records_nothing() {
        let mut counters = VerificationCounters::default();
        report_verification_panic("some::item", Ok(()), &mut counters);
        assert_eq!(
            counters.panics, 0,
            "a non-panicking item must not be counted"
        );
    }

    #[test]
    fn panic_increments_the_counter() {
        let mut counters = VerificationCounters::default();
        let result = caught(|| panic!("probe injected panic"));
        report_verification_panic("some::item", result, &mut counters);
        assert_eq!(
            counters.panics, 1,
            "a panicked item must leave counters.panics as its trace"
        );
    }

    #[test]
    fn a_panicked_item_forces_a_non_zero_exit() {
        // The whole point of the counter: the run must not exit 0. The
        // policy half (`panics > 0` is an error) already has tests; what is
        // asserted here is that THIS function is what puts the crate into
        // that state.
        use crate::callbacks::reporting::{ProofAssertCounters, VerificationSummary};

        let mut counters = VerificationCounters::default();
        counters.verified = 1;
        let pa = ProofAssertCounters::default();
        assert_eq!(
            VerificationSummary::from_counters(&counters, &pa).exit_code(),
            0,
            "control: one verified function and nothing else exits 0"
        );
        let result = caught(|| panic!("probe injected panic"));
        report_verification_panic("some::item", result, &mut counters);
        assert_ne!(
            VerificationSummary::from_counters(&counters, &pa).exit_code(),
            0,
            "a panicked item must force a non-zero exit"
        );
    }

    #[test]
    fn ay_panics_are_classified_apart_from_trust_wp_panics() {
        assert!(
            is_ay_panic_for_hook("api wrapper panic: sort mismatch"),
            "the ay classification the guard branches on must still recognise ay payloads"
        );
        assert!(
            !is_ay_panic_for_hook("probe injected panic"),
            "an ordinary payload must take the `panicked during verification` branch"
        );
    }
}
