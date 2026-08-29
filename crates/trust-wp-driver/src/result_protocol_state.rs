// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Session-scoped fatal counters for the structured result protocol (#1690).
//!
//! These counters track fatal categories that were previously recoverable only
//! by brittle stderr text scans in `cargo-trust-wp`.

use std::cell::RefCell;

use trust_wp_core::result_protocol::StructuredVerificationResult;

/// Fatal categories that the driver reports separately from the base summary.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[allow(clippy::struct_field_names)] // all fields are error counters — shared suffix is domain-correct
pub(crate) struct FatalResultCounters {
    pub(crate) parse_errors: u64,
    pub(crate) termination_errors: u64,
    pub(crate) logic_recursion_errors: u64,
    pub(crate) erasure_errors: u64,
}

impl FatalResultCounters {
    /// Overlay fatal counters onto an existing structured result record.
    pub(crate) fn merge_into(self, result: &mut StructuredVerificationResult) {
        result.parse_errors = self.parse_errors;
        result.termination_errors = self.termination_errors;
        result.logic_recursion_errors = self.logic_recursion_errors;
        result.erasure_errors = self.erasure_errors;
    }

    /// Build a result record for early-stop paths that do not have a summary.
    pub(crate) fn into_structured_result(
        self,
        base_exit_code: i32,
    ) -> StructuredVerificationResult {
        let mut result = StructuredVerificationResult {
            base_exit_code,
            ..Default::default()
        };
        self.merge_into(&mut result);
        result
    }
}

thread_local! {
    static FATAL_RESULT_COUNTERS: RefCell<FatalResultCounters> =
        RefCell::new(FatalResultCounters::default());
}

/// Clear counters between compiler invocations.
pub(crate) fn clear_fatal_result_counters() {
    FATAL_RESULT_COUNTERS.with(|state| {
        *state.borrow_mut() = FatalResultCounters::default();
    });
}

/// Snapshot the current fatal counters for protocol emission.
pub(crate) fn snapshot_fatal_result_counters() -> FatalResultCounters {
    FATAL_RESULT_COUNTERS.with(|state| *state.borrow())
}

/// Record a parse error that should map to wrapper exit code 3.
pub(crate) fn record_parse_error() {
    FATAL_RESULT_COUNTERS.with(|state| {
        state.borrow_mut().parse_errors += 1;
    });
}

/// Record a termination-check error that should map to wrapper exit code 2.
pub(crate) fn record_termination_error() {
    FATAL_RESULT_COUNTERS.with(|state| {
        state.borrow_mut().termination_errors += 1;
    });
}

/// Record a logic-recursion error that should map to wrapper exit code 2.
pub(crate) fn record_logic_recursion_error() {
    FATAL_RESULT_COUNTERS.with(|state| {
        state.borrow_mut().logic_recursion_errors += 1;
    });
}

/// Record an `#[erasure(target)]` validation error that should map to wrapper exit code 2.
///
/// Phase 5c (THIR-level equivalence scaffold): incremented when a function
/// carrying `#[erasure(target)]` fails the driver-side validity check applied
/// to the (lhs, rhs) pair discovered from doc markers. See
/// `crates/trust-wp-driver/src/callbacks/discovery/erasure.rs` for the precise
/// list of checks (vs. what is deferred for full Creusot parity).
pub(crate) fn record_erasure_error() {
    FATAL_RESULT_COUNTERS.with(|state| {
        state.borrow_mut().erasure_errors += 1;
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clear_resets_all_fatal_counters() {
        clear_fatal_result_counters();
        record_parse_error();
        record_termination_error();
        record_logic_recursion_error();
        record_erasure_error();

        clear_fatal_result_counters();

        assert_eq!(
            snapshot_fatal_result_counters(),
            FatalResultCounters::default()
        );
    }

    #[test]
    fn into_structured_result_preserves_fatal_counts() {
        let counters = FatalResultCounters {
            parse_errors: 2,
            termination_errors: 3,
            logic_recursion_errors: 4,
            erasure_errors: 5,
        };

        let result = counters.into_structured_result(2);

        assert_eq!(result.base_exit_code, 2);
        assert_eq!(result.parse_errors, 2);
        assert_eq!(result.termination_errors, 3);
        assert_eq!(result.logic_recursion_errors, 4);
        assert_eq!(result.erasure_errors, 5);
    }

    #[test]
    fn record_erasure_error_increments_counter() {
        clear_fatal_result_counters();
        record_erasure_error();
        record_erasure_error();
        assert_eq!(snapshot_fatal_result_counters().erasure_errors, 2);
        clear_fatal_result_counters();
    }
}
