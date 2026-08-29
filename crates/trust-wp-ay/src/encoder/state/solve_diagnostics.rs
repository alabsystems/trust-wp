// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Solve diagnostics state: cached statistics and reason data from the last
//! `check_sat_with_details()` call. Extracted from AYEncoder to break the
//! encoder->verify bidirectional type coupling (#2655).

use crate::shared_types::{SolveStatisticsSnapshot, UnknownReason};

/// Cached diagnostic data from the most recent SMT solve call.
///
/// Cleared before each new `check_sat()` call and populated from the
/// `SolveDetails` envelope returned by ay-dpll. (#2639, #2655)
#[derive(Debug, Clone, Default)]
pub(crate) struct SolveDiagnosticsState {
    statistics: Option<SolveStatisticsSnapshot>,
    unknown_reason: Option<UnknownReason>,
    executor_error: Option<String>,
}

impl SolveDiagnosticsState {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Clear all cached diagnostics before a new solve call.
    pub(crate) fn clear(&mut self) {
        self.statistics = None;
        self.unknown_reason = None;
        self.executor_error = None;
    }

    pub(crate) fn set_statistics(&mut self, stats: SolveStatisticsSnapshot) {
        self.statistics = Some(stats);
    }

    pub(crate) fn set_unknown_reason(&mut self, reason: UnknownReason) {
        self.unknown_reason = Some(reason);
    }

    pub(crate) fn set_executor_error(&mut self, error: String) {
        self.executor_error = Some(error);
    }

    pub(crate) fn statistics(&self) -> Option<&SolveStatisticsSnapshot> {
        self.statistics.as_ref()
    }

    pub(crate) fn unknown_reason(&self) -> Option<&UnknownReason> {
        self.unknown_reason.as_ref()
    }

    pub(crate) fn executor_error(&self) -> Option<&str> {
        self.executor_error.as_deref()
    }
}
