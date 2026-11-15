// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Encoding-error subtype breakdown for driver-side fail triage (#2015).
//!
//! Provides a shared callbacks-local taxonomy that records which
//! `EncodingError` variant caused each `errors += 1` increment.
//! The breakdown is strict subset telemetry — it never replaces the
//! aggregate `errors` counter but adds per-variant attribution.

use trust_wp_ay::EncodingError;

/// Per-variant counts for `EncodingError` subtypes.
///
/// Every field is a strict subset of the aggregate `errors` counter
/// in the parent counter struct. The sum of all fields may be less
/// than `errors` because non-`EncodingError` error paths (Unknown,
/// parse/setup failures, non-exhaustive fallbacks) only increment
/// the aggregate counter.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct EncodingErrorBreakdown {
    pub unsupported: usize,
    pub sort_inference: usize,
    pub solver: usize,
}

impl EncodingErrorBreakdown {
    /// Record one `EncodingError` by dispatching on its variant.
    pub(crate) fn record(&mut self, err: &EncodingError) {
        match err {
            EncodingError::Unsupported { .. } => self.unsupported += 1,
            EncodingError::SortInference { .. } => self.sort_inference += 1,
            EncodingError::SolverError { .. } => self.solver += 1,
            // EncodingError is #[non_exhaustive]; future variants go to
            // the aggregate `errors` counter only — no silent data loss.
            #[allow(unreachable_patterns)]
            _ => {}
        }
    }

    /// Merge another breakdown into this one (for summary aggregation).
    pub(crate) fn merge_from(&mut self, other: &Self) {
        self.unsupported = self.unsupported.saturating_add(other.unsupported);
        self.sort_inference = self.sort_inference.saturating_add(other.sort_inference);
        self.solver = self.solver.saturating_add(other.solver);
    }

    /// Returns `true` when no encoding-error subtypes have been recorded.
    pub(crate) fn is_empty(&self) -> bool {
        self.unsupported == 0 && self.sort_inference == 0 && self.solver == 0
    }

    /// Format the parser-safe summary suffix.
    ///
    /// Returns `None` when no subtypes have been recorded, `Some(...)` with
    /// the format `encoding-errors unsupported=U sort-inference=S solver=E`
    /// otherwise. The caller appends this as an extra comma-delimited part
    /// after the mandatory `N errors` field.
    pub(crate) fn format_suffix(&self) -> Option<String> {
        if self.is_empty() {
            return None;
        }
        Some(format!(
            "encoding-errors unsupported={} sort-inference={} solver={}",
            self.unsupported, self.sort_inference, self.solver
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_by_default() {
        let b = EncodingErrorBreakdown::default();
        assert!(b.is_empty());
        assert_eq!(b.format_suffix(), None);
    }

    #[test]
    fn record_unsupported() {
        let mut b = EncodingErrorBreakdown::default();
        let err = EncodingError::Unsupported {
            message: "test".into(),
            span: None,
            contract_text: None,
        };
        b.record(&err);
        assert_eq!(b.unsupported, 1);
        assert_eq!(b.sort_inference, 0);
        assert_eq!(b.solver, 0);
        assert!(!b.is_empty());
    }

    #[test]
    fn record_sort_inference() {
        let mut b = EncodingErrorBreakdown::default();
        let err = EncodingError::SortInference {
            context: "test".into(),
            detail: "detail".into(),
            span: None,
        };
        b.record(&err);
        assert_eq!(b.unsupported, 0);
        assert_eq!(b.sort_inference, 1);
        assert_eq!(b.solver, 0);
    }

    #[test]
    fn record_solver_error() {
        let mut b = EncodingErrorBreakdown::default();
        let err = EncodingError::SolverError {
            message: "test".into(),
            span: None,
        };
        b.record(&err);
        assert_eq!(b.unsupported, 0);
        assert_eq!(b.sort_inference, 0);
        assert_eq!(b.solver, 1);
    }

    #[test]
    fn merge_from_accumulates() {
        let mut a = EncodingErrorBreakdown {
            unsupported: 1,
            sort_inference: 2,
            solver: 0,
        };
        let b = EncodingErrorBreakdown {
            unsupported: 3,
            sort_inference: 0,
            solver: 4,
        };
        a.merge_from(&b);
        assert_eq!(a.unsupported, 4);
        assert_eq!(a.sort_inference, 2);
        assert_eq!(a.solver, 4);
    }

    #[test]
    fn format_suffix_when_nonempty() {
        let b = EncodingErrorBreakdown {
            unsupported: 3,
            sort_inference: 4,
            solver: 1,
        };
        assert_eq!(
            b.format_suffix(),
            Some("encoding-errors unsupported=3 sort-inference=4 solver=1".to_string())
        );
    }
}
