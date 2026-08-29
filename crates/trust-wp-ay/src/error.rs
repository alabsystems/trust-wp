// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Error types for trust-wp-ay encoding.
//!
//! This module defines errors that can occur during formula encoding
//! and verification.
//!
//! # Key Types
//!
//! - [`EncodingError`]: Main error type for encoding failures
//!
//! # Error Categories
//!
//! - `Unsupported`: Formula uses a feature not yet implemented
//! - `SolverError`: ay solver encountered an internal error
//!
//! # See Also
//!
//! - [`crate::span::SourceSpan`]: Location info for error reporting

use crate::span::SourceSpan;

/// Errors that can occur during encoding
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum EncodingError {
    /// Unsupported formula construct
    #[error("{}", format_unsupported_error(.message, .span.as_ref(), .contract_text.as_ref()))]
    Unsupported {
        /// Description of what's unsupported
        message: String,
        /// Source location (if known)
        span: Option<SourceSpan>,
        /// Original contract text (for error context)
        contract_text: Option<String>,
    },

    /// Sort inference failure — a sort could not be resolved and no sound
    /// default exists. Replaces silent `Sort::Int` fallbacks (#1608).
    #[error("{}", format_sort_inference_error(.context, .detail, .span.as_ref()))]
    SortInference {
        /// Where the sort was needed (e.g., "logic_fn_placeholder:foo param 0")
        context: String,
        /// What went wrong
        detail: String,
        /// Source location (if known)
        span: Option<SourceSpan>,
    },

    /// Sort conflict — a variable or term was requested with an incompatible
    /// sort after already being established with a different one.
    #[error(
        "{}",
        format_sort_conflict_error(
            .context,
            .declared_sort,
            .requested_sort,
            .span.as_ref()
        )
    )]
    SortConflict {
        /// Where the conflict happened (for example "variable 'x'")
        context: String,
        /// The sort already associated with the context
        declared_sort: String,
        /// The incompatible sort that was requested
        requested_sort: String,
        /// Source location (if known)
        span: Option<SourceSpan>,
    },

    /// AY solver error
    #[error("{}", format_solver_error(.message, .span.as_ref()))]
    SolverError {
        /// Error message from the solver
        message: String,
        /// Source location (if known)
        span: Option<SourceSpan>,
    },
}

fn format_unsupported_error(
    message: &str,
    span: Option<&SourceSpan>,
    contract_text: Option<&String>,
) -> String {
    use std::fmt::Write;
    let mut result = format!("unsupported formula: {message}");
    if let Some(s) = span {
        if let (Some(file), Some(line)) = (&s.file, s.line) {
            let _ = write!(result, "\n  --> {file}:{line}");
            if let Some(col) = s.column {
                let _ = write!(result, ":{col}");
            }
        }
    }
    if let Some(text) = contract_text {
        let _ = write!(result, "\n  contract: {text}");
    }
    result
}

fn format_sort_inference_error(context: &str, detail: &str, span: Option<&SourceSpan>) -> String {
    use std::fmt::Write;
    let mut result = format!("sort inference failed: {context} — {detail}");
    if let Some(s) = span {
        if let (Some(file), Some(line)) = (&s.file, s.line) {
            let _ = write!(result, "\n  --> {file}:{line}");
            if let Some(col) = s.column {
                let _ = write!(result, ":{col}");
            }
        }
    }
    result
}

fn format_sort_conflict_error(
    context: &str,
    declared_sort: &str,
    requested_sort: &str,
    span: Option<&SourceSpan>,
) -> String {
    use std::fmt::Write;
    let mut result = format!(
        "sort conflict: {context}: declared as {declared_sort}, requested as {requested_sort}"
    );
    if let Some(s) = span {
        if let (Some(file), Some(line)) = (&s.file, s.line) {
            let _ = write!(result, "\n  --> {file}:{line}");
            if let Some(col) = s.column {
                let _ = write!(result, ":{col}");
            }
        }
    }
    result
}

fn format_solver_error(message: &str, span: Option<&SourceSpan>) -> String {
    use std::fmt::Write;
    let mut result = format!("ay error: {message}");
    if let Some(s) = span {
        if let (Some(file), Some(line)) = (&s.file, s.line) {
            let _ = write!(result, "\n  --> {file}:{line}");
            if let Some(col) = s.column {
                let _ = write!(result, ":{col}");
            }
        }
    }
    result
}

/// A ay solver panic caught by the panic-isolation boundary.
///
/// Returned by [`crate::encoder::type_resolve::catch_solver_panic_with_reason`]
/// when ay panics during a solver operation (sort mismatch, internal assertion
/// failure, etc.). Callers decide how to handle the error — there is no
/// implicit fallback value. (#903, #1663)
#[derive(Debug, thiserror::Error)]
pub(crate) enum SolverPanicError {
    /// ay panicked during the named operation.
    #[error("ay solver panic during {operation}: {reason}")]
    Panic {
        /// The operation that triggered the panic (e.g., "check_sat", "eq_term").
        operation: String,
        /// The panic reason extracted from ay.
        reason: String,
    },
}

impl SolverPanicError {
    /// Consume the error and return the panic reason string.
    ///
    /// Useful for passing to `record_solver_panic()` which stores a `String`.
    pub(crate) fn into_reason(self) -> String {
        match self {
            Self::Panic { reason, .. } => reason,
        }
    }

    /// Borrow the panic reason string.
    pub(crate) fn reason(&self) -> &str {
        match self {
            Self::Panic { reason, .. } => reason,
        }
    }
}

/// Error from a vacuity check via unsat-core inspection.
///
/// Returned by [`crate::encoder::AYEncoder::is_vacuous_unsat`] when the
/// unsat-core retrieval fails (e.g., no UNSAT result to extract a core from).
/// (#903, #2414)
#[derive(Debug, thiserror::Error)]
pub(crate) enum VacuityCheckError {
    /// The unsat-core could not be retrieved from the solver.
    #[error("vacuity check failed: unsat core retrieval error: {message}")]
    UnsatCoreRetrieval {
        /// The error message from `try_get_unsat_core()`.
        message: String,
    },
}

impl EncodingError {
    /// Create an unsupported error with just a message (no span info).
    ///
    /// Increments the `UnsupportedConstructSkip` unsoundness counter (#2206).
    pub fn unsupported(message: impl Into<String>) -> Self {
        crate::encoder::unsoundness::increment(
            crate::encoder::unsoundness::UnsoundnessCategory::UnsupportedConstructSkip,
        );
        Self::Unsupported {
            message: message.into(),
            span: None,
            contract_text: None,
        }
    }

    /// Create an unsupported error with span information.
    ///
    /// Increments the `UnsupportedConstructSkip` unsoundness counter (#2206).
    pub fn unsupported_with_span(message: impl Into<String>, span: SourceSpan) -> Self {
        crate::encoder::unsoundness::increment(
            crate::encoder::unsoundness::UnsoundnessCategory::UnsupportedConstructSkip,
        );
        Self::Unsupported {
            message: message.into(),
            span: Some(span),
            contract_text: None,
        }
    }

    /// Create an unsupported error with full context.
    ///
    /// Increments the `UnsupportedConstructSkip` unsoundness counter (#2206).
    pub fn unsupported_with_context(
        message: impl Into<String>,
        span: Option<SourceSpan>,
        contract_text: Option<String>,
    ) -> Self {
        crate::encoder::unsoundness::increment(
            crate::encoder::unsoundness::UnsoundnessCategory::UnsupportedConstructSkip,
        );
        Self::Unsupported {
            message: message.into(),
            span,
            contract_text,
        }
    }

    /// Create a sort inference error.
    pub fn sort_inference(context: impl Into<String>, detail: impl Into<String>) -> Self {
        Self::SortInference {
            context: context.into(),
            detail: detail.into(),
            span: None,
        }
    }

    /// Create a sort conflict error.
    pub fn sort_conflict(
        context: impl Into<String>,
        declared_sort: impl Into<String>,
        requested_sort: impl Into<String>,
    ) -> Self {
        Self::SortConflict {
            context: context.into(),
            declared_sort: declared_sort.into(),
            requested_sort: requested_sort.into(),
            span: None,
        }
    }

    /// Create a solver error with just a message.
    pub fn solver_error(message: impl Into<String>) -> Self {
        Self::SolverError {
            message: message.into(),
            span: None,
        }
    }

    /// Create a solver error with span information.
    pub fn solver_error_with_span(message: impl Into<String>, span: SourceSpan) -> Self {
        Self::SolverError {
            message: message.into(),
            span: Some(span),
        }
    }

    /// Attach a source span to an existing error.
    ///
    /// Useful for the driver layer, which knows the source location from
    /// rustc but catches errors from the span-unaware encoder layer.
    #[must_use]
    pub fn with_span(self, span: SourceSpan) -> Self {
        match self {
            Self::Unsupported {
                message,
                contract_text,
                ..
            } => Self::Unsupported {
                message,
                span: Some(span),
                contract_text,
            },
            Self::SolverError { message, .. } => Self::SolverError {
                message,
                span: Some(span),
            },
            Self::SortInference {
                context, detail, ..
            } => Self::SortInference {
                context,
                detail,
                span: Some(span),
            },
            Self::SortConflict {
                context,
                declared_sort,
                requested_sort,
                ..
            } => Self::SortConflict {
                context,
                declared_sort,
                requested_sort,
                span: Some(span),
            },
        }
    }
}
