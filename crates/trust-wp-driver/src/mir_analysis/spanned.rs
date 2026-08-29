// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Spanned expressions for MIR source location mapping.

use rustc_span::Span;
use trust_wp_core::formula::PureExpr;

/// A pure expression with MIR source location information.
///
/// This struct wraps a `PureExpr` with an optional `rustc_span::Span` from MIR,
/// enabling error messages that point to the specific source line that caused
/// a verification failure.
///
/// Unlike `SpannedExpr` in trust-wp-core (which uses `SourceSpan` for contract
/// text positions), this uses rustc's native span type for MIR-derived expressions.
#[derive(Debug, Clone)]
pub(crate) struct SpannedBodyExpr {
    /// The underlying expression
    pub(crate) expr: PureExpr,
    /// Source span from MIR (integrates with rustc's source map)
    pub(crate) span: Option<Span>,
}

impl SpannedBodyExpr {
    /// Create a new spanned expression with a span.
    pub(crate) fn new(expr: PureExpr, span: Span) -> Self {
        Self {
            expr,
            span: Some(span),
        }
    }

    /// Create a spanned expression without location info.
    pub(crate) fn unspanned(expr: PureExpr) -> Self {
        Self { expr, span: None }
    }
}

impl From<PureExpr> for SpannedBodyExpr {
    fn from(expr: PureExpr) -> Self {
        Self::unspanned(expr)
    }
}
