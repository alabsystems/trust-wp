// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Formula representation for trust-wp's pure and experimental separation-logic ASTs.
//!
//! This module defines the core types for representing:
//! - Pure expressions (heap-independent)
//! - Experimental separation-logic formulas
//! - Memory permissions (fractional)
//! - Source spans for error reporting
//!
//! # Module structure
//!
//! - `pure_expr`: Core AST types (`PureExpr`, `MatchArm`, `Pattern`)
//! - `types`: Operators, memory locations, values, permissions
//! - `internal`: Workspace-internal tuple-lowering helpers
//! - `substitute`: Variable substitution with quantifier shadowing
//! - `postcond`: Postcondition transforms for mutable refs and closures
//! - `display`: `Display` implementations for all formula types

use std::sync::Arc;

mod display;
mod float_bits;
pub mod int_bounds;
pub mod internal;
mod named_binding;
mod postcond;
mod pure_expr;
pub mod sort_intern;
mod substitute;
mod traversal;
mod types;

#[cfg(test)]
mod tests;

// Re-export the semantic AST surface.
pub use named_binding::NamedBindingValue;
pub use pure_expr::{
    reuse_arc, reuse_node, ExprSort, FloatBits, MatchArm, Pattern, PureExpr, PureExprChildRole,
};
pub use sort_intern::{intern_sort_name, resolve_sort_name};
#[doc(hidden)]
pub use substitute::expr_has_free_occurrence;
#[doc(hidden)]
pub use substitute::rename_free_var;
pub use substitute::CaptureAvoidingSubstOptions;
pub use traversal::PureExprDepthLimitedTraversalExt;
pub use types::{
    named_struct_ctor_name, parse_named_struct_ctor, BinOp, BorrowFinality, BorrowIdOrigin,
    BorrowIdStep, Location, Permission, UnOp, Value,
};

/// Placeholder value name for an indexed write (`v[i] = expr`) whose written
/// VALUE could not be translated (e.g. the value is itself an un-modeled indexed
/// read, as in `door_open[i] = !door_open[i]`). A deref `set` effect carrying this
/// value as `v@.set(i, <opaque>)` is a sound LENGTH-ONLY summary: `Seq::set` is
/// length-invariant in its value, so `len(v@.set(i, _)) == len(v@)` holds for any
/// value. Loop preservation MUST suppress the element-content fact
/// (`index_logic(updated, i) == value`) for this marker — asserting it would be
/// unsound — and emit only the length / off-index frame facts.
/// (gap nested-loop-outer-element-and-indexed-write-frame; 100doors)
pub const INDEX_MUT_OPAQUE_VALUE: &str = "__trust_wp_indexmut_opaque_value";

/// True iff `expr` is the opaque indexed-write value placeholder.
#[must_use]
pub fn is_index_mut_opaque_value(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == INDEX_MUT_OPAQUE_VALUE)
}

/// A formula in trust-wp's verification AST.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Formula {
    /// Trivially true
    True,
    /// Trivially false
    False,
    /// Pure boolean expression
    Pure(PureExpr),
    /// Points-to assertion: location ↦ value
    PointsTo {
        location: Location,
        value: Value,
        permission: Permission,
    },
    /// Mutable borrow (`RustHorn`-style prophecy encoding)
    ///
    /// Represents a mutable borrow as a (current, final, id) triple where:
    /// - `current`: The value at borrow creation
    /// - `final_val`: The prophecy of value when borrow ends
    /// - `id`: The borrow identity used to distinguish same-value reborrows
    ///
    /// This enables verification of mutable references without heap modeling,
    /// relying on Rust's ownership guarantees for disjointness.
    ///
    /// See: designs/2026-02-01-rusthorn-vs-sl.md
    MutBorrow {
        /// Variable name for the borrow
        var: String,
        /// Current value at borrow creation (corresponds to `*v`)
        current: Arc<PureExpr>,
        /// Final value when borrow ends (corresponds to `^v`)
        final_val: Arc<PureExpr>,
        /// Borrow identity value
        id: Arc<PureExpr>,
    },
    /// Separating conjunction: P * Q
    SepConj(Arc<Formula>, Arc<Formula>),
    /// Regular conjunction: P ∧ Q
    And(Arc<Formula>, Arc<Formula>),
    /// Disjunction: P ∨ Q
    Or(Arc<Formula>, Arc<Formula>),
    /// Implication: P → Q
    Implies(Arc<Formula>, Arc<Formula>),
    /// Magic wand: P -* Q
    MagicWand(Arc<Formula>, Arc<Formula>),
    /// Existential quantification: `exists<var: sort> body`
    ///
    /// Triggers: outer vec = trigger groups, inner vec = multi-patterns.
    /// Empty vec = no triggers (backward compatible).
    Exists {
        /// Bound variable name
        var: String,
        /// Optional sort for the bound variable (None defaults to Int)
        var_sort: Option<ExprSort>,
        /// Quantifier body
        body: Arc<Formula>,
        /// Optional trigger patterns for SMT instantiation control
        triggers: Vec<Vec<Formula>>,
    },
    /// Universal quantification: `forall<var: sort> body`
    ///
    /// Triggers: outer vec = trigger groups, inner vec = multi-patterns.
    /// Empty vec = no triggers (backward compatible).
    Forall {
        /// Bound variable name
        var: String,
        /// Optional sort for the bound variable (None defaults to Int)
        var_sort: Option<ExprSort>,
        /// Quantifier body
        body: Arc<Formula>,
        /// Optional trigger patterns for SMT instantiation control
        triggers: Vec<Vec<Formula>>,
    },
}

/// Source location for error reporting.
///
/// Used to map verification failures back to source code locations.
/// For contract expressions, use [`SourceSpan::from_contract`] with byte offsets
/// within the contract string. For MIR-derived expressions, use
/// [`SourceSpan::with_location`] to populate file/line/column from rustc spans.
///
/// This is the single canonical span type across all trust-wp crates (see #655).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SourceSpan {
    /// File path (if known)
    pub file: Option<String>,
    /// Start byte offset within contract string
    pub start: usize,
    /// End byte offset within contract string
    pub end: usize,
    /// Source line number (if known, 1-indexed)
    pub line: Option<u32>,
    /// Source column number (if known, 1-indexed)
    pub column: Option<u32>,
}

impl SourceSpan {
    /// Create a span from byte offsets within a contract string.
    #[must_use]
    pub fn from_contract(start: usize, end: usize) -> Self {
        Self {
            start,
            end,
            ..Default::default()
        }
    }

    /// Create a span with full location info.
    #[must_use]
    pub fn with_location(file: &str, line: u32, column: u32) -> Self {
        Self {
            file: Some(file.to_string()),
            line: Some(line),
            column: Some(column),
            ..Default::default()
        }
    }
}

/// A pure expression with optional source location.
///
/// This wrapper preserves source location information from parsing,
/// enabling better error messages that point to the specific
/// subexpression that caused a verification failure.
///
/// Use [`crate::contract_parser::parse_contract_spanned`] to parse contract
/// strings into `SpannedExpr` with source location tracking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpannedExpr {
    /// The underlying expression
    pub expr: PureExpr,
    /// Source span within contract text
    pub span: Option<SourceSpan>,
}

impl SpannedExpr {
    /// Create a new spanned expression with a span.
    #[must_use]
    pub fn new(expr: PureExpr, span: SourceSpan) -> Self {
        Self {
            expr,
            span: Some(span),
        }
    }

    /// Create a spanned expression without location info.
    #[must_use]
    pub fn unspanned(expr: PureExpr) -> Self {
        Self { expr, span: None }
    }

    /// Extract just the expression, discarding span info.
    #[must_use]
    pub fn into_expr(self) -> PureExpr {
        self.expr
    }
}

impl From<PureExpr> for SpannedExpr {
    fn from(expr: PureExpr) -> Self {
        Self::unspanned(expr)
    }
}
