// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MIR-level proof assertion detection for the trust-wp driver.
//!
//! Detects `proof_assert!` macro invocations via MIR closure aggregates
//! with `#[doc = "trust-wp:proof_assert:"]` marker attributes.
//!
//! # Detection
//!
//! `find_proof_asserts_in_mir()` walks MIR basic blocks looking for
//! `Rvalue::Aggregate(AggregateKind::Closure(def_id, _), _)` where the
//! closure's DefId carries the proof_assert doc marker. This provides:
//! - Precise `Location`-based cutoff (not span-based)
//! - Compiler `SourceScope` for variable resolution
//! - Implicit path conditions via MIR CFG
//!
//! # Verification
//!
//! Each detected `proof_assert!(expr)` becomes a verification obligation:
//! the driver must prove that `expr` holds at that program point given
//! the function's preconditions and preceding code. Verification is
//! performed inline in `verify_contracts` (Phase 4, #1572).

use log::debug;
use rustc_hir::{def_id::LocalDefId, HirId};
use rustc_middle::{
    mir::{self, Body, Location, Rvalue, SourceScope, StatementKind},
    ty::TyCtxt,
};
use rustc_span::{def_id::DefId, Span};

/// Information about a detected proof assertion.
#[derive(Debug, Clone)]
pub(crate) struct ProofAssert {
    /// Span of the proof_assert! for error reporting
    pub(crate) span: Span,
    /// The containing function's LocalDefId
    pub(crate) containing_fn: LocalDefId,
    /// The assertion expression as a string (for debugging/display)
    pub(crate) expr_text: Option<String>,
    /// Whether this assertion came from `#[trusted] proof_assert!(...)`.
    pub(crate) trusted: bool,
    /// The assertion closure's DefId.
    ///
    /// Identifies the closure in MIR. Used to look up the closure's captures
    /// (for variable resolution) and its source span.
    pub(crate) closure_def_id: Option<DefId>,
    /// The MIR `SourceScope` at the assertion point.
    ///
    /// Used for variable resolution via `visible_locals_at_scope()`.
    pub(crate) source_scope: Option<SourceScope>,
    /// The MIR location (BasicBlock + statement index) of the assertion.
    ///
    /// Used to determine what MIR statements precede the assertion.
    pub(crate) location: Option<Location>,
}

/// Find proof assertions in a single function's MIR body.
///
/// Walks all statements in all basic blocks looking for
/// `Rvalue::Aggregate(AggregateKind::Closure(def_id, _), _)` where `def_id`
/// has the `trust-wp:proof_assert` doc attribute. Returns assertions sorted by
/// MIR location.
pub(crate) fn find_proof_asserts_in_mir(
    tcx: TyCtxt<'_>,
    body: &Body<'_>,
    containing_fn: LocalDefId,
) -> Vec<ProofAssert> {
    let mut asserts = Vec::new();

    for (bb_idx, bb_data) in body.basic_blocks.iter_enumerated() {
        for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
            let closure_def_id = match stmt.kind {
                StatementKind::Assign(box (
                    _,
                    Rvalue::Aggregate(box mir::AggregateKind::Closure(def_id, _), _),
                )) => Some(def_id),
                _ => None,
            };

            let Some(closure_def_id) = closure_def_id else {
                continue;
            };

            // Check if this closure has the proof_assert doc marker
            let Some((expr_text, trusted)) =
                get_proof_assert_expr_text_from_def_id(tcx, closure_def_id)
            else {
                continue;
            };

            let fn_path = tcx.def_path_str(containing_fn);
            debug!("MIR: Found proof_assert! in {fn_path} at {bb_idx:?}[{stmt_idx}]: {expr_text}");

            asserts.push(ProofAssert {
                span: stmt.source_info.span,
                containing_fn,
                expr_text: Some(expr_text),
                trusted,
                closure_def_id: Some(closure_def_id),
                source_scope: Some(stmt.source_info.scope),
                location: Some(Location {
                    block: bb_idx,
                    statement_index: stmt_idx,
                }),
            });
        }
    }

    // Sort by location for deterministic ordering
    asserts.sort_by_key(|a| a.location);
    asserts
}

/// Check if a DefId has the `#[doc = "trust-wp:proof_assert:..."]` marker
/// and extract the expression text if present.
///
/// This is the MIR-level equivalent of `get_proof_assert_expr_text` (which
/// works with HirId). Uses `tcx.get_attrs_by_path` to check attributes on
/// the closure's DefId.
fn get_proof_assert_expr_text_from_def_id(
    tcx: TyCtxt<'_>,
    def_id: DefId,
) -> Option<(String, bool)> {
    // For local DefIds, convert to HirId and use existing logic
    if let Some(local_def_id) = def_id.as_local() {
        let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
        return get_proof_assert_expr_text(tcx, hir_id);
    }
    None
}

/// Check if a HIR node has the `#[doc = "trust-wp:proof_assert:..."]` marker
/// and extract the expression text if present.
///
/// Returns `Some((expr_text, trusted))` if this is a proof_assert marker with
/// embedded expression,
/// `None` otherwise.
fn get_proof_assert_expr_text(tcx: TyCtxt<'_>, hir_id: HirId) -> Option<(String, bool)> {
    let attrs = tcx.hir_attrs(hir_id);
    for attr in attrs {
        if let Some(value) = crate::attr_utils::doc_marker_str(attr) {
            let value_str = value.as_str();
            if let Some(expr_text) = value_str.strip_prefix("trust-wp:trusted_proof_assert:") {
                if expr_text.is_empty() {
                    return None;
                }
                return Some((expr_text.to_string(), true));
            }
            if let Some(expr_text) = value_str.strip_prefix("trust-wp:proof_assert:") {
                // Return None for empty expression (shouldn't happen in practice)
                if expr_text.is_empty() {
                    return None;
                }
                return Some((expr_text.to_string(), false));
            }
        }
    }
    None
}
