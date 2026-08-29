// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Suppress pedantic doc warnings - DefId doesn't need backticks
#![allow(clippy::doc_markdown)]

//! Contract data extracted from the Rust source.

use rustc_hir::def_id::{DefId, LocalDefId};

/// A function with associated contracts.
#[derive(Debug, Clone)]
pub(crate) struct FunctionContract {
    /// The LocalDefId of the function (needed to retrieve MIR body)
    pub(crate) local_def_id: LocalDefId,
    /// The DefId of the function (for path resolution and display)
    pub(crate) def_id: DefId,
    /// Preconditions (from #[requires(...)])
    pub(crate) requires: Vec<String>,
    /// Postconditions (from #[ensures(...)])
    pub(crate) ensures: Vec<String>,
    /// Loop invariants (from #[invariant(...)]), flattened across all loops
    pub(crate) invariants: Vec<String>,
    /// Per-loop invariants with source span (start, end) of the loop expression.
    /// Each entry is (start_byte, end_byte, invariants_for_that_loop).
    /// Used to associate invariants with specific loops in multi-loop functions.
    pub(crate) per_loop_invariants: Vec<(u32, u32, Vec<String>)>,
    /// Per-loop variants with source span (start, end) of the loop expression.
    /// Each entry is (start_byte, end_byte, variants_for_that_loop).
    /// Used to associate termination variants with specific loops in multi-loop functions.
    pub(crate) per_loop_variants: Vec<(u32, u32, Vec<String>)>,
    /// Source spans (start, end) of ALL loop expressions, including those without
    /// invariants. Used to prevent false invariant inheritance from outer loops.
    pub(crate) all_loop_spans: Vec<(u32, u32)>,
    /// Loop variants for termination proofs (from #[variant(...)])
    pub(crate) variants: Vec<String>,
    /// Whether this function requires termination checking (`#[check(terminates)]`)
    pub(crate) terminates: bool,
    /// Whether this function is a ghost function (`#[check(ghost)]`).
    /// Ghost functions use total integer arithmetic (no division-by-zero obligations).
    /// Wiring to `VerificationRequest.total_int_arithmetic()` is in verification.rs.
    pub(crate) ghost: bool,
    /// Whether this function is trusted (postconditions assumed, body not verified)
    pub(crate) trusted: bool,
    /// If this method implements a trait method, the trait's DefId and method name.
    /// Used to look up inherited contracts from trait declarations.
    pub(crate) trait_origin: Option<TraitOrigin>,
}

/// Links an impl method back to its trait declaration.
///
/// Used for trait contract inheritance: when an impl method has no contracts
/// of its own, we check whether the trait declaration has contracts and
/// inherit them.
#[derive(Debug, Clone)]
pub(crate) struct TraitOrigin {
    /// DefId of the trait (e.g., the `Counter` in `impl Counter for MyStruct`)
    pub(crate) trait_def_id: DefId,
    /// Method name on the trait (e.g., "count")
    pub(crate) trait_method_name: String,
}

/// A trait method with associated contracts.
///
/// Represents the specification side of a trait method declaration.
/// These contracts are inherited by impl methods and used at generic call sites.
#[derive(Debug, Clone)]
pub(crate) struct TraitMethodContract {
    /// The DefId of the trait itself
    pub(crate) trait_def_id: DefId,
    /// The DefId of the trait method declaration
    pub(crate) method_def_id: DefId,
    /// Method name (e.g., "count")
    pub(crate) method_name: String,
    /// Full trait path (e.g., "crate::Counter")
    pub(crate) trait_path: String,
    /// Preconditions from the trait declaration
    pub(crate) requires: Vec<String>,
    /// Postconditions from the trait declaration
    pub(crate) ensures: Vec<String>,
}
