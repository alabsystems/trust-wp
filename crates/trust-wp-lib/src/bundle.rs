// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Serializable verification input bundles.
//!
//! These types represent the complete inputs for a single verification call.
//! External consumers (e.g., tRust) construct a bundle from their own IR
//! and pass it to [`crate::verify`] or [`crate::verify_mut_borrow`].
//!
//! **Serde support:** `Serialize`/`Deserialize` derives are pending Phase 1a,
//! which adds serde feature flags to `trust-wp-core` and `trust-wp-ay` inner types.
//! Once the inner types support serde, the bundles will gain derives.

use std::{
    collections::{HashMap, HashSet},
    time::Duration,
};

use trust_wp_core::{
    formula::{BorrowFinality, BorrowIdOrigin, PureExpr},
    logic::{AdtDecls, AdtFieldRanges, LogicFnDef, LogicMode, TypeInvariantDef},
    TrackLevel,
};

/// Complete input for verifying a single pure function.
///
/// This is the owned equivalent of [`trust_wp_ay::VerificationRequest`].
/// External callers construct this from their own IR (e.g., tRust's tMIR)
/// and pass it to [`crate::verify`].
///
/// All fields use owned types so the bundle can be serialized, stored, and
/// replayed without lifetime constraints.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct VerificationBundle {
    /// Preconditions: expressions assumed true at function entry.
    pub requires: Vec<PureExpr>,
    /// Postconditions: expressions to prove at function exit.
    pub ensures: Vec<PureExpr>,
    /// Body expression: symbolic result of executing the function body.
    /// `None` for bodyless trait methods or opaque functions.
    pub return_expr: Option<PureExpr>,
    /// Ghost context: additional facts from ghost blocks.
    pub ghost_context: Vec<PureExpr>,
    /// Logic function definitions available for this verification.
    pub logic_fns: Vec<LogicFnDef>,
    /// Logic function openness modes.
    pub mode_overrides: Vec<LogicMode>,
    /// Type invariant definitions.
    pub type_invariants: Vec<TypeInvariantDef>,
    /// ADT declarations for native datatype registration.
    pub adt_decls: Option<AdtDecls>,
    /// ADT field range constraints for integer fields.
    pub adt_field_ranges: Option<AdtFieldRanges>,
    /// Type-level constants (e.g., `size_of` values).
    pub type_constants: HashMap<String, PureExpr>,
    /// Verification tracking level.
    pub track: Option<TrackLevel>,
    /// Solver timeout.
    pub timeout: Option<Duration>,
    /// Whether to use total integer arithmetic (suppress div-by-zero obligations).
    pub total_int_arithmetic: bool,
    /// Whether to use BV theory for bitwise operations.
    pub bitwise_proof: bool,
}

impl VerificationBundle {
    /// Create a new bundle with required fields and sensible defaults.
    ///
    /// Optional fields default to `None`/empty. Use struct update syntax
    /// or direct field assignment for optional fields.
    #[must_use]
    pub fn new(requires: Vec<PureExpr>, ensures: Vec<PureExpr>) -> Self {
        Self {
            requires,
            ensures,
            return_expr: None,
            ghost_context: Vec::new(),
            logic_fns: Vec::new(),
            mode_overrides: Vec::new(),
            type_invariants: Vec::new(),
            adt_decls: None,
            adt_field_ranges: None,
            type_constants: HashMap::new(),
            track: None,
            timeout: None,
            total_int_arithmetic: false,
            bitwise_proof: true,
        }
    }
}

/// Extension for functions with mutable borrow patterns.
///
/// Wraps a [`VerificationBundle`] with the additional fields needed
/// by the mutable-borrow verification path.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct MutBorrowBundle {
    /// Base verification input.
    pub base: VerificationBundle,
    /// Final-value bindings for mutable parameters.
    pub final_values: HashMap<String, PureExpr>,
    /// Parameters with dataflow-precise resolve points.
    pub resolve_assumptions: Option<Vec<String>>,
    /// Prophecy writeback pairs (child -> parent).
    pub prophecy_writebacks: Option<HashMap<String, String>>,
    /// Per-reborrow finality metadata.
    pub borrow_finality: Option<HashMap<String, BorrowFinality>>,
    /// Per-reborrow identity origin metadata.
    pub borrow_id_origins: Option<HashMap<String, BorrowIdOrigin>>,
    /// Parameters whose mutation was detected but not symbolically advanced.
    pub mutation_continued_params: Option<HashSet<String>>,
}

impl MutBorrowBundle {
    /// Create a new mutable borrow bundle.
    #[must_use]
    pub fn new(base: VerificationBundle, final_values: HashMap<String, PureExpr>) -> Self {
        Self {
            base,
            final_values,
            resolve_assumptions: None,
            prophecy_writebacks: None,
            borrow_finality: None,
            borrow_id_origins: None,
            mutation_continued_params: None,
        }
    }
}
