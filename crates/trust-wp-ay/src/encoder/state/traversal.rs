// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Encoding traversal state: recursion depth, path conditions, and solver
//! configuration (#2655).
//!
//! Groups the fields that track the encoder's position within the
//! recursive `encode`/`encode_pure_impl` traversal of expression trees,
//! plus construction-time solver configuration (logic mode, quantifier
//! support) that was previously stored as top-level AYEncoder fields.

use ay_dpll::api::{Logic, Term};

/// Traversal state for recursive expression encoding (#2655).
///
/// Holds the recursion depth counter, the path-condition stack used
/// during `Ite` branch traversal, and construction-time solver configuration
/// (logic, quantifier support). These fields are tightly coupled:
/// both track "where we are / what mode we're in" during encoding.
///
/// All traversal fields `pub(in crate::encoder)` because the RAII guards
/// need raw pointer access to the interior fields.
pub(crate) struct TraversalState {
    /// Current recursion depth during `encode`/`encode_pure_impl` traversal.
    /// Checked against [`super::super::MAX_ENCODING_DEPTH`] to prevent
    /// stack overflow. (#1116, #2655)
    pub(in crate::encoder) recursion_depth: usize,
    /// Active path conditions while recursively encoding branch expressions.
    ///
    /// This lets side-effecting encodings (for example non-Bool `LetAssume` /
    /// `LetObligation`) assert guarded facts like `path => fact` instead of
    /// leaking branch-local assumptions globally. (#2655)
    pub(in crate::encoder) path_conditions: Vec<Term>,
    /// The SMT logic used at construction time (e.g., `QfAuflia`, `Auflia`).
    /// Used by loop encoder tests to verify logic escalation (#1604) and
    /// available for debug diagnostics.
    ///
    /// Moved from top-level AYEncoder field (#2655).
    pub(in crate::encoder) logic: Logic,
    /// Whether the solver was created with quantifier support (AUFLIA/UFLIA/ALL).
    /// When true and footprints exceed the threshold, `encode_sep_conj` uses
    /// quantified domain-based disjointness instead of O(L*R) cross-pair.
    ///
    /// Derivable from `logic` but cached to avoid recomputing on hot paths.
    /// Moved from top-level AYEncoder field (#2655).
    pub(in crate::encoder) supports_quantifiers: bool,
}

impl TraversalState {
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn new() -> Self {
        Self {
            recursion_depth: 0,
            path_conditions: Vec::new(),
            logic: Logic::QfAuflia,
            supports_quantifiers: false,
        }
    }

    /// Create with specific logic configuration (used by constructors).
    pub(crate) fn with_logic(logic: Logic, supports_quantifiers: bool) -> Self {
        Self {
            recursion_depth: 0,
            path_conditions: Vec::new(),
            logic,
            supports_quantifiers,
        }
    }
}
