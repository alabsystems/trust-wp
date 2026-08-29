// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unified scoped program-point state for proof_assert extraction.
//!
//! `ScopedProgramPointState` captures everything the proof_assert layer needs
//! from a single MIR extraction pass at one program point: the return
//! expression, call effects, substitution map, and diagnostics.
//!
//! This replaces the pattern where `proof_assert_extract/mod.rs` coordinated
//! separate return-expression and substitution extraction passes for the same
//! cutoff location. (#2497)

use trust_wp_core::formula::PureExpr;

use super::{
    super::{diagnostics::ExtractionDiagnostics, effects::CallEffects},
    NameSubstitutions,
};

/// Unified symbolic state at a single MIR program point.
///
/// Returned by [`super::entrypoints::extract_program_point_state_until_location_detailed`].
/// Captures the full extraction result that proof_assert callers need,
/// eliminating the need for separate return-expression and substitution
/// extraction passes.
#[derive(Debug)]
pub(crate) struct ScopedProgramPointState {
    /// The return expression tree (may contain `LetAssume`/`LetObligation`).
    pub(crate) return_expr: Option<PureExpr>,
    /// Call effects from spec application during body extraction.
    pub(crate) call_effects: CallEffects,
    /// Name-to-expression substitution map for program-point variable state.
    pub(crate) substitutions: NameSubstitutions,
    /// Extraction diagnostics accumulated during the walk.
    pub(crate) diagnostics: ExtractionDiagnostics,
}
