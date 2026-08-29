// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Helpers module — re-exports from focused sub-modules.
//!
//! This module was split in #1655 to support #1572 Phase 4 (inline WP).
//! Each sub-module has a single responsibility:
//! - `counterexample`: verification failure reporting
//! - `proof_assert_verify`: orchestration + preparation (`prepare_proof_assert`)
//! - `proof_assert_extract`: call-effect stripping, substitutions, simplification
//! - `expr_analysis`: expression tree walkers (`extract_old_deref_vars`, etc.)
//! - `logic_fn_scope`: logic function visibility and name normalization

#[cfg(test)]
mod tests;

// Re-export public API used by sibling modules in callbacks/
pub(super) use counterexample::report_counterexample;
// Re-exports used only by tests (via `helpers::analyze_call_assumptions` etc.)
#[cfg(test)]
pub(super) use expr_analysis::analyze_call_assumptions;
#[cfg(test)]
pub(super) use expr_analysis::IdentityFinalValueSynthesisSkipReason;
pub(super) use expr_analysis::{
    contains_mutating_call_effect, diagnose_identity_final_value_synthesis_skip_with_expr,
    expr_contains_old, extract_final_self_field_vars, extract_final_vars, extract_old_deref_vars,
    synthesize_identity_final_values_with_expr,
};
#[cfg(test)]
pub(super) use expr_analysis::{
    diagnose_identity_final_value_synthesis_skip, synthesize_identity_final_values,
};
// Re-exports used only by mod.rs tests (via `helpers::parent_module`)
#[cfg(test)]
pub(super) use logic_fn_scope::parent_module;
pub(super) use logic_fn_scope::scope_logic_fn_modes;
#[cfg(test)]
pub(super) use proof_assert_extract::{
    normalize_scalar_proof_assert_boundary, resolve_internal_references,
    simplify_proof_assert_expr, strip_call_effects, substitution_assumptions,
};
pub(super) use proof_assert_verify::{build_proof_assert_setup, prepare_proof_assert};

// Reference sibling modules for the `use` paths above
use super::counterexample;
#[cfg(test)]
use super::proof_assert_extract;
use super::{expr_analysis, logic_fn_scope, proof_assert_verify};
