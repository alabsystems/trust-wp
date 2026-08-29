// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Suppress pedantic warnings that don't affect correctness
#![allow(clippy::too_many_lines)] // Complex analysis functions are cohesive
#![allow(clippy::wildcard_imports)] // Extract submodules intentionally re-export wildcard symbols

//! Context-aware return expression extraction from MIR.
//!
//! Extracts function body expressions from MIR for simple pure functions,
//! with support for function call specs and source-location-spanned results.
//!
//! Spec application logic lives in [`super::spec_apply`]; call-site DefId
//! resolution lives in [`super::call_resolve`].

#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use std::{
    cell::{Cell, RefCell},
    collections::{HashMap, HashSet},
    sync::Arc,
};

#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use rustc_hir::def_id::DefId;
#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Location, Operand, Rvalue, SwitchTargets, TerminatorKind},
    ty::TyCtxt,
};
#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use rustc_span::Span;
#[cfg(test)]
#[allow(unused_imports)] // Re-exported for tests via `use super::*`
use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;
#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use trust_wp_core::formula::{BinOp, PureExpr};
#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use trust_wp_driver::StdSpec;

// Re-export items used by tests (imported via `use super::*` in tests.rs)
#[cfg(test)]
use super::{call_resolve::resolve_arg_names_or_warn, spec_apply::TranslatedArg};
mod assertion;
mod block_visitor;
mod borrow_carriers;
// #prophecy-slots M5: the caller-side expiry lane reuses the #124 ground-value
// predicate and the source-name resolver rather than re-deriving either.
pub(in crate::mir_analysis) use borrow_carriers::expr_is_ground_constant_tree;
mod branching;
mod branching_diag;
mod call_args;
mod call_effect_blocks;
mod call_resolve_shared;
mod call_resolve_util;
mod call_spec;
mod cell_builtin;
mod closure;
mod cutoff;
mod default_postcondition;
mod entrypoints;
mod helpers;
pub(in crate::mir_analysis) use helpers::source_name_for_local;
pub(crate) use helpers::collect_generic_assoc_const_definitions;
mod loop_body;
mod name_substitutions;
mod param_destructuring;
mod primary;
pub(crate) mod program_point_state;
mod spanned_extract;
mod substitution;
mod try_operator;

#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use assertion::*;
#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use branching::*;
#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use call_args::*;
pub(crate) use call_effect_blocks::collect_call_effects_for_blocks;
#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use call_resolve_util::*;
#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use call_spec::*;
#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use closure::*;
pub(crate) use cutoff::PROOF_ASSERT_STATE_MARKER_NAME;
pub(super) use cutoff::{cutoff_reached_at_statement, cutoff_reached_at_terminator};
#[cfg(test)]
#[allow(unused_imports)] // Re-exported for tests via `use super::*`
use default_postcondition::specialize_take_default_postcondition_for_ty;
#[cfg(test)]
pub(crate) use entrypoints::extract_name_substitutions_until_location;
#[cfg(test)]
pub(crate) use entrypoints::extract_return_expr_with_context;
pub(crate) use entrypoints::{
    extract_name_substitutions_until_location_in_region, extract_name_substitutions_until_span,
    extract_name_substitutions_until_span_in_region,
    extract_program_point_state_until_location_detailed, extract_return_expr_with_context_detailed,
    extract_return_expr_with_cutoff_span, get_mir_body, normalize_immutable_ref_param_derefs,
};
pub(super) use entrypoints::{extract_return_expr_impl, ExtractionConfig};
#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use helpers::*;
pub(crate) use loop_body::{
    collect_loop_body_call_obligations, extract_recursive_call_args, LoopBodySpecContext,
    RecursiveCallSite,
};
pub(crate) use name_substitutions::NameSubstitutions;
pub(crate) use param_destructuring::extract_param_destructuring_substitutions;
pub(super) use primary::{extract_from_block_with_context, BlockExtractionContext};
pub(crate) use spanned_extract::extract_return_expr_spanned;
pub(super) use substitution::SubstitutionExtractionContext;
#[allow(unused_imports)] // Re-exported for tests via `use super::*`
use try_operator::*;

#[cfg(test)]
mod tests;

// Recursive unevaluated-const expansion depth guard.
// Symbolic fallback may recursively read MIR bodies of const items and anon consts.
// Keep recursion bounded to avoid infinite cycles in self-referential constants.
thread_local! {
    pub(crate) static UNEVAL_CONST_EXPANSION_DEPTH: Cell<usize> = const { Cell::new(0) };
}

thread_local! {
    pub(crate) static QUALIFIED_ASSOC_CONST_DEFINITIONS:
        RefCell<HashMap<String, PureExpr>> = RefCell::new(HashMap::new());
}

pub(super) const MAX_UNEVAL_CONST_EXPANSION_DEPTH: usize = 6;

pub(crate) fn clear_qualified_assoc_const_definitions() {
    QUALIFIED_ASSOC_CONST_DEFINITIONS.with(|state| {
        state.borrow_mut().clear();
    });
}

pub(crate) fn record_qualified_assoc_const_definition(name: String, expr: PureExpr) {
    QUALIFIED_ASSOC_CONST_DEFINITIONS.with(|state| {
        state.borrow_mut().insert(name, expr);
    });
}

pub(crate) fn take_qualified_assoc_const_definitions() -> HashMap<String, PureExpr> {
    QUALIFIED_ASSOC_CONST_DEFINITIONS.with(|state| std::mem::take(&mut *state.borrow_mut()))
}
