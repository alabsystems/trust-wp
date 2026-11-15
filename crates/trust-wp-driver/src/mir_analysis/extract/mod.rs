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
pub(in crate::mir_analysis) use assertion::machine_int_range_fact;
mod block_visitor;
mod borrow_carriers;
// #prophecy-slots M5: the caller-side expiry lane reuses the #124 ground-value
// predicate and the source-name resolver rather than re-deriving either.
pub(in crate::mir_analysis) use borrow_carriers::expr_is_ground_constant_tree;
mod branching;
mod branching_diag;
mod call_args;
mod call_effect_blocks;
mod call_effect_paths;
mod call_effect_reach;
mod call_resolve_shared;
mod call_resolve_util;
mod call_spec;
pub(in crate::mir_analysis) use call_spec::callee_invariant_premises;
mod cell_builtin;
mod closure;
pub(crate) mod collect_gate;
mod cutoff;
mod default_postcondition;
pub(in crate::mir_analysis) mod drop_glue_writes;
pub(crate) use drop_glue_writes::params_rebound_by_handoffs;
mod param_writes;
pub(crate) use param_writes::{
    param_writes_before, params_with_renamable_entry, params_written_before,
    PARAM_ENTRY_VALUE_SUFFIX,
};
mod entrypoints;
mod helpers;
pub(in crate::mir_analysis) use helpers::{
    block_must_diverge, source_name_for_local, translate_rvalue_with_enum_variants,
};
pub(crate) use helpers::{
    body_entry_diverges_via_panic, body_has_reachable_obligation_source,
    body_reaches_diverging_call, body_reaches_runtime_check,
    collect_generic_assoc_const_definitions,
};
mod loop_body;
mod loop_condition_writes;
pub(crate) use loop_condition_writes::loop_condition_exit_write;
mod loop_merges;
#[cfg(test)]
pub(in crate::mir_analysis) use loop_merges::{
    compute_skipped_loop_merges, loop_exit_edge, region_effects,
};
pub(crate) use loop_merges::{
    loop_condition_block, loop_exit_arm_dominating, loop_has_unmodeled_exit, loop_head_rebinds,
    loop_head_symbol, loop_lane_exit, switch_arm_dominating, LaneExit, LOOP_HEAD_SYMBOL_PREFIX,
};
mod name_substitutions;
mod panic_site_coverage;
mod param_destructuring;
mod past_loop_names;
mod primary;
pub(crate) use primary::body_returns_a_stale_store_read;
pub(crate) mod program_point_state;
mod reborrow_handback;
mod spanned_extract;
mod substitution;
mod try_operator;
mod unannotated_loops;
mod write_aliases;

#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use assertion::*;
#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use branching::*;
pub(in crate::mir_analysis) use call_args::stale_arguments;
#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use call_args::*;
pub(crate) use call_effect_blocks::{collect_call_effects_for_blocks, LoopEntryValues};
#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use call_resolve_util::*;
#[allow(unused_imports)] // Re-exported for tests and sibling modules via `use super::*`
use call_spec::*;
pub(crate) use closure::ty_exposes_interior_mutability;
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
#[cfg(test)]
pub(crate) use loop_body::collect_loop_body_call_obligations;
pub(crate) use loop_body::{
    collect_arithmetic_panic_obligations, collect_loop_body_call_obligations_split,
    collect_post_loop_arithmetic_obligations, collect_unannotated_loop_arithmetic_obligations,
    extract_recursive_call_args, loop_assigned_locals_by_header, unwalked_charged_assert_sites,
    with_charged_assert_recording, ArithmeticRegion, LoopBodySpecContext, RecursiveCallSite,
};
pub(crate) use name_substitutions::NameSubstitutions;
pub(crate) use panic_site_coverage::{
    unchecked_panic_sites, with_dead_edge_recording, EnteredBody, ProvedDeadEdges,
};
pub(crate) use param_destructuring::extract_param_destructuring_substitutions;
pub(super) use primary::{extract_from_block_with_context, BlockExtractionContext};
pub(crate) use spanned_extract::extract_return_expr_spanned;
pub(super) use substitution::SubstitutionExtractionContext;
#[allow(unused_imports)] // Re-exported for tests via `use super::*`
use try_operator::*;
pub(crate) use unannotated_loops::collect_unannotated_loop_obligations;

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
