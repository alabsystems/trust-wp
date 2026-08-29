// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MIR analysis for verification condition generation.
//!
//! This module extracts function body expressions from MIR for simple
//! pure functions. For a function like:
//!
//! ```rust
//! fn increment(x: i32) -> i32 {
//!     x + 1
//! }
//! ```
//!
//! We extract the return expression `x + 1` as a `PureExpr` that can
//! be used in SMT-LIB2 verification conditions.
//!
//! # Module structure
//!
//! - [`spanned`] - Spanned expression type for source location mapping
//! - [`translate`] - MIR-to-PureExpr translation helpers
//! - [`call_resolve`] - Call-site DefId resolution and HIR parameter name lookup
//! - [`effects`] - Explicit call-effect context (replaces thread-local side channels)
//! - [`spec_apply`] - Contract specification application at call sites
//! - [`extract`] - Context-aware return expression extraction
//! - [`mut_borrow`] - Mutable borrow analysis (RustHorn-style)
//! - [`not_final_places`] - Backward dataflow analysis for final reborrow detection (#2150)
//! - [`projected_expiry`] - Caller-side expiry pins for `&mut` inside a call result (#prophecy-slots M5)
//! - [`resolver`] - Dataflow-precise borrow resolution for `&mut` parameters (#2150)
//! - [`loops`] - Loop detection and body extraction

mod call_resolve;
pub(crate) mod diagnostics;
pub(crate) mod effects;
pub(crate) mod extract;
mod loops;
mod mut_borrow;
pub(crate) mod not_final_places;
pub(crate) mod projected_expiry;
#[cfg(test)]
mod projected_expiry_tests;
pub(crate) mod reborrow_prophecy;
pub(crate) mod resolver;
mod spanned;
mod spec_apply;
pub(crate) mod translate;

// Note: CallEffects and ExtractionSession are imported directly via
// effects:: paths by consumers (extract/call_spec/mod.rs, extract/mod.rs,
// spec_apply.rs). No re-export needed here.
pub(crate) use call_resolve::resolve_arg_names_or_warn;
pub(crate) use extract::{
    clear_qualified_assoc_const_definitions, collect_call_effects_for_blocks,
    collect_loop_body_call_obligations, extract_name_substitutions_until_location_in_region,
    extract_name_substitutions_until_span, extract_name_substitutions_until_span_in_region,
    extract_param_destructuring_substitutions, extract_program_point_state_until_location_detailed,
    extract_recursive_call_args, extract_return_expr_spanned,
    extract_return_expr_with_context_detailed, extract_return_expr_with_cutoff_span, get_mir_body,
    normalize_immutable_ref_param_derefs, take_qualified_assoc_const_definitions,
    LoopBodySpecContext, NameSubstitutions, RecursiveCallSite,
};
#[cfg(test)]
pub(crate) use loops::LoopInfo;
pub(crate) use loops::{
    detect_loops, extract_loop_body, resolve_pre_loop_calls, CallSpecContext, ChangedPlaces,
    ChangedPlacesTree, ForLoopGhostState, LoopAnalysis, LoopBodyExpr,
};
pub(crate) use mut_borrow::{
    collect_mut_ref_paths_with_tcx, extract_mut_borrow_body, type_contains_mut_ref_with_tcx,
    type_eventually_contains_mut_ref, IndexedWrite, MutBorrowBody,
};
pub(crate) use reborrow_prophecy::{analyze_reborrow_prophecy, ReborrowProphecyInfo};
pub(crate) use spanned::SpannedBodyExpr;
