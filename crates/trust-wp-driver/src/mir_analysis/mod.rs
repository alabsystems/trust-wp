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

pub(crate) mod binding_identity;
mod call_resolve;
mod contract_signature;
pub(crate) mod deref_store_staleness;
pub(crate) mod diagnostics;
#[cfg(test)]
mod drop_glue_writes_tests;
pub(crate) mod effects;
pub(crate) mod extract;
pub(crate) mod fact_scope;
pub(crate) mod governed_place;
mod loops;
mod mut_borrow;
pub(crate) mod not_final_places;
pub(crate) mod projected_expiry;
#[cfg(test)]
mod projected_expiry_tests;
pub(crate) mod reaching_defs;
pub(crate) mod reborrow_prophecy;
pub(crate) mod resolver;
mod spanned;
mod spec_apply;
pub(crate) use spec_apply::is_positional_alias;
pub(crate) mod translate;

// Note: CallEffects and ExtractionSession are imported directly via
// effects:: paths by consumers (extract/call_spec/mod.rs, extract/mod.rs,
// spec_apply.rs). No re-export needed here.
pub(crate) use call_resolve::{
    fresh_fallback_arg_var, is_fallback_arg_placeholder, name_unnamed_params,
    resolve_arg_names_or_warn, resolve_spec_or_mir_arg_names, ANON_PARAM_PREFIX,
    POSITIONAL_PARAM_PREFIX,
};
pub(crate) use contract_signature::{
    call_signature, contract_signature, input_types, install_final_readers,
    is_held_mutable_parameter_type, CallSite,
};
#[cfg(test)]
pub(crate) use extract::collect_loop_body_call_obligations;
pub(crate) use extract::{
    body_entry_diverges_via_panic, body_has_reachable_obligation_source,
    body_reaches_diverging_call, body_reaches_runtime_check, body_returns_a_stale_store_read,
    clear_qualified_assoc_const_definitions, collect_arithmetic_panic_obligations,
    collect_call_effects_for_blocks, collect_loop_body_call_obligations_split,
    collect_post_loop_arithmetic_obligations, collect_unannotated_loop_arithmetic_obligations,
    collect_unannotated_loop_obligations, extract_name_substitutions_until_location_in_region,
    extract_name_substitutions_until_span, extract_name_substitutions_until_span_in_region,
    extract_param_destructuring_substitutions, extract_program_point_state_until_location_detailed,
    extract_recursive_call_args, extract_return_expr_spanned,
    extract_return_expr_with_context_detailed, extract_return_expr_with_cutoff_span, get_mir_body,
    loop_assigned_locals_by_header, loop_condition_block, loop_condition_exit_write,
    loop_exit_arm_dominating, loop_has_unmodeled_exit, loop_head_rebinds, loop_head_symbol,
    loop_lane_exit, normalize_immutable_ref_param_derefs, param_writes_before,
    params_rebound_by_handoffs, params_with_renamable_entry, params_written_before,
    switch_arm_dominating, take_qualified_assoc_const_definitions, unchecked_panic_sites,
    unwalked_charged_assert_sites, with_charged_assert_recording, with_dead_edge_recording,
    ArithmeticRegion, EnteredBody, LaneExit, LoopBodySpecContext, LoopEntryValues,
    NameSubstitutions, ProvedDeadEdges, RecursiveCallSite, PARAM_ENTRY_VALUE_SUFFIX,
};
pub(crate) use loops::{
    detect_loops, every_return_passes_through, extract_loop_body, name_invalidated_args,
    names_rewritten_after_exit_before_later_loop, params_invalidated_by_loops,
    params_invalidated_by_loops_at_exits, resolve_pre_loop_calls, CallSpecContext, ChangedPlaces,
    ChangedPlacesTree, DroppedPremise, ForLoopGhostState, InvalidatedEntryNames, LoopAnalysis,
    LoopBodyExpr, LoopInfo,
};
#[cfg(test)]
pub(crate) use mut_borrow::IndexedWrite;
pub(crate) use mut_borrow::{
    collect_mut_ref_paths_with_tcx, extract_mut_borrow_body, params_with_stale_call_final_credit,
    type_contains_mut_ref_with_tcx, type_eventually_contains_mut_ref, MutBorrowBody,
};
pub(crate) use reborrow_prophecy::{analyze_reborrow_prophecy, ReborrowProphecyInfo};
pub(crate) use spanned::SpannedBodyExpr;
