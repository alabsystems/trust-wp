// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for loop invariant verification — extracted from inline tests (#1669).
//!
//! Split into leaf modules aligned to production ownership (#2372).

mod for_loop_facts;
mod invariant_selection_and_expr_refs;
mod post_loop_reasoning;
mod reporting_and_ghost_rewrite;
mod result_aggregation;
mod stable_loop_invariants;
mod stable_type_invariants;

pub(super) use trust_wp_ay::{
    Counterexample, LoopVerificationResult, UnknownReason, VerificationResult,
};
pub(super) use trust_wp_core::formula::{BinOp, PureExpr};

pub(super) use super::{
    expr_utils::{expr_referenced_vars, expr_references_var},
    for_loop_facts::{
        build_for_loop_completion_facts, build_for_loop_init_facts,
        build_for_loop_literal_start_element_index_fact, build_for_loop_produced_len_bound,
        build_for_loop_produced_len_step_fact, build_for_loop_range_element_bounds,
        build_for_loop_range_element_current_fact, build_for_loop_structural_invariant,
        build_for_loop_transition_end_fact, build_for_loop_transition_fact,
        build_for_loop_transition_guard_fact, build_for_loop_transition_step_fact,
        build_for_loop_zero_start_element_index_fact,
        build_group_guarded_for_loop_produced_len_bound,
        build_group_guarded_for_loop_range_element_facts,
        build_group_guarded_for_loop_seq_element_facts, build_guarded_for_loop_range_element_facts,
        build_guarded_seq_for_loop_yielded_element_facts,
        is_for_loop_element_nonnegative_invariant,
    },
    ghost_rewrite::{
        filter_post_loop_borrow_resolution_vars, is_trust_wp_ghost_def_path,
        rewrite_loop_ensures_for_ghost_return,
    },
    inference::{
        infer_parameter_frame_invariants, infer_stable_loop_invariants,
        infer_stable_type_invariant_clauses, infer_unsigned_nonneg_invariants,
        infer_unsigned_nonneg_requires,
    },
    old_rewrite::rewrite_loop_postcondition_old,
    reporting::{
        combine_loop_results, combine_optional_results, loop_verification_evidence_gap_reasons,
        worst_result,
    },
    span_matching::find_loop_invariants,
    transition_facts::{
        build_fmap_identity_bridge_facts, build_transition_facts_for_loop_state,
        build_tuple_position_map, include_structural_invariant_in_loop_vc,
    },
};
pub(super) use crate::mir_analysis::{ChangedPlaces, ChangedPlacesTree, ForLoopGhostState};
