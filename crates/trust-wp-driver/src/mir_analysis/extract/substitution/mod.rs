// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof-assert substitution extraction from MIR.
//!
//! This module implements the substitution extraction pipeline used by
//! `proof_assert!` verification. Instead of extracting return expressions,
//! it walks MIR blocks up to a cutoff (span or location) and builds a
//! name-to-expression substitution map representing program state at the
//! assertion point.
//!
//! The main entry point is [`extract_substitutions_from_block`], called from
//! [`super::extract_name_substitutions_until_span`] and
//! [`super::extract_name_substitutions_until_location`].
//!
//! The directory boundary mirrors the real subsystem ownership:
//! - [`visitor`] walks MIR blocks
//! - [`branch_merge`] handles `SwitchInt` recursion
//! - [`call_resolution`] resolves call results
//! - [`name_bindings`] materializes source-name substitutions
//! - [`state`] owns shared recursion state and cutoff reachability

mod branch_merge;
mod call_resolution;
mod name_bindings;
mod state;
mod visitor;
mod write_effects;

#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local},
    ty::TyCtxt,
};
pub(super) use state::SubstitutionCutoff;
pub(in crate::mir_analysis) use state::SubstitutionExtractionContext;
use state::SubstitutionState;
use trust_wp_core::formula::PureExpr;
use trust_wp_driver::StdSpec;
use visitor::SubstitutionVisitor;

use super::{
    super::translate::ty_to_expr_sort_enriched, block_visitor::walk_block,
    closure::closure_capture_names_for_body, NameSubstitutions,
};

/// Build a new [`SubstitutionExtractionContext`] and initial
/// [`SubstitutionState`], then kick off block-level substitution extraction.
///
/// This is the internal implementation behind
/// [`super::extract_name_substitutions_until_span`] and
/// [`super::extract_name_substitutions_until_location`].
pub(super) fn extract_substitutions_entry<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    arg_names: &[String],
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    cutoff: SubstitutionCutoff,
) -> Option<NameSubstitutions> {
    let mut local_exprs: HashMap<Local, PureExpr> = HashMap::new();
    for (i, name) in arg_names.iter().enumerate() {
        let local = Local::from_usize(i + 1);
        let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[local].ty);
        local_exprs.insert(local, PureExpr::Var(name.clone(), sort));
    }
    let st = SubstitutionState {
        local_exprs,
        deref_exprs: HashMap::new(),
        borrow_of: HashMap::new(),
        name_updates: HashMap::new(),
        visited: HashSet::new(),
    };
    let closure_capture_names = closure_capture_names_for_body(tcx, body);
    let ctx = SubstitutionExtractionContext {
        tcx,
        user_specs,
        trait_specs,
        extern_specs,
        closure_capture_names,
    };
    extract_substitutions_from_block(body, BasicBlock::from_u32(0), st, cutoff, arg_names, &ctx)
}

#[derive(Debug)]
pub(super) struct SubstitutionOutcome {
    pub(super) substitutions: Option<NameSubstitutions>,
    pub(super) failed_only_due_to_cycle: bool,
}

/// Create a [`SubstitutionVisitor`] and walk the block using the generic
/// [`walk_block`]. Used by both the entry point and recursive calls from
/// [`branch_merge`].
///
/// The visitor stores a `body` reference so that its `check_cutoff_at_*`
/// callbacks can call `build_substitutions(body)` directly. (#2066, Phase 4)
pub(super) fn extract_substitutions_from_block<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    st: SubstitutionState,
    cutoff: SubstitutionCutoff,
    arg_names: &[String],
    ctx: &SubstitutionExtractionContext<'_, 'tcx>,
) -> Option<NameSubstitutions> {
    extract_substitution_outcome_from_block(body, bb, st, cutoff, arg_names, ctx).substitutions
}

pub(super) fn extract_substitution_outcome_from_block<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    st: SubstitutionState,
    cutoff: SubstitutionCutoff,
    arg_names: &[String],
    ctx: &SubstitutionExtractionContext<'_, 'tcx>,
) -> SubstitutionOutcome {
    let mut visitor = SubstitutionVisitor {
        tcx: ctx.tcx,
        body,
        local_exprs: st.local_exprs,
        deref_exprs: st.deref_exprs,
        borrow_of: st.borrow_of,
        name_updates: st.name_updates,
        visited: st.visited,
        cutoff,
        arg_names,
        ctx,
        saw_cycle: false,
        saw_unsupported: false,
        closure_env_captures: HashMap::new(),
        closure_copy_of: HashMap::new(),
    };
    let substitutions = walk_block(body, bb, &mut visitor);
    SubstitutionOutcome {
        failed_only_due_to_cycle: substitutions.is_none()
            && visitor.saw_cycle
            && !visitor.saw_unsupported,
        substitutions,
    }
}
