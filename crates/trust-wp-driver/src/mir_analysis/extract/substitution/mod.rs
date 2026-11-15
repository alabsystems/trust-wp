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
        final_reborrow_sites: call_resolution::final_reborrow_sites(tcx, body),
        written_deref_reads: crate::mir_analysis::deref_store_staleness::written_deref_reads(
            tcx, body,
        ),
        loop_head_rebinds: super::loop_merges::loop_head_rebinds(
            body,
            body.arg_count,
            &crate::mir_analysis::detect_loops(body),
            &cutoff_blocks(body, &cutoff),
        ),
        renamable_params: match (cutoff.stop_location, cutoff.region_span) {
            (Some(at), None) if !tcx.is_closure_like(body.source.def_id()) => {
                super::param_writes::params_with_renamable_entry(tcx, body, at)
                    .into_keys()
                    .collect()
            }
            _ => HashSet::new(),
        },
    };
    extract_substitutions_from_block(body, BasicBlock::from_u32(0), st, cutoff, arg_names, &ctx)
}

/// The blocks the walk stops in (D-187): the block of a location cutoff, or
/// every block holding a statement or terminator whose span lies inside a
/// span cutoff.
fn cutoff_blocks(body: &Body<'_>, cutoff: &SubstitutionCutoff) -> HashSet<BasicBlock> {
    if let Some(location) = cutoff.stop_location {
        return HashSet::from([location.block]);
    }
    let Some(stop) = cutoff.stop_span else {
        return HashSet::new();
    };
    let stop = stop.source_callsite();
    if stop.is_dummy() {
        return HashSet::new();
    }
    let inside = |span: rustc_span::Span| {
        let span = span.source_callsite();
        !span.is_dummy() && span.lo() >= stop.lo() && span.hi() <= stop.hi()
    };
    body.basic_blocks
        .iter_enumerated()
        .filter(|(_, data)| {
            data.statements
                .iter()
                .any(|statement| inside(statement.source_info.span))
                || inside(data.terminator().source_info.span)
        })
        .map(|(block, _)| block)
        .collect()
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
/// callbacks can call `build_substitutions(body)` directly.
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
    // The blanket half of the interior-mutability rule, shared with the
    // primary block walker (`super::extract_from_block_with_context`): on
    // entry to a block that is the return target of a call, or of a `Drop`
    // with glue, every local whose type can reach interior mutability is
    // rebound to a fresh symbol. The callee may have written memory those
    // locals reach even when it received none of them as an argument (two
    // `&Cell<u8>` arguments may alias; a `Drop` impl may hold one), so the
    // per-argument rule at the call site cannot cover them. Premise-removing:
    // it only drops the identification of a pre-call read with a post-call
    // one.
    let mut local_exprs = st.local_exprs;
    super::loop_body::rebind_interior_mutable_locals_at_effect_target(
        ctx.tcx,
        body,
        bb,
        &mut local_exprs,
    );
    let mut visitor = SubstitutionVisitor {
        tcx: ctx.tcx,
        body,
        local_exprs,
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
