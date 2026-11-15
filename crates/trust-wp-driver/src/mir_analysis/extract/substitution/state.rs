// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Local, Location},
    ty::TyCtxt,
};
use rustc_span::Span;
use trust_wp_core::formula::PureExpr;
use trust_wp_driver::StdSpec;

use super::super::helpers::{block_can_reach_cutoff, block_can_reach_location};

/// Mutable state threaded through substitution extraction recursion.
///
/// Bundling these four owned maps into a single struct keeps the recursive
/// function under clippy's `too_many_arguments` threshold while preserving the
/// clone-per-branch ownership pattern needed for SwitchInt exploration.
#[derive(Clone)]
pub(in crate::mir_analysis::extract) struct SubstitutionState {
    pub(super) local_exprs: HashMap<Local, PureExpr>,
    pub(super) deref_exprs: HashMap<Local, PureExpr>,
    pub(super) borrow_of: HashMap<Local, Local>,
    pub(super) name_updates: HashMap<String, PureExpr>,
    pub(super) visited: HashSet<BasicBlock>,
}

pub(in crate::mir_analysis) struct SubstitutionExtractionContext<'a, 'tcx> {
    pub(in crate::mir_analysis::extract) tcx: TyCtxt<'tcx>,
    pub(in crate::mir_analysis::extract) user_specs: &'a HashMap<DefId, StdSpec>,
    pub(in crate::mir_analysis::extract) trait_specs: &'a HashMap<DefId, StdSpec>,
    pub(in crate::mir_analysis::extract) extern_specs: &'a HashMap<String, StdSpec>,
    pub(in crate::mir_analysis::extract) closure_capture_names: Option<Vec<String>>,
    /// `&mut` borrow sites that Creusot's `NotFinalPlaces` analysis classifies
    /// as FINAL reborrows (the parent borrow is not moved, borrowed or written
    /// after the reborrow). Only these may be identified with the carrier of
    /// the place they reborrow; every other reborrow through a `&mut` deref is
    /// bound to a fresh per-site carrier (fresh id, no final link), matching
    /// Creusot's `borrow_mut`. An absent site is treated as NON-final.
    pub(in crate::mir_analysis::extract) final_reborrow_sites: HashSet<Location>,
    /// Per statement or call, the places it reads through a dereference whose
    /// memory a write may have changed before it (D-185), with what is known
    /// of that memory (`DerefStoreStaleness::current_state`).
    /// A read absent here reads memory no write reaches, so its entry value is
    /// its current one.
    pub(in crate::mir_analysis::extract) written_deref_reads: HashMap<
        Location,
        Vec<(
            rustc_middle::mir::Place<'tcx>,
            crate::mir_analysis::deref_store_staleness::CurrentState,
        )>,
    >,
    /// Per header of a loop the cutoff lies in, the locals that loop may
    /// change, which the walk re-binds to their loop-head symbols on entering
    /// the header (D-187, [`super::super::loop_merges::loop_head_rebinds`]).
    pub(in crate::mir_analysis::extract) loop_head_rebinds: HashMap<BasicBlock, Vec<Local>>,
    /// The parameters whose own name inside every value this walk records is
    /// their entry value, which the `proof_assert` lane names apart from
    /// their value at the cutoff (D-241,
    /// [`crate::mir_analysis::params_with_renamable_entry`]). Only these are
    /// re-bound to the functional update of their value by a field store; any
    /// other parameter keeps the identity reset (#1500), because a copy of
    /// its entry value is still read at its binding at the cutoff and the
    /// update would hand the copy the value stored after it. Empty for a walk
    /// with no program point or with a region.
    pub(in crate::mir_analysis::extract) renamable_params: HashSet<Local>,
}

/// Cutoff parameters for substitution extraction.
///
/// Bundles the three cutoff-related `Option` fields that are threaded through
/// every recursive call in the substitution extraction pipeline. Reducing three
/// parameters to one lowers argument counts enough to eliminate
/// `#[allow(clippy::too_many_arguments)]` on the six affected functions. (#2657)
#[derive(Clone, Copy)]
pub(in crate::mir_analysis::extract) struct SubstitutionCutoff {
    pub(in crate::mir_analysis::extract) stop_span: Option<Span>,
    pub(in crate::mir_analysis::extract) stop_location: Option<Location>,
    pub(in crate::mir_analysis::extract) region_span: Option<Span>,
}

pub(super) fn block_can_reach_substitution_cutoff<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    bb: BasicBlock,
    cutoff: &SubstitutionCutoff,
) -> bool {
    if let Some(location) = cutoff.stop_location {
        return block_can_reach_location(body, bb, location, &mut HashSet::new());
    }
    if let Some(span) = cutoff.stop_span {
        return block_can_reach_cutoff(body, bb, span, &mut HashSet::new());
    }
    false
}
