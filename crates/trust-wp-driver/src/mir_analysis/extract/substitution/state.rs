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
