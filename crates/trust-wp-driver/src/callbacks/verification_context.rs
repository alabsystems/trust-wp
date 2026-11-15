// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared verification parameter objects for trust-wp-driver callbacks.
//!
//! These context structs replace long positional argument lists across
//! verification dispatch helpers.

use std::{
    collections::{HashMap, HashSet},
    time::Duration,
};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use trust_wp_core::{
    formula::PureExpr,
    logic::{LogicFnDef, LogicMode, TypeInvariantDef},
    TrackLevel,
};
use trust_wp_driver::StdSpec;

use super::super::{
    contracts::{FunctionContract, TraitMethodContract},
    ghost::GhostBlock,
};

/// Top-level inputs for `verify_contracts`.
#[derive(Clone, Copy)]
pub(super) struct VerificationRunConfig<'a> {
    /// All discovered contracts, including contracts outside `--filter`.
    ///
    /// Filtered verification should still resolve callee specs for modular
    /// call-site assumptions; `verify_contracts` receives only the contracts
    /// selected for proof.
    pub(super) all_contracts: &'a [FunctionContract],
    pub(super) ghost_blocks: &'a [GhostBlock],
    pub(super) logic_fns: &'a [LogicFnDef],
    pub(super) type_invariant_defs: &'a [TypeInvariantDef],
    pub(super) trait_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) trait_contracts: &'a [TraitMethodContract],
    pub(super) recursive_fns: &'a HashSet<DefId>,
    /// Extern specs for call-site resolution. Passed explicitly to replace
    /// `EXTERN_SPECS` thread-local access in `mir_analysis/` (#963 Phase C).
    pub(super) extern_specs: &'a HashMap<String, StdSpec>,
    pub(super) verbose: bool,
    pub(super) track_level: TrackLevel,
    pub(super) timeout: Option<Duration>,
    /// Treat unverified logic function postconditions as errors (#1490).
    pub(super) strict_axioms: bool,
    /// Downgrade Verified results with trust/hole proof steps to Unknown
    /// (Phase 1 soundness gate).
    pub(super) strict_trust: bool,
}

/// Shared context for all verification passes within a single contract (#1986).
///
/// Bundles the per-function parameters that are identical across
/// `verify_contract_loop_path`, the standalone refinement pass, and the non-loop
/// verification path. Replaces 21-parameter and 16-parameter positional
/// signatures with a single `&VerificationContext` plus per-call args.
///
/// Two lifetimes: `'tcx` for rustc's query context, `'a` for borrowed
/// verification data (which may be local to the loop iteration).
#[derive(Clone, Copy)]
pub(super) struct VerificationContext<'a, 'tcx> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) contract: &'a FunctionContract,
    pub(super) def_path: &'a str,
    pub(super) loc: &'a str,
    pub(super) recursive_fns: &'a HashSet<DefId>,
    pub(super) trait_contract_map: &'a HashMap<DefId, HashMap<String, &'a TraitMethodContract>>,
    pub(super) type_invariants_opt: Option<&'a [TypeInvariantDef]>,
    pub(super) logic_fns_opt: Option<&'a [LogicFnDef]>,
    pub(super) mode_overrides_opt: Option<&'a [LogicMode]>,
    pub(super) type_constants: Option<&'a HashMap<String, PureExpr>>,
    pub(super) track_level: TrackLevel,
    pub(super) timeout: Option<Duration>,
    pub(super) verbose: bool,
    pub(super) user_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) trait_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) extern_specs: &'a HashMap<String, StdSpec>,
    /// Rustc-backed ADT declarations for native datatype encoding (#1982).
    pub(super) adt_decls_opt: Option<&'a trust_wp_core::logic::AdtDecls>,
    /// Per-ADT integer field range constraints (e.g. `u32` field
    /// non-negativity), threaded into loop VCs so struct-field loop variants
    /// carry their range facts (#2702).
    pub(super) adt_field_ranges_opt: Option<&'a trust_wp_core::logic::AdtFieldRanges>,
}

/// Shared context for proof assertion verification.
///
/// Bundles verification config that is constant across all proof_assert checks
/// in a single crate. Used by inline verification in `verify_contracts`
/// and by `prepare_proof_assert`.
#[derive(Clone, Copy)]
pub(super) struct ProofAssertContext<'a> {
    pub(super) logic_fn_defs: &'a [LogicFnDef],
    pub(super) type_invariant_defs: &'a [TypeInvariantDef],
    pub(super) trait_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) extern_specs: &'a HashMap<String, StdSpec>,
    pub(super) verbose: bool,
}
