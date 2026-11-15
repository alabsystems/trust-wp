// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared request/result types for loop verification.

use std::{collections::HashMap, time::Duration};

use rustc_hir::def_id::DefId;
use trust_wp_ay::LoopVerificationResult;
use trust_wp_core::{
    formula::PureExpr,
    logic::{LogicFnDef, LogicMode, TypeInvariantDef},
    TrackLevel,
};
use trust_wp_driver::StdSpec;

use crate::{
    callbacks::parsing::ParsedContract,
    contracts::FunctionContract,
    mir_analysis::{LoopAnalysis, LoopBodyExpr},
};

pub(super) type PreExtractedLoopBody = Option<(LoopBodyExpr, u32)>;
pub(super) type PreExtractedLoopBodies = Vec<PreExtractedLoopBody>;
pub(super) type PerLoopConditions = Vec<Option<PureExpr>>;

/// Parameters for loop invariant verification from the driver.
///
/// Bundles function identity, transformed contract clauses, loop analysis
/// results, and solver configuration for the inductive loop proof.
pub(in crate::callbacks) struct LoopWithInvariantRequest<'a> {
    pub(in crate::callbacks) def_path: &'a str,
    pub(in crate::callbacks) loc: &'a str,
    pub(in crate::callbacks) contract: &'a FunctionContract,
    pub(in crate::callbacks) parsed: &'a ParsedContract,
    pub(in crate::callbacks) requires: &'a [PureExpr],
    pub(in crate::callbacks) transformed_ensures: &'a [PureExpr],
    pub(in crate::callbacks) loop_analysis: &'a LoopAnalysis,
    pub(in crate::callbacks) type_invariants: Option<&'a [TypeInvariantDef]>,
    pub(in crate::callbacks) logic_fns: Option<&'a [LogicFnDef]>,
    pub(in crate::callbacks) mode_overrides: Option<&'a [LogicMode]>,
    pub(in crate::callbacks) type_constants: Option<&'a HashMap<String, PureExpr>>,
    pub(in crate::callbacks) track: Option<TrackLevel>,
    pub(in crate::callbacks) verbose: bool,
    pub(in crate::callbacks) timeout: Option<Duration>,
    /// User-defined and trait spec tables for call result modeling in loop bodies.
    /// When provided, `extract_loop_body` can resolve callee postconditions
    /// instead of havocing call destinations. (#1463)
    pub(in crate::callbacks) user_specs: &'a HashMap<DefId, StdSpec>,
    pub(in crate::callbacks) trait_specs: &'a HashMap<DefId, StdSpec>,
    /// Extern specs for call-site resolution in loop body extraction (#963 Phase C).
    pub(in crate::callbacks) extern_specs: &'a HashMap<String, StdSpec>,
    /// Rustc-backed ADT declarations for native datatype encoding (#1982).
    pub(in crate::callbacks) adt_decls: Option<&'a trust_wp_core::logic::AdtDecls>,
    /// Per-ADT integer field range constraints (e.g. `u32` field
    /// non-negativity) for loop VCs (#2702). Carries the same ranges the
    /// function-level pipeline uses so loop obligations over structs with
    /// unsigned fields get their `field(x) >= 0` facts.
    pub(in crate::callbacks) adt_field_ranges: Option<&'a trust_wp_core::logic::AdtFieldRanges>,
}

/// Output of loop invariant verification, bundling the verification result
/// with frame constraints for unmodified variables.
///
/// When the loop verification path returns `ContinueWithAssumptions`, the
/// function-level verifier needs to know which pre-loop bindings are preserved
/// across the loop. Frame constraints express `var == pre_loop_value` for each
/// variable NOT in the loop's `modified_vars` set.
pub(in crate::callbacks) struct LoopVerificationOutput {
    /// Whether the dispatcher may add a single loop's negated condition to
    /// the exit facts: every return passes through the loop (D-224). With
    /// several loops, each one's negated condition is already in
    /// `continuation_assumptions` when it holds at every return.
    pub(in crate::callbacks) exit_condition_holds_at_return: bool,
    /// The inductive verification results (init, preservation, postcondition, variant).
    pub(in crate::callbacks) result: LoopVerificationResult,
    /// Frame constraints for variables not modified by the loop body.
    /// Each entry is `Var(name) == pre_loop_value`. These should be injected
    /// into `effective_requires` alongside loop-exit assumptions when the
    /// function-level verification path handles post-loop reasoning (#2085).
    pub(in crate::callbacks) frame_constraints: Vec<PureExpr>,
    /// Loop facts that remain valid on the post-loop continuation path.
    ///
    /// This includes the exact effective invariants used by the loop proof
    /// (after structural/inferred additions) plus any synthesized completion
    /// facts needed to reason about the exhausted iterator state. The
    /// function-level verifier injects these alongside `¬condition` and frame
    /// constraints when continuing after a verified loop body. (#2116, #2085)
    pub(in crate::callbacks) continuation_assumptions: Vec<PureExpr>,
    /// Return expression extracted from post-loop MIR blocks.
    /// When the function returns a value computed after the loop (e.g., a local
    /// variable assigned before the loop and returned after), this provides the
    /// `result == <expr>` binding that `extract_return_expr_with_context` cannot
    /// produce (it bails at loop back-edges). Used by `ContinueWithAssumptions`
    /// to set `parsed.result_expr` for function-level postcondition checking.
    pub(in crate::callbacks) return_expr: Option<PureExpr>,
    /// Final values for `&mut` parameters written through deref after loop exit (#2085).
    ///
    /// For `*x = n` after the loop, maps `"x"` to `Var("n")`. This provides the
    /// `final_values` needed by `verify_mut_borrow_function_with_modes` when
    /// `extract_mut_borrow_body` returns `None` due to loop cycle detection.
    /// Without these, postconditions like `^x == n` cannot be checked because the
    /// SMT verifier has no binding for `x_final`.
    pub(in crate::callbacks) post_loop_final_values: HashMap<String, PureExpr>,
    /// The full set of assumptions threaded to the loop call obligation checker,
    /// including effective invariants used across all loops and guarded
    /// call-obligation facts that are not raw loop invariants.
    ///
    /// The checker needs the effective list, not the user-written
    /// `parsed.loop_fields.invariants` alone: the synthesized invariants carry
    /// facts like `i >= 0` and `v.len() > 0` that in-loop call preconditions
    /// depend on, and a check without them fails for want of facts the loop
    /// proof already had.
    ///
    /// Indexed like `loop_analysis.loops`: entry `k` holds only at loop `k`, so
    /// a consumer must never pool entries across loops.
    pub(in crate::callbacks) per_loop_effective_invariants: Vec<Vec<PureExpr>>,
    /// Verified-shaped loop phase outcomes that lacked accepted solver proof
    /// evidence. The dispatcher records these as evidence gaps before counting
    /// the loop path as cleanly verified.
    pub(in crate::callbacks) evidence_gap_reasons: Vec<String>,
}

/// Per-loop verification output, folded by the multi-loop orchestrator. (#2337)
pub(super) struct SingleLoopResult {
    pub(super) result: LoopVerificationResult,
    pub(super) frame_contributions: Vec<(String, PureExpr)>,
    pub(super) continuation_assumptions: Vec<PureExpr>,
    pub(super) return_expr: Option<PureExpr>,
    pub(super) post_loop_final_values: HashMap<String, PureExpr>,
    /// The full set of effective invariants used for this loop's verification,
    /// before the orchestrator appends call-obligation-only guarded facts. (#1709)
    pub(super) effective_invariants: Vec<PureExpr>,
    pub(super) evidence_gap_reasons: Vec<String>,
}
