// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-contract skip-decision logic for the verification loop (#1526 Phase 5).
//!
//! Consolidates three independent skip guards (trusted, logic-fn, bodyless-trait)
//! into a single decision point so `verify_contracts` doesn't need to enumerate
//! skip conditions inline.

use std::collections::HashSet;

use rustc_middle::ty::TyCtxt;

use super::super::super::contracts::FunctionContract;

/// Whether a trait method declaration should be skipped from verification (#1178).
///
/// Bodyless trait methods (e.g., `fn foo(&self) -> bool;`) have contracts that serve
/// as specifications for implementations, not as verification targets.
pub(super) fn should_skip_bodyless_trait_method(
    is_trait_container: bool,
    has_default_body: bool,
) -> bool {
    is_trait_container && !has_default_body
}

/// Outcome of the per-contract skip-decision check (#1526 Phase 5).
///
/// Each variant carries the reason a contract should be skipped from
/// the main verification loop, along with the counter field to increment.
pub(super) enum SkipDecision {
    /// Proceed with verification — do not skip.
    Verify,
    /// `#[trusted]` function: postconditions assumed, not checked (#674).
    Trusted,
    /// Logic function without `#[ensures]`: axiomatized, not MIR-verified (#674).
    LogicFnAxiom,
    /// Logic function WITH `#[ensures]`: postcondition verified in a separate pass (#893).
    LogicFnEnsures,
    /// Bodyless trait method declaration: spec only, not verifiable (#1178).
    BodylessTraitMethod,
    /// A body that runs as a coroutine or only builds one: refused, never
    /// verified (see [`is_coroutine_body`]).
    CoroutineBody,
}

/// The refusal both assertion passes and the contract loop print for a body
/// [`is_coroutine_body`] reports.
pub(in crate::callbacks) const COROUTINE_REFUSAL: &str =
    "the body is a coroutine or builds one (`async fn`, `async`/`gen` block, async closure), \
     which trust-wp does not verify; refused instead of credited";

/// Count and name the contract loop's refusal of a coroutine body.
pub(super) fn refuse_coroutine_body(
    def_path: &str,
    counters: &mut super::super::reporting::VerificationCounters,
) {
    counters.errors += 1;
    eprintln!("trust-wp: {def_path} error: {COROUTINE_REFUSAL}");
}

/// Whether a body is a coroutine (an `async`/`gen` block, an `async fn`'s
/// lowered body) or only builds one (an `async fn` item, an async closure).
///
/// Neither is verified. The item's own MIR constructs the coroutine and does
/// nothing else, so its VC holds nothing of the body the user wrote; the
/// coroutine body carries `Yield`/resume semantics no lane models, and Creusot
/// does not verify coroutines either (its MIR translation treats `Yield` as
/// unreachable). A credit on either would be a verdict on code no pass
/// examined (async_fn_body_assertion_never_examined.rs), so both are REFUSED.
/// The refusal reaches every such body that owes anything because
/// `discover_coroutine_obligation_bodies` chooses its candidates with this
/// predicate; a body no pass admits is examined by nothing, not refused.
pub(in crate::callbacks) fn is_coroutine_body(
    tcx: TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
) -> bool {
    use rustc_hir::def::DefKind;
    if tcx.is_coroutine(def_id) {
        return true;
    }
    match tcx.def_kind(def_id) {
        DefKind::Fn | DefKind::AssocFn => tcx.asyncness(def_id).is_async(),
        DefKind::Closure => matches!(
            tcx.type_of(def_id)
                .instantiate_identity()
                .skip_norm_wip()
                .kind(),
            rustc_middle::ty::TyKind::CoroutineClosure(..)
        ),
        _ => false,
    }
}

/// Decide whether a contract should be skipped from the main verification loop.
///
/// Consolidates the independent skip guards (trusted, logic-fn, coroutine,
/// bodyless-trait) into a single decision point. The caller updates counters
/// and emits diagnostics based on the returned variant.
pub(super) fn check_contract_skip(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    logic_fn_paths: &HashSet<String>,
    logic_fn_has_ensures: &HashSet<String>,
) -> SkipDecision {
    // Guard 1: Trusted functions — postconditions assumed, not verified.
    // NOT counted as "verified" (soundness: false accept in should_fail harness, #674).
    if contract.trusted {
        return SkipDecision::Trusted;
    }

    // Guard 2: Logic functions — runtime bodies erased to unreachable!().
    // MIR-based verification would produce trivially-true results (#674).
    // Two checks: (1) fast path via pre-computed logic_fn_paths set, (2) fallback
    // via raw attribute marker for unparseable bodies (pearlite! blocks, #674 case 5).
    let def_path_str = tcx.def_path_str(contract.def_id);
    if logic_fn_paths.contains(&def_path_str)
        || super::super::super::logic::has_logic_marker(tcx.get_all_attrs(contract.def_id))
    {
        return if logic_fn_has_ensures.contains(&def_path_str) {
            SkipDecision::LogicFnEnsures
        } else {
            SkipDecision::LogicFnAxiom
        };
    }

    // Guard 3: coroutine bodies and the items that only build one.
    if is_coroutine_body(tcx, contract.def_id) {
        return SkipDecision::CoroutineBody;
    }

    // Guard 4: Bodyless trait method declarations (#1178).
    // Trait methods without a default body have contracts that serve as specs for
    // implementations. Verifying them produces false counterexamples.
    if let Some(assoc_item) = tcx.opt_associated_item(contract.def_id) {
        let is_trait = matches!(
            assoc_item.container,
            rustc_middle::ty::AssocContainer::Trait
        );
        // Only query defaultness for trait-container items — calling
        // `tcx.defaultness()` on inherent impl items causes an ICE.
        let has_body = is_trait && tcx.defaultness(contract.def_id).has_value();
        if should_skip_bodyless_trait_method(is_trait, has_body) {
            return SkipDecision::BodylessTraitMethod;
        }
    }

    SkipDecision::Verify
}

/// Summary of which clause types a contract contains.
///
/// Used by guard predicates to decide whether a function needs type invariant
/// injection or whether a parse failure should count as an error.
#[allow(clippy::struct_excessive_bools)] // Each field is an independent clause-type presence flag
pub(super) struct ContractClausePresence {
    pub(super) has_requires: bool,
    pub(super) has_ensures: bool,
    pub(super) has_invariants: bool,
    pub(super) has_variants: bool,
}

impl ContractClausePresence {
    pub(super) fn from_contract(contract: &FunctionContract) -> Self {
        Self {
            has_requires: !contract.requires.is_empty(),
            has_ensures: !contract.ensures.is_empty(),
            has_invariants: !contract.invariants.is_empty(),
            has_variants: !contract.variants.is_empty(),
        }
    }

    /// Whether a function with no explicit contracts should receive type invariant injection (#359).
    ///
    /// Returns true when type invariant definitions exist AND the contract has no explicit
    /// requires, ensures, invariants, or variants.
    pub(super) fn needs_type_invariant_injection(&self, has_type_invariant_defs: bool) -> bool {
        has_type_invariant_defs
            && !self.has_requires
            && !self.has_ensures
            && !self.has_invariants
            && !self.has_variants
    }

    /// Whether a contract has any user-written clauses.
    ///
    /// Used to distinguish parse failures on real contracts (which count as errors)
    /// from parse failures on empty contracts (which are silently skipped).
    pub(super) fn has_clauses(&self) -> bool {
        self.has_requires || self.has_ensures || self.has_invariants || self.has_variants
    }
}
