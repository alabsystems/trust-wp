// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Generic solve helpers, axiom-free probes, retry logic, and result resolution.
//!
//! Extracted from the monolithic `solver_tail.rs` (#1988). These are reusable
//! verification utilities shared across function, mut-borrow, and loop paths.
//! Originally moved from `verify/mod.rs` in #1576 Slice B.

use tracing::debug;
use trust_wp_core::formula::{PureExpr, PureExprDepthLimitedTraversalExt as _};

use super::{
    extract_proof_summary, FreshBaseRecheckFn, BASE_RECHECK_PATHOLOGY_MESSAGE,
    VACUOUS_PROOF_MESSAGE,
};
use crate::{
    encoder::{AYEncoder, MAX_ENCODING_DEPTH},
    error::EncodingError,
    verify::{
        hard_timeout::ResolveContinuation, Counterexample, UnknownReason, VerificationResult,
    },
};

const AXIOM_FREE_NEGATED_GOAL_LABEL_PREFIX: &str = "__trust_wp_axiom_free_negated_goal";
const PROOF_REQUIRED_NEGATED_GOAL_LABEL_PREFIX: &str = "__trust_wp_proof_required_negated_goal";

// ── Generic solve helpers (moved from verify/mod.rs, #1576 Slice B) ──

pub(crate) fn unknown_result_from_encoder(encoder: &AYEncoder) -> VerificationResult {
    // When a ay assertion or check_sat panicked, the Unknown is a safety
    // fallback — the solver's self-reported reason would be misleading.
    // Surface the actual panic message so the diagnostic is actionable (#1009).
    if let Some(panic_reason) = encoder.solver_panic_reason() {
        return VerificationResult::Unknown(UnknownReason::SolverPanic(format!(
            "ay solver panicked: {panic_reason}"
        )));
    }
    // Prefer the cached executor error from `check_sat_with_details()` (#2639).
    // This is the atomic envelope captured during the same solve call, avoiding
    // stale side-channel reads from `solver.executor_error()`.
    if let Some(executor_detail) = encoder.last_executor_error() {
        let base = encoder
            .last_unknown_reason()
            .map_or("internal-error", |r| r.as_str());
        return VerificationResult::Unknown(UnknownReason::SolverMessage(format!(
            "{base}: {executor_detail}"
        )));
    }
    // Prefer the cached typed unknown reason from `check_sat_with_details()` (#2639).
    // Fall back to the live solver accessor only when no cached solve details
    // have been recorded yet (e.g., solver panicked before `check_sat_with_details`).
    if let Some(cached_reason) = encoder.last_unknown_reason() {
        return VerificationResult::Unknown(cached_reason.clone());
    }
    // Legacy fallback: read the solver's side-channel reason string.
    let solver = encoder.solver();
    let reason = solver.unknown_reason().map(|reason| reason.to_string());
    if let Some(executor_detail) = solver.executor_error() {
        let base = reason.as_deref().unwrap_or("internal-error");
        return VerificationResult::Unknown(UnknownReason::SolverMessage(format!(
            "{base}: {executor_detail}"
        )));
    }
    VerificationResult::unknown_from_solver(reason)
}

fn fail_closed_solver_context_result(
    encoder: &AYEncoder,
    verdict: &str,
) -> Option<VerificationResult> {
    encoder.fail_closed_solver_context().map(|context| {
        VerificationResult::Unknown(UnknownReason::SolverMessage(format!(
            "fail-closed {verdict}: {context}"
        )))
    })
}

fn fail_closed_solver_context_is_active(encoder: &AYEncoder) -> bool {
    encoder.fail_closed_solver_context().is_some()
}

fn solve_evidence_result_is_unsat(result: &str) -> bool {
    result.eq_ignore_ascii_case("unsat")
        || result
            .strip_prefix("Unsat")
            .is_some_and(|suffix| suffix.is_empty() || suffix.starts_with('('))
}

fn has_accepted_unsat_evidence(encoder: &AYEncoder) -> bool {
    encoder.last_solve_evidence().is_some_and(|evidence| {
        evidence.accepted_for_consumer && solve_evidence_result_is_unsat(&evidence.result)
    })
}

fn rejected_unsat_evidence_reason(encoder: &AYEncoder) -> UnknownReason {
    let detail = encoder.last_solve_evidence().map_or_else(
        || "missing solver evidence".to_string(),
        |evidence| {
            evidence
                .consumer_rejection
                .clone()
                .unwrap_or_else(|| "solver evidence was not accepted for consumers".to_string())
        },
    );
    UnknownReason::SolverMessage(format!(
        "UNSAT result lacks accepted solver evidence: {detail}"
    ))
}

/// Collect assumptions introduced by `LetAssume` nodes in a body.
///
/// The eager closure-law helpers need to see both body-local
/// `postcondition_once(...)` assumptions and body-local existential
/// `postcondition_mut(...)` assumptions. Reusing the raw `LetAssume`
/// assumptions lets the solver tail feed both cases into the same eager
/// instantiation helpers used for preconditions. (#2556)
///
/// Uses `for_each_recursive_with_depth_limit` for exhaustive variant
/// coverage (#2577). Also now visits quantifier triggers, which the
/// previous manual traversal skipped.
pub(in crate::verify) fn collect_body_let_assume_assumptions(expr: &PureExpr) -> Vec<&PureExpr> {
    let mut assumptions = Vec::new();
    expr.for_each_recursive_with_depth_limit(MAX_ENCODING_DEPTH, |node| {
        if let PureExpr::LetAssume { assumption, .. } = node {
            assumptions.push(assumption.as_ref());
        }
    });
    assumptions
}

/// Assert all standard axioms on the encoder after expressions have been encoded.
///
/// This is the shared axiom assertion sequence used by all verification paths
/// (function, mut_borrow, loop). Must be called after all expressions are encoded
/// so that the encoder knows which UF symbols exist and can assert the
/// appropriate axioms. (#785)
///
/// `requires` is needed for eager axiom instantiation: when preconditions contain
/// ground `postcondition_once(...)` calls, the reverse fn_mut_once axiom is
/// pre-instantiated so that ay's single-round E-matching can use the ground
/// `postcondition_mut(...)` term in the same pass (#970). `body_assumptions`
/// carries `LetAssume` assumptions that were asserted while encoding the return
/// expression but still need eager closure-law handling so the solver sees the
/// same ground bridge terms that a top-level precondition would provide. (#2556)
pub(in crate::verify) fn assert_standard_axioms(
    encoder: &mut AYEncoder,
    requires: &[PureExpr],
    body_assumptions: &[&PureExpr],
) -> Result<(), EncodingError> {
    // Fast path: when no axiom-relevant symbols have been declared during
    // encoding (no logic functions, spec functions, or datatypes), every
    // axiom family below is guaranteed to be a no-op. Skip the entire
    // axiom assertion sequence to avoid the O(N) symbol scans, quantifier
    // variable allocation, and function declaration lookups. This benefits
    // pure arithmetic obligations (e.g., `result == x + 1`) that have no
    // UF dependencies. (#2674)
    if !encoder.has_any_axiom_relevant_symbols() {
        return Ok(());
    }

    // Demand-driven closure axiom emission (#1997): single-pass demand guard
    // scan classifies all closure_postcondition_* symbols in one O(N) traversal
    // instead of 3× O(N) (#2278 F5). Only assert axioms for present categories.
    let flags = encoder.closure_postcondition_flags();

    // Context-aware demand guard (#2668): single-pass scan of requires and
    // body_assumptions for ground closure postcondition calls (postcondition,
    // postcondition_mut, postcondition_once). If none exist, the quantified
    // closure law axioms have no triggers to fire on and become dead-weight
    // overhead that pushes ay-dpll from decidable QF_LIA into undecidable
    // AUFLIA, causing Unknown(Incomplete) on simple closure body verifications
    // like disjoint_captures::{closure#0} (bug/962). The UF symbols may still
    // be declared (from the closure's own ensures contract or from trait
    // membership), but without ground instances the axioms are inert.
    //
    // Consolidated scan (#2694): replaces 3 sequential traversals (any, mut,
    // once) with one pass that sets all three flags simultaneously, avoiding
    // redundant expression-tree traversals on large verification contexts.
    let ctx_flags = AYEncoder::scan_postcondition_context(requires, body_assumptions);
    let has_closure_postcondition_in_context = ctx_flags.has_any;

    if flags.has_once
        && has_closure_postcondition_in_context
        && std::env::var_os("TRUST_WP_ENABLE_QUANTIFIED_FN_MUT_ONCE_LAWS").is_some()
    {
        // The full quantified FnMut/FnOnce bridge includes reverse
        // witness-generating laws and can push simple forward-only closure
        // obligations into quantifier-ematching-exists-incomplete. The hot
        // path below asserts sound eager ground forward instances for the
        // concrete postcondition_mut facts already present in the VC; keep
        // the global quantified bridge opt-in unless a caller deliberately
        // needs reverse witness reasoning.
        encoder.assert_fn_mut_once_law();
    }
    // Assert the eager ground bridges BEFORE the Fn laws so ay-dpll's
    // single-round matcher sees the `postcondition_mut(...)` terms when the
    // quantified fn_mut / fn_once laws are registered. This is the same
    // convergence issue that motivates the eager once-instantiation helper:
    // if the ground term arrives after the quantified law, the chain can stay
    // SAT even though the bridge is logically present. (#2556, #970)
    if flags.has_once && flags.has_mut && has_closure_postcondition_in_context {
        encoder.assert_eager_fn_mut_once_instantiations(requires)?;
        encoder.assert_eager_fn_mut_once_instantiations_for_exprs(body_assumptions)?;
        // ay v0.2.0 E-matching may not instantiate the quantified forward law.
        // Eagerly assert postcondition_once conclusions for ground postcondition_mut
        // calls in requires so the solver sees the bridge fact directly.
        encoder.assert_eager_fn_mut_once_forward_instantiations(requires)?;
        encoder.assert_eager_fn_mut_once_forward_instantiations_for_exprs(body_assumptions)?;
    }
    // Eagerly Skolemize existential assumptions containing postcondition_mut.
    // ay-dpll cannot Skolemize existentials (ay#813), so existential call-site
    // assumptions like `exists<f2> postcondition_mut(f, a, f2, r) && resolve(f2)`
    // produce no ground terms for E-matching. This pre-Skolemizes them so the
    // fn_mut law's trigger can fire in a single round (#970, #2556).
    // Failure is a soundness issue — verification must not proceed without
    // Skolemized axioms (#1631).
    if flags.has_mut && has_closure_postcondition_in_context {
        encoder.assert_eager_existential_skolemizations(requires)?;
        encoder.assert_eager_existential_skolemizations_for_exprs(body_assumptions)?;
    }
    if flags.has_fn
        && has_closure_postcondition_in_context
        && std::env::var_os("TRUST_WP_ENABLE_QUANTIFIED_FN_CLOSURE_LAWS").is_some()
    {
        // Latest ay can spend the full solve budget E-matching the global Fn
        // closure-law foralls. Function obligations assert direct ground
        // fn_mut/fn_once bridge instances for the current goal before this tail
        // runs, so keep the quantified laws opt-in in the hot verification path.
        // Direct encoder tests still exercise the global law generator.
        encoder.assert_fn_closure_laws();
    }
    // Postcondition_mut ensures axioms (#2668): connect postcondition_mut UF
    // predicates to concrete capture-level effects for closures with registered
    // ensures and struct sorts. Demand guard uses pre-computed ctx_flags.has_mut
    // from the consolidated scan (#2694), avoiding a redundant traversal.
    if flags.has_mut && ctx_flags.has_mut {
        encoder.assert_postcondition_mut_ensures_axioms();
    }
    // Standalone postcondition_once resolve law (#2668): when postcondition_once
    // is declared but postcondition (Fn-trait) is absent, the fn_once law in
    // assert_fn_closure_laws cannot fire. Assert a weaker resolve-only law so
    // FnOnce-only closures get the critical resolve constraint at call sites.
    // Context guard: only assert when there are ground postcondition calls
    // in the verification context (#2668).
    if flags.has_once && !flags.has_fn && has_closure_postcondition_in_context {
        encoder.assert_standalone_postcondition_once_laws();
    }
    // Postcondition_once ensures axioms (#2668): uses pre-computed
    // ctx_flags.has_once from the consolidated scan (#2694).
    if flags.has_once && ctx_flags.has_once {
        encoder.assert_postcondition_once_ensures_axioms();
    }
    // Eager ground fn_once instantiation for ensures (#2668): when the ensures
    // contain a postcondition_once goal and the Fn postcondition symbol exists,
    // eagerly assert the fn_once biconditional so ay's single-round E-matching
    // can connect the postcondition assumption to the postcondition_once goal.
    // Context guard: only assert when there are ground postcondition calls (#2668).
    if flags.has_once && flags.has_fn && has_closure_postcondition_in_context {
        encoder.assert_eager_fn_once_for_ensures(requires)?;
        encoder.assert_eager_fn_once_for_ensures_exprs(body_assumptions)?;
    }
    // Eager ground ensures instantiation (#2668): pre-instantiate the quantified
    // ensures axioms for each ground postcondition_once/postcondition_mut call
    // in the preconditions. ay-dpll's single-round E-matching may fire for one
    // ground call but miss subsequent ones (e.g., two sequential closure calls
    // in test_fnmut3). Inlineable postcondition_once calls may not leave a UF
    // declaration behind, so the once path keys off the expression context rather
    // than `flags.has_once`.
    if ctx_flags.has_once {
        encoder.assert_eager_ground_postcondition_once_ensures(requires)?;
        encoder.assert_eager_ground_postcondition_once_ensures_for_exprs(body_assumptions)?;
    }
    if flags.has_mut && ctx_flags.has_mut {
        encoder.assert_eager_ground_postcondition_mut_ensures(requires)?;
        encoder.assert_eager_ground_postcondition_mut_ensures_for_exprs(body_assumptions)?;
    }

    // Demand-driven standard axiom emission (#2674 Phase 5): single-pass scan
    // of spec-function and logic-function registries determines which axiom
    // families have declared symbols. Only call axiom assertion methods for
    // families that have demand. For verification queries that don't use
    // FMap/FSet/Option/Result/tuples (e.g., pure arithmetic, bitvector proofs),
    // this eliminates all per-family overhead.
    let demand = encoder.standard_axiom_demand();

    if demand.has_tuples {
        encoder.assert_tuple_axioms();
    }
    if demand.has_unit {
        encoder.assert_unit_singleton_axioms();
    }
    if demand.has_option_result {
        encoder.assert_option_result_axioms();
    }
    if demand.has_fmap {
        encoder.assert_fmap_axioms();
    }
    if demand.has_fset {
        encoder.assert_fset_axioms();
    }
    if demand.has_deep_model {
        encoder.assert_deep_model_axioms();
    }
    if demand.has_layout {
        encoder.assert_layout_axioms();
    }
    if demand.has_trait_postcondition {
        encoder.assert_trait_postcondition_axioms();
    }
    if demand.has_type_invariant {
        encoder.assert_type_invariant_axioms();
    }
    // Phase 3 (#2288): assert ground instances of Seq/FMap/FSet axioms using
    // term-only applications collected during encoding. Must run AFTER the
    // quantified axioms above (so UF declarations exist) and BEFORE check_sat.
    encoder.assert_standard_ground_instances();
    Ok(())
}

// ── Axiom-free probe ──────────────────────────────────────────────────

/// Outcome of the axiom-free probe phase.
#[derive(Debug)]
pub(in crate::verify) enum AxiomFreeOutcome {
    /// Proved UNSAT without axioms — postcondition holds.
    ///
    /// The axiom-free probe uses `AssertionPhase::Other` (no label prefix)
    /// so unsat-core vacuity checking is not meaningful here. The caller
    /// uses a base re-solve as the vacuity guard instead. (#2141, #2520)
    Unsat,
    /// Found SAT without axioms — a potential counterexample. The axioms
    /// might eliminate this model, so the full axiom path still runs. If the
    /// full path returns `Incomplete`, this counterexample is used as a
    /// fallback only when no fail-closed solver context is active. (#2141, #2404)
    Sat(Counterexample),
    /// Inconclusive within the probe timeout — axioms are needed.
    Inconclusive,
}

/// Try solving without standard axioms first (#2116, #2141).
///
/// Many obligations (simple equalities, arithmetic, structural invariants) are
/// provable from declarations + negated goal alone. Quantified axioms (closure
/// laws, collection semantics) are only needed when the proof depends on
/// collection/closure semantics.
///
/// Uses a bounded 500ms timeout so the probe doesn't consume the full
/// solver timeout on problems that genuinely need axioms. The original
/// timeout is restored before returning.
///
/// Returns [`AxiomFreeOutcome::Unsat`] when the obligation is provable without
/// axioms. The caller uses a base re-solve as the vacuity guard (no unsat-core
/// check here — `AssertionPhase::Other` has no label prefix). Returns
/// [`AxiomFreeOutcome::Sat`] with a counterexample if the negated goal is
/// satisfiable without axioms (potential false positive). Returns
/// [`AxiomFreeOutcome::Inconclusive`] if axioms are needed.
pub(in crate::verify) fn axiom_free_solve_with_sat(encoder: &mut AYEncoder) -> AxiomFreeOutcome {
    use std::time::Duration;

    // Save and set a short probe timeout so Phase 1 doesn't eat into Phase 2.
    // 500ms is sufficient: simple obligations (empty Seq == empty Seq, i == 0)
    // resolve in <100ms. Problems requiring axioms hit Unknown quickly at this
    // bound, preserving time budget for the full Phase 2 solve.
    let original_timeout = encoder.solver().timeout();
    let probe_timeout = Duration::from_millis(500);
    // Only use the probe timeout if it's shorter than the original.
    let effective_probe = match original_timeout {
        Some(orig) if orig <= probe_timeout => orig,
        _ => probe_timeout,
    };
    encoder.set_timeout(Some(effective_probe));

    let result = encoder.with_negated_goal_label_prefix(
        AXIOM_FREE_NEGATED_GOAL_LABEL_PREFIX.to_string(),
        |encoder| encoder.check_sat(),
    );

    // Restore the original timeout for Phase 2 / outer check_sat.
    encoder.set_timeout(original_timeout);

    match result {
        ay_dpll::api::SolveResult::Unsat(_) if has_accepted_unsat_evidence(encoder) => {
            AxiomFreeOutcome::Unsat
        }
        ay_dpll::api::SolveResult::Unsat(_) => AxiomFreeOutcome::Inconclusive,
        ay_dpll::api::SolveResult::Sat if fail_closed_solver_context_is_active(encoder) => {
            AxiomFreeOutcome::Inconclusive
        }
        ay_dpll::api::SolveResult::Sat => {
            let model = encoder.get_model();
            AxiomFreeOutcome::Sat(Counterexample::from_encoder_model(encoder, model))
        }
        _ => AxiomFreeOutcome::Inconclusive,
    }
}

/// Extended axiom-free probe with a longer timeout (#2692).
///
/// Used when the standard 500ms axiom-free probe returns `Inconclusive` but
/// the demand analysis shows no axiom families need assertion. In this case
/// the obligation is likely pure arithmetic (QF_LIA) that needs more solver
/// time rather than quantified axioms. The extended probe uses 5s, matching
/// the base recheck probe timeout, to give the solver enough time for
/// ITE-heavy obligations like sorting networks (inc_max_3).
///
/// The solver's incremental state from the first 500ms probe is preserved,
/// so the extended probe picks up where the first left off. This makes the
/// effective timeout 500ms + 5s = 5.5s for the axiom-free path, which is
/// still much shorter than the full 60s solver timeout and avoids injecting
/// axioms that would push decidable problems into undecidable territory.
pub(super) fn axiom_free_solve_with_sat_extended(encoder: &mut AYEncoder) -> AxiomFreeOutcome {
    use std::time::Duration;

    let original_timeout = encoder.solver().timeout();
    // 5s extended probe: sufficient for ITE-heavy arithmetic obligations
    // like 3-level sorting networks. The solver's learned clauses from the
    // initial 500ms probe carry over, so most of this budget is spent on
    // new search rather than re-exploration.
    let extended_timeout = Duration::from_secs(5);
    let effective_probe = match original_timeout {
        Some(orig) if orig <= extended_timeout => orig,
        _ => extended_timeout,
    };
    encoder.set_timeout(Some(effective_probe));

    debug!(
        "[TRUST_WP_DEBUG] extended axiom-free probe: no axiom demand detected, \
         retrying with {}ms timeout (#2692)",
        effective_probe.as_millis()
    );

    let result = encoder.with_negated_goal_label_prefix(
        AXIOM_FREE_NEGATED_GOAL_LABEL_PREFIX.to_string(),
        |encoder| encoder.check_sat(),
    );

    encoder.set_timeout(original_timeout);

    match result {
        ay_dpll::api::SolveResult::Unsat(_) if has_accepted_unsat_evidence(encoder) => {
            AxiomFreeOutcome::Unsat
        }
        ay_dpll::api::SolveResult::Unsat(_) => AxiomFreeOutcome::Inconclusive,
        ay_dpll::api::SolveResult::Sat if fail_closed_solver_context_is_active(encoder) => {
            AxiomFreeOutcome::Inconclusive
        }
        ay_dpll::api::SolveResult::Sat => {
            let model = encoder.get_model();
            AxiomFreeOutcome::Sat(Counterexample::from_encoder_model(encoder, model))
        }
        _ => AxiomFreeOutcome::Inconclusive,
    }
}

/// Try solving without standard axioms first (#2116).
///
/// UNSAT-only variant used by loop verification paths that only need the
/// fast UNSAT shortcut. Returns `Some(Unsat)` if provable without axioms;
/// `None` otherwise (caller asserts axioms and re-solves).
pub(in crate::verify) fn try_axiom_free_solve(
    encoder: &mut AYEncoder,
) -> Option<ay_dpll::api::SolveResult> {
    use std::time::Duration;

    let original_timeout = encoder.solver().timeout();
    let probe_timeout = Duration::from_millis(500);
    let effective_probe = match original_timeout {
        Some(orig) if orig <= probe_timeout => orig,
        _ => probe_timeout,
    };
    encoder.set_timeout(Some(effective_probe));

    let result = encoder.with_negated_goal_label_prefix(
        AXIOM_FREE_NEGATED_GOAL_LABEL_PREFIX.to_string(),
        |encoder| encoder.check_sat(),
    );

    encoder.set_timeout(original_timeout);

    match result {
        ay_dpll::api::SolveResult::Unsat(_) if has_accepted_unsat_evidence(encoder) => Some(result),
        _ => None,
    }
}

// ── Retry logic ───────────────────────────────────────────────────────

/// Whether retry on UNKNOWN is disabled via `TRUST_WP_NO_RETRY=1`.
pub(in crate::verify) fn retry_disabled() -> bool {
    use std::sync::OnceLock;
    static DISABLED: OnceLock<bool> = OnceLock::new();
    *DISABLED.get_or_init(|| {
        std::env::var("TRUST_WP_NO_RETRY")
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false)
    })
}

/// Retry `check_sat` with a reduced timeout when the initial call returns
/// UNKNOWN due to timeout (#2142, #2674).
///
/// Strategy: re-run `check_sat` with half the original solver timeout. The
/// solver state (assertions, declarations) persists across calls — ay-dpll's
/// incremental solving means the retry benefits from search state built
/// during the first attempt. Using half the timeout (instead of the full
/// original) saves wall-clock budget for subsequent obligation slices: for
/// a 60s solver timeout, the retry uses 30s instead of 60s, saving 30s of
/// the hard-timeout envelope. The solver's learned clauses and conflict
/// analysis from the initial attempt make the half-timeout retry effective
/// for non-deterministic timeouts while limiting waste on genuinely hard
/// problems. (#2674)
///
/// Returns `None` if retry is disabled, the UNKNOWN reason is not timeout, or
/// the retry also returns UNKNOWN. Returns `Some(result)` if the retry
/// produced a definitive result (Sat or Unsat).
pub(crate) fn retry_check_sat_on_timeout(
    encoder: &mut AYEncoder,
) -> Option<ay_dpll::api::SolveResult> {
    if retry_disabled() {
        return None;
    }

    // Only retry on timeout — other UNKNOWN reasons (incomplete, memout,
    // solver panic) are unlikely to resolve with more time.
    // Prefer the cached typed reason from check_sat_with_details() (#2639),
    // falling back to the legacy solver side-channel for backward compat.
    let is_timeout = encoder
        .last_unknown_reason()
        .is_some_and(crate::verify::types::UnknownReason::is_timeout);
    if !is_timeout {
        // Legacy fallback: check the solver's string-based reason in case
        // no cached details are available (e.g., probe paths that bypass
        // check_sat_with_details).
        let reason = encoder.solver().unknown_reason();
        let legacy_timeout = reason.as_ref().is_some_and(|r| {
            let s = r.to_string();
            s.contains("timeout") || s.contains("Timeout")
        });
        if !legacy_timeout {
            return None;
        }
    }

    // No timeout set — UNKNOWN shouldn't be timeout-related. Bail out.
    let original = encoder.solver().timeout()?;

    // Use half the original timeout for the retry when the original is >= 10s.
    // The solver's incremental state carries over (learned clauses, conflict
    // analysis), so half the time is usually sufficient to resolve
    // non-deterministic timeouts. For genuinely hard problems, saving 50%
    // of the retry budget preserves wall-clock time for subsequent obligation
    // slices. For a 60s solver timeout, the retry uses 30s instead of 60s,
    // saving 30s of the hard-timeout envelope per function. (#2674)
    //
    // For short timeouts (< 10s), use the original timeout unchanged. The
    // halving optimization targets production verification where solver
    // timeouts are >= 30s. Short timeouts typically appear in tests or
    // probe configurations where halving would provide negligible benefit.
    let retry_timeout = if original >= std::time::Duration::from_secs(10) {
        original / 2
    } else {
        original
    };

    #[allow(clippy::cast_possible_truncation)]
    let retry_ms = retry_timeout.as_millis() as u64;
    #[allow(clippy::cast_possible_truncation)]
    let original_ms = original.as_millis() as u64;
    tracing::info!(
        original_ms,
        retry_ms,
        "retrying check_sat with reduced timeout (#2674)"
    );

    // Set the reduced retry timeout, retry, then restore the original.
    encoder.set_timeout(Some(retry_timeout));
    let result = encoder.check_sat();
    encoder.set_timeout(Some(original));

    match result {
        ay_dpll::api::SolveResult::Unknown => {
            tracing::info!("retry also returned Unknown — accepting timeout");
            None
        }
        definitive => {
            let verdict = match &definitive {
                ay_dpll::api::SolveResult::Unsat(_) => "Unsat",
                ay_dpll::api::SolveResult::Sat => "Sat",
                _ => "other",
            };
            tracing::info!(verdict, "retry resolved Unknown");
            Some(definitive)
        }
    }
}

/// Run `check_sat` with retry-on-timeout. Returns the definitive `SolveResult`.
///
/// Consolidates the retry pattern previously duplicated across 4 resolve
/// functions (#2441 Phase 1). If the initial `check_sat` returns `Unknown`,
/// delegates to [`retry_check_sat_on_timeout`] for a single extended-timeout
/// retry. Returns the definitive result (Sat/Unsat) or the original Unknown.
pub(crate) fn check_sat_with_retry(encoder: &mut AYEncoder) -> ay_dpll::api::SolveResult {
    let result = encoder.check_sat();
    if matches!(result, ay_dpll::api::SolveResult::Unknown) {
        retry_check_sat_on_timeout(encoder).unwrap_or(result)
    } else {
        result
    }
}

// ── Tiered solve ─────────────────────────────────────────────────────

/// Short initial timeout for the tiered solve probe (#2674 Phase 4).
///
/// 10 seconds is sufficient for the common case: most axiom-dependent
/// obligations resolve in 1-5s with the ground pool + E-matching. Problems
/// that need the full timeout (60s) typically indicate missing specs or
/// fundamental limitations rather than needing more search time.
const TIERED_PROBE_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(10);

/// Minimum solver timeout before tiered solving is worth the overhead (#2674).
///
/// When the solver timeout is <= 15s, the tiered probe (10s) would consume
/// most of the budget. In that case, skip the probe and go directly to the
/// full solve.
const TIERED_PROBE_MIN_FULL_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(15);

/// Run `check_sat` with a tiered timeout strategy (#2674 Phase 4).
///
/// Two-phase approach for the full axiom path:
/// 1. **Short probe** (10s): Most axiom-dependent obligations resolve quickly
///    once the ground pool and E-matching axioms are asserted. If the probe
///    returns SAT or UNSAT, we have a definitive answer without consuming the
///    full timeout budget.
/// 2. **Full solve**: Only invoked when the short probe returns Unknown. The
///    solver's incremental state is preserved across calls, so the full solve
///    benefits from search progress made during the probe.
///
/// This avoids the common case where a 60s timeout is allocated but the
/// obligation resolves in 2-3s. The hard-timeout envelope (2x solver timeout
/// + grace) still bounds total wall-clock cost, and the tiered approach stays
/// within that envelope since `TIERED_PROBE_TIMEOUT < solver_timeout`.
///
/// Falls back to a single `check_sat_with_retry` when:
/// - The solver timeout is <= 15s (probe would consume most of the budget)
/// - No solver timeout is configured
/// - `TRUST_WP_NO_RETRY=1` (retry disabled)
pub(crate) fn tiered_check_sat(encoder: &mut AYEncoder) -> ay_dpll::api::SolveResult {
    tiered_check_sat_with_phase(encoder).0
}

/// Which phase of [`tiered_check_sat`] produced the returned result.
///
/// Test-visible routing evidence: the probe-decline pin asserts that a probe
/// `Unknown` — including `QuantifierUnhandled` — reaches [`FullSolve`], i.e.
/// the full solve is never skipped on the strength of a probe verdict alone.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TieredSolvePhase {
    /// Tiering skipped (no timeout, or timeout below the 15s minimum);
    /// a single `check_sat_with_retry` produced the result.
    Untiered,
    /// The 10s probe returned a definitive Sat/Unsat.
    Probe,
    /// The probe returned Unknown and the full solve ran with the
    /// obligation's original budget.
    FullSolve,
}

/// [`tiered_check_sat`] with the resolving phase exposed for routing pins.
pub(crate) fn tiered_check_sat_with_phase(
    encoder: &mut AYEncoder,
) -> (ay_dpll::api::SolveResult, TieredSolvePhase) {
    let original_timeout = encoder.solver().timeout();

    // Skip tiered solving when the solver timeout is too short for it to help,
    // or when no timeout is configured.
    let should_tier = match original_timeout {
        Some(timeout) if timeout >= TIERED_PROBE_MIN_FULL_TIMEOUT => true,
        _ => false,
    };

    if !should_tier {
        return (check_sat_with_retry(encoder), TieredSolvePhase::Untiered);
    }

    // Phase 1: Short probe.
    encoder.set_timeout(Some(TIERED_PROBE_TIMEOUT));
    let probe_result = encoder.check_sat();
    encoder.set_timeout(original_timeout);

    match probe_result {
        ay_dpll::api::SolveResult::Unknown => {
            // EVERY probe Unknown proceeds to the full solve — including
            // `QuantifierUnhandled` (#129 leg B, removing the 71dfb30 #perf
            // short-circuit).
            //
            // The removed short-circuit treated a probe `QuantifierUnhandled`
            // as a STRUCTURAL property of the query ("re-running with a larger
            // timeout re-derives the same verdict") and returned the probe's
            // Unknown without ever running the full solve. Both halves of that
            // rationale went stale:
            //
            // - The verdict is NOT structural: it reports where the quantifier
            //   engine stood when the 10s probe budget expired, and the full
            //   solve (incremental continuation, larger budget) CAN reach a
            //   different verdict. Measured under the decoupled budget regime
            //   (e36ef2e): probe-declined slices sat next to sibling slices of
            //   the same obligation that verified with clean strict
            //   certificates (list_index_mut: 3 of 4 slices verified, the 4th
            //   was declined with the full solve skipped by construction), so
            //   the skip — not the engine — was what sank the obligation to
            //   Unknown without a real attempt.
            // - The perf motivation priced full-solve churn against a per-test
            //   wall the solver budget was coupled to (pre-e36ef2e). Under the
            //   decoupled regime the full solve runs inside a derived budget
            //   that nests within the wall, so the churn is bounded and cannot
            //   kill the test by itself.
            //
            // FAIL-CLOSED: this routing introduces no new accepting path. The
            // full solve's result flows through the identical resolvers as
            // every solve — Unsat must pass the accepted-evidence gates
            // (proof-complete statistics, consumer-accepted) or is demoted to
            // Unknown; Sat goes through the fail-closed counterexample path;
            // Unknown resolves exactly as the probe's Unknown would have. A
            // decline can only become an accept by producing the same evidence
            // any other solve must.
            tracing::debug!(
                probe_timeout_ms = TIERED_PROBE_TIMEOUT.as_millis(),
                probe_unknown_reason = ?encoder.last_unknown_reason(),
                "tiered solve: probe returned Unknown, proceeding to full solve (#2674)"
            );
            // Phase 2: Full solve with the original timeout. The solver's
            // incremental state carries over — learned clauses, conflict
            // analysis, and partial model from the probe are retained.
            //
            // Skip retry (#2674): when the tiered probe already consumed
            // TIERED_PROBE_TIMEOUT (10s) of search time and the full solve
            // also returns Unknown, the solver has had 10s + T of cumulative
            // search. A T/2 retry (30s for T=60s) is unlikely to resolve
            // genuinely stuck problems but wastes significant wall-clock
            // budget. For multi-slice functions, this 30s saving per slice
            // can be the difference between fitting within the compat harness
            // limit (120s) and timing out. The retry is only valuable for
            // non-deterministic timeouts where the solver almost finished —
            // these are resolved by the full solve's fresh timeout window.
            let result = encoder.check_sat();
            if matches!(result, ay_dpll::api::SolveResult::Unknown) {
                tracing::debug!(
                    "tiered solve: full solve also returned Unknown — \
                     skipping retry (probe + full already exhausted budget, #2674)"
                );
            }
            (result, TieredSolvePhase::FullSolve)
        }
        definitive => {
            let verdict = match &definitive {
                ay_dpll::api::SolveResult::Unsat(_) => "Unsat",
                ay_dpll::api::SolveResult::Sat => "Sat",
                _ => "other",
            };
            tracing::debug!(
                verdict,
                probe_timeout_ms = TIERED_PROBE_TIMEOUT.as_millis(),
                "tiered solve: probe resolved in short timeout (#2674)"
            );
            (definitive, TieredSolvePhase::Probe)
        }
    }
}

// ── Result resolution ─────────────────────────────────────────────────

/// Check SAT and map the result to a [`VerificationResult`].
///
/// Test-only resolve function with unsat-core vacuity checking.
/// Production paths use `resolve_sat_result_without_vacuity` (no vacuity)
/// or `resolve_base_sat_result` (inverted vacuity).
pub(in crate::verify) fn resolve_last_unsat_with_vacuity(
    encoder: &mut AYEncoder,
) -> VerificationResult {
    // Vacuity guard (#2414): demote to Unknown if the negated
    // postcondition did not participate in the UNSAT proof.
    match encoder.is_vacuous_unsat() {
        Ok(true) => VerificationResult::Unknown(UnknownReason::SolverMessage(
            VACUOUS_PROOF_MESSAGE.to_string(),
        )),
        Err(err) => VerificationResult::Unknown(UnknownReason::SolverMessage(format!(
            "vacuity check failed while reading unsat core: {err}"
        ))),
        Ok(false) => {
            let summary = extract_proof_summary(encoder.solver());
            VerificationResult::Verified(summary)
        }
    }
}

pub(in crate::verify) fn prefer_non_vacuous_core_on_incomplete_base(
    core_result: VerificationResult,
    base_result: ResolveContinuation,
) -> ResolveContinuation {
    match base_result {
        // A Verified base recheck is a positive SAT/non-vacuity witness, not
        // the proof of the scoped obligation. Preserve the scoped result and
        // its exact strict certificate; returning the base result here loses
        // that certificate and the mandatory authority boundary correctly
        // downgrades the aggregate to Unknown(ProofTrusted).
        ResolveContinuation::Continue(VerificationResult::Verified(_))
            if matches!(core_result, VerificationResult::Verified(_)) =>
        {
            ResolveContinuation::Continue(core_result)
        }
        other => other,
    }
}

pub(super) fn prefer_non_vacuous_core_on_fresh_base_recheck(
    core_result: VerificationResult,
    base_result: ResolveContinuation,
    fresh_base_recheck: Option<&FreshBaseRecheckFn<'_>>,
    allow_abort_rescue: bool,
) -> ResolveContinuation {
    // The same-encoder base recheck (run after a genuine UNSAT proof, with the
    // negated-goal scope popped) demotes the proof on two distinct signals:
    //
    //   1. The explicit VACUOUS message: the base UNSAT-core showed the base
    //      alone is contradictory — a real vacuity finding.
    //   2. A solver-limited `Unknown` (Incomplete / quantifier): the base
    //      re-solve could not decide SAT/UNSAT. This is AMBIGUOUS — the base
    //      may be perfectly consistent but contain opaque conversion terms
    //      (e.g. `bv2nat` over a SWAR computation) that plain LIA cannot
    //      model-validate without the negated goal that drove the original
    //      bit-blast proof. Demoting here discards a genuine proof.
    //
    //   3. A pathological-base signal: either the explicit
    //      BASE_RECHECK_PATHOLOGY_MESSAGE (the long-budget encoder-preserving
    //      recheck observed a hard-timeout of the detached base solve and
    //      refused to risk the live encoder) or a hard-timeout
    //      `Abort(Unknown(Timeout))` (the classic recheck churned past its
    //      envelope and the live encoder was lost to the abandoned worker).
    //      Neither says anything about the base's consistency — silently
    //      demoting discards a genuine proof. The fresh recheck runs on its
    //      OWN encoder, so it can still produce a positive SAT witness.
    //      Note a PLAIN `Unknown(Timeout)` base recheck deliberately stays
    //      non-demotable (as before this rescue existed): making every soft
    //      timeout rescue-eligible measurably multiplies fresh-recheck solver
    //      load in short-budget (unit test) regimes.
    //
    // In all cases we consult `fresh_base_recheck`, which runs the Full base
    // (faithful vacuity guard) and, when Full is itself solver-limited, falls
    // back to a preconditions-only probe (a strict relaxation of the base).
    // The fresh recheck reports `Verified`/SAT only when the preconditions are
    // satisfiable, i.e. the base is non-vacuous; a vacuous base (UNSAT
    // preconditions) yields non-`Verified` and the demotion stands. We never
    // assert the unproven goal, so a genuinely SAT/free obligation can never be
    // promoted. (#2414, #popcount)
    // Abort-shape rescue is restricted to the long-budget (harness) regime:
    // in short-budget unit-test runs the extra fresh-recheck solve blows the
    // tests' own wall-clock budgets, and the pre-change behavior there was to
    // return the abort unrescued.
    let same_encoder_abort_timeout = allow_abort_rescue
        && matches!(
            &base_result,
            ResolveContinuation::Abort(VerificationResult::Unknown(UnknownReason::Timeout))
        );
    let is_same_encoder_demotable = same_encoder_abort_timeout
        || matches!(
            &base_result,
            ResolveContinuation::Continue(VerificationResult::Unknown(reason))
                if matches!(reason, UnknownReason::SolverMessage(message)
                        if message == VACUOUS_PROOF_MESSAGE
                            || message == BASE_RECHECK_PATHOLOGY_MESSAGE)
                    || fresh_base_recheck_is_residual_solver_limited(reason)
        );
    let core_is_verified = matches!(core_result, VerificationResult::Verified(_));
    if !is_same_encoder_demotable || !core_is_verified {
        return base_result;
    }

    let Some(fresh_base_recheck) = fresh_base_recheck else {
        return base_result;
    };

    match fresh_base_recheck() {
        // Positive non-vacuity witness (SAT preconditions): the core proof
        // stands. When the same-encoder recheck hard-timed out, the live
        // encoder is still owned by the abandoned worker thread — preserve
        // the Abort shape so the caller never drives the placeholder encoder;
        // the shared pipeline records the rescued slice result without
        // touching it.
        Ok(VerificationResult::Verified(_)) if same_encoder_abort_timeout => {
            ResolveContinuation::Abort(core_result)
        }
        Ok(VerificationResult::Verified(_)) => ResolveContinuation::Continue(core_result),
        // Only the VACUOUS-message demotion may be rescued through a residual
        // solver-limited fresh recheck. A solver-limited SAME-encoder demotion
        // requires a positive non-vacuity witness (Verified/SAT) from the fresh
        // recheck; a fresh recheck that is itself solver-limited gives no such
        // witness, so the visible gap is preserved. This residual arm keeps
        // its ORIGINAL, narrower reason set (Incomplete / quantifier): a fresh
        // recheck that merely timed out never rescues anything.
        Ok(VerificationResult::Unknown(reason))
            if fresh_base_recheck_is_residual_solver_limited(&reason)
                && same_encoder_base_is_vacuous_message(&base_result) =>
        {
            ResolveContinuation::Continue(core_result)
        }
        Ok(VerificationResult::Unknown(_)) => base_result,
        // Without a positive fresh SAT witness, a hard-timed-out same-encoder
        // recheck keeps its Abort(Unknown(Timeout)) — never promote, and never
        // hand the caller a Continue over the placeholder encoder.
        Ok(_) if same_encoder_abort_timeout => base_result,
        Ok(other) => ResolveContinuation::Continue(other),
        Err(_) => base_result,
    }
}

fn same_encoder_base_is_vacuous_message(base_result: &ResolveContinuation) -> bool {
    matches!(
        base_result,
        ResolveContinuation::Continue(VerificationResult::Unknown(
            UnknownReason::SolverMessage(message)
        )) if message == VACUOUS_PROOF_MESSAGE
    )
}

/// Solver-limited reasons for which an ALREADY-RUNNING fresh base recheck may
/// escalate from the Full mode to the PreconditionsOnly relaxation (see the
/// `fresh_base_recheck` closure in `verify::function`).
///
/// `Timeout` and the detached-replay pathology marker count as solver-limited
/// HERE: the fresh Full recheck's soft caps and tight hard-timeout envelope can
/// expire while the base is perfectly consistent (ay can churn on an
/// already-decided base — e.g. rederiving an identical LRA conflict — without
/// honoring its soft timeout).
/// The escalation still only produces a positive witness when the relaxed
/// probe is genuinely SAT. This predicate deliberately does NOT govern
/// rescue ELIGIBILITY (see `fresh_base_recheck_is_residual_solver_limited`):
/// a plain timed-out same-encoder base recheck stays non-demotable.
/// (#index_range, #cell03)
pub(in crate::verify) fn fresh_base_recheck_is_solver_limited(reason: &UnknownReason) -> bool {
    matches!(reason, UnknownReason::Incomplete | UnknownReason::Timeout)
        || matches!(
            reason,
            UnknownReason::SolverMessage(message)
                if message == BASE_RECHECK_PATHOLOGY_MESSAGE
        )
        || reason.is_quantifier()
}

/// The original, narrower solver-limited set used by the same-encoder
/// demotability check and the residual VACUOUS-message rescue arm in
/// [`prefer_non_vacuous_core_on_fresh_base_recheck`]. `Timeout` is
/// deliberately excluded: the residual arm rescues a proof WITHOUT a positive
/// SAT witness (a pre-existing #popcount exception scoped to the explicit
/// VACUOUS finding), and widening it to timeouts would weaken the vacuity
/// firewall; for demotability, blanket-rescuing every soft timeout multiplies
/// fresh-recheck solver load in short-budget regimes.
fn fresh_base_recheck_is_residual_solver_limited(reason: &UnknownReason) -> bool {
    matches!(reason, UnknownReason::Incomplete) || reason.is_quantifier()
}

#[cfg(test)]
pub(in crate::verify) fn resolve_sat_result(encoder: &mut AYEncoder) -> VerificationResult {
    let result = check_sat_with_retry(encoder);
    match result {
        ay_dpll::api::SolveResult::Unsat(_) => resolve_last_unsat_with_vacuity(encoder),
        ay_dpll::api::SolveResult::Sat => {
            if let Some(result) = fail_closed_solver_context_result(encoder, "SAT counterexample") {
                return result;
            }
            let model = encoder.get_model();
            VerificationResult::Failed(Counterexample::from_encoder_model(encoder, model))
        }
        _ => unknown_result_from_encoder(encoder),
    }
}

/// Resolve a base-context (no negated postcondition) SAT check into a
/// [`VerificationResult`] with **inverted** semantics for vacuity detection.
///
/// Called AFTER a successful UNSAT proof on the negated goal. The negated
/// goal scope has been popped, so we re-solve only the base assertions:
/// - **SAT** → base is consistent → the proof was genuine → [`VerificationResult::Verified(_)`]
/// - **UNSAT** → base alone is contradictory → vacuous proof → [`VerificationResult::Unknown`]
/// - **Unknown** → cannot determine → delegate to [`unknown_result_from_encoder`]
///
/// Getting this inversion wrong is a **soundness bug**: swapping the SAT/UNSAT
/// arms would either hide vacuous proofs (reporting Verified when preconditions
/// are contradictory) or reject genuine proofs.
/// SAT-side vacuity base recheck for bases carrying the encoder's enum-payload
/// / UF-constructor bridge UNIVERSALS (#result_own).
///
/// ay's batch solver reports `Unknown(quantifier-unhandled)` — never SAT —
/// whenever these conservative definitional bridge universals are present, so
/// both the incremental `tiered_base_recheck` and the detached full-base replay
/// (`run_base_recheck_preserving_encoder`) can only churn to their hard-timeout
/// and demote an already-genuine proof. First re-materialize the bridges' ground
/// consequences at the observed receivers (entailed; pins the fresh projection/
/// coercion symbols at every observed application), then re-solve the IDENTICAL
/// base with NATIVE datatypes but EXEMPTING exactly those tracked universals.
///
/// Returns `Some(Verified)` ONLY on a MODEL-VALIDATED SAT
/// (`classify_base_replay_details` requires `was_model_validated &&
/// sat_model_validated`); any other outcome returns `None` so the caller falls
/// through to its normal recheck. SOUND: see
/// `replay_native_base_exempting_bridge_foralls`. A genuinely vacuous base
/// replays UNSAT (returns `None` here, never a false Verified), and dropping
/// constraints can never manufacture a false vacuity.
fn try_bridge_forall_exempt_base_recheck(encoder: &mut AYEncoder) -> Option<VerificationResult> {
    if !encoder.has_enum_payload_bridge_forall_axioms() {
        return None;
    }
    encoder.assert_registered_enum_payload_ground_consequences_from_assertions();
    let details = encoder.replay_native_base_exempting_bridge_foralls()?;
    match classify_base_replay_details(&details) {
        Some(result @ VerificationResult::Verified(_)) => Some(result),
        _ => None,
    }
}

pub(in crate::verify) fn resolve_base_sat_result(encoder: &mut AYEncoder) -> VerificationResult {
    if encoder.solver_panic_reason().is_some() {
        return unknown_result_from_encoder(encoder);
    }

    // Optimization (#2674): use a tiered approach for the base recheck.
    // The base context (preconditions + body constraints without the negated
    // postcondition) is typically SAT (consistent preconditions), so the solver
    // should find a model quickly. Use a short 5s probe first before committing
    // to the full solver timeout. This saves significant wall-clock time for
    // functions where the base recheck would otherwise consume the full 60s+30s
    // retry budget on an Unknown result.
    //
    // The 5s probe is shorter than the main solve's 10s tiered probe because:
    // 1. The base context is simpler (no negated postcondition, no eager
    //    negated-existential instantiations).
    // 2. SAT results (the common case) are found quickly — the solver just
    //    needs to find any satisfying assignment for the preconditions.
    // 3. UNSAT results (vacuous proofs from contradictory preconditions) are
    //    also fast — a small DPLL conflict detects the contradiction.
    // Predicate-closure obligations (e.g. PredCell `c@ == |z| ...`) carry a
    // closure defining universal whose model the incremental base recheck cannot
    // construct, so `tiered_base_recheck` churns its whole budget and returns
    // Unknown — which would demote an already-genuine proof. A fresh
    // non-incremental solve of the IDENTICAL base confirms it is SAT (consistent
    // preconditions) in well under a second. Do this FIRST, before the
    // incremental recheck burns the hard-timeout envelope and starves the fresh
    // solve. Gated to closure obligations so other tests' vacuity behavior is
    // unchanged. SOUND: only a confirmed-SAT base is accepted; a genuinely
    // vacuous (UNSAT) base fresh-parses UNSAT, never SAT. (#985, #2316)
    let has_closure_mapping_axioms = encoder.has_closure_mapping_axioms();
    if has_closure_mapping_axioms {
        // Materialize the value-level closure-get ground instances at the base's
        // observed keys so the fresh solve can confirm SAT by congruence instead
        // of having to construct a model for the closure universal (which the
        // bare solver cannot). Entailed by the closure axiom, so it does not
        // change SAT-ness — it only makes the consistency check decidable.
        encoder.assert_mapping_closure_get_instances(
            crate::encoder::ground_pool::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES,
        );
    }
    if (has_closure_mapping_axioms || encoder.has_seq_theory() || encoder.has_logic_functions())
        && encoder.batch_current_stack_is_sat()
    {
        return VerificationResult::Verified(None);
    }

    // #result_own: bases carrying the encoder's enum-payload / UF-constructor
    // bridge UNIVERSALS (e.g. `Result::as_ref/cloned/copied` over a datatype
    // payload) never fresh-solve SAT — ay's batch solver reports
    // `quantifier-unhandled` while these conservative definitional bridges are
    // present, so the incremental `tiered_base_recheck` below just churns to its
    // hard-timeout and demotes an already-genuine proof. Try the native,
    // bridge-forall-exempting fresh SAT check first.
    if let Some(result) = try_bridge_forall_exempt_base_recheck(encoder) {
        return result;
    }

    let result = tiered_base_recheck(encoder);
    match result {
        ay_dpll::api::SolveResult::Unsat(_) => VerificationResult::Unknown(
            UnknownReason::SolverMessage(VACUOUS_PROOF_MESSAGE.to_string()),
        ),
        // Base recheck SAT means the base is consistent — the original proof
        // was genuine. No proof artifact is available here (the last solver
        // result is SAT, not UNSAT). (#2629)
        ay_dpll::api::SolveResult::Sat => VerificationResult::Verified(None),
        _ => resolve_base_unknown_via_native_replay(encoder)
            .unwrap_or_else(|| unknown_result_from_encoder(encoder)),
    }
}

fn resolve_base_unknown_via_native_replay(encoder: &AYEncoder) -> Option<VerificationResult> {
    let replay_json = encoder.native_replay_json()?;
    let replay = ay_dpll::api::Solver::replay_native_replay_json_str(replay_json).ok()?;
    if let Some(validated_sat) = classify_base_replay_details(&replay) {
        return Some(validated_sat);
    }
    if !replay.result.is_unsat() {
        return None;
    }

    // Ordinary replay is a SAT/model diagnostic only. If it observes UNSAT,
    // rerun the exact artifact through AY's proof-producing strict API and
    // locally re-check every authority field before classifying the base as
    // contradictory.
    let strict =
        encoder.replay_native_json_with_strict_proofs(replay_json, BASE_RECHECK_PROBE_TIMEOUT)?;
    classify_strict_base_unsat_replay_details(&strict)
}

/// Classify a fresh native-replay re-solve of a BASE stack (negated goal
/// already popped) with inverted vacuity semantics.
///
/// - Model-VALIDATED SAT → the base is consistent → `Verified(None)`.
/// - Anything else (UNSAT, Unknown, unvalidated SAT) → `None`; the caller falls
///   through to its next recheck strategy. Fail-closed: neither an unvalidated
///   SAT nor any UNSAT from this ordinary diagnostic replay is trusted.
fn classify_base_replay_details(replay: &ay_dpll::api::SolveDetails) -> Option<VerificationResult> {
    match replay.result.result() {
        ay_dpll::api::SolveResult::Sat
            if replay.result.was_model_validated() && replay.verification.sat_model_validated =>
        {
            debug!("base recheck Unknown recovered by validated fresh native replay SAT");
            Some(VerificationResult::Verified(None))
        }
        _ => None,
    }
}

fn classify_strict_base_unsat_replay_details(
    replay: &ay_dpll::api::SolveDetails,
) -> Option<VerificationResult> {
    crate::encoder::ay_api::solve_details_have_complete_unsat_proof(replay).then(|| {
        VerificationResult::Unknown(UnknownReason::SolverMessage(
            VACUOUS_PROOF_MESSAGE.to_string(),
        ))
    })
}

/// Run a base-context vacuity recheck with a tight hard-timeout envelope (#2674).
///
/// The base recheck uses a tiered approach: 5s probe + 15s capped full solve
/// = 20s maximum. However, `run_with_hard_timeout` computes its envelope from
/// the encoder's current solver timeout (e.g., 1.5 * 60s + grace = 90.1s),
/// creating a 70s gap between the base recheck's actual time usage and the
/// hard-timeout envelope.
///
/// This wrapper temporarily sets the encoder timeout to `BASE_RECHECK_FULL_CAP`
/// before calling `run_with_hard_timeout`, so the hard-timeout envelope is
/// computed from 15s (1.5 * 15 + 0.1s = 22.6s) instead of 60s (90.1s).
/// The `tiered_base_recheck` inside `resolve_base_sat_result` still manages
/// its own probe/full timeouts internally. After the call, the original timeout
/// is restored (if the call returned Continue; Abort leaves the encoder as a
/// placeholder whose timeout doesn't matter).
///
/// For a stuck obligation where the base recheck returns Unknown, this saves
/// ~67s per base recheck call (90.1s - 22.6s), which accumulates across
/// multiple obligation slices and base recheck paths.
pub(in crate::verify) fn run_base_recheck_with_tight_timeout(
    encoder: &mut AYEncoder,
) -> ResolveContinuation {
    use crate::verify::hard_timeout::run_with_hard_timeout;

    let original_timeout = encoder.solver().timeout();
    // Set timeout to the base recheck full cap so hard_timeout_for computes a
    // tight envelope (1.5 * 15s + grace = 22.6s) instead of (1.5 * 60s + grace = 90.1s).
    // Preserve smaller caller budgets: short diagnostic requests must not be
    // stretched to 15s and overrun their enclosing test/watchdog budget.
    let base_timeout = original_timeout
        .map(|timeout| timeout.min(BASE_RECHECK_FULL_CAP))
        .unwrap_or(BASE_RECHECK_FULL_CAP);
    encoder.set_timeout(Some(base_timeout));
    let result = run_with_hard_timeout(encoder, resolve_base_sat_result);
    // Restore original timeout. On Continue, the encoder is restored from the
    // worker thread (which may have modified the timeout internally), so we
    // must explicitly restore. On Abort, the encoder is a placeholder.
    if matches!(result, ResolveContinuation::Continue(_)) {
        encoder.set_timeout(original_timeout);
    }
    result
}

/// Resolve a base-context recheck behind the tight base timeout envelope.
///
/// Fresh-base callbacks build a local encoder only for the recheck result; if
/// the hard timeout aborts, the placeholder encoder can be dropped and the
/// timeout result returned directly.
pub(in crate::verify) fn resolve_base_sat_result_with_tight_timeout(
    encoder: &mut AYEncoder,
) -> VerificationResult {
    // Fresh-base rechecks route through the encoder-preserving wrapper too:
    // a pathological base churns on a REBUILT encoder just like on the live
    // one, and the wrapper's detached validated-SAT confirm is what lets the
    // #2414 rescue actually produce its witness (#index_range). The wrapper's
    // internal long-budget gate keeps short-budget (unit test) callers on the
    // classic path. The pathology latch is local: this is a one-shot recheck.
    // The encoder here is DISPOSABLE (built solely for this recheck), so a
    // pathological detached replay still ATTEMPTS the bounded in-worker
    // recheck instead of skipping fail-closed (#basereq).
    let local_latch = std::cell::Cell::new(false);
    match run_base_recheck_preserving_encoder(
        encoder,
        &local_latch,
        BaseRecheckEncoderDisposition::Disposable,
    ) {
        ResolveContinuation::Continue(result) | ResolveContinuation::Abort(result) => result,
    }
}

/// Soft solver timeout recorded into the detached replay artifact.
///
/// 10 seconds mirrors `batch_current_stack_is_sat` (#985): typical SAT bases
/// confirm in well under a second, and CEGQI-needing closure bases were
/// measured at ~5-8s.
const BASE_RECHECK_DETACHED_SOFT_CAP: std::time::Duration = std::time::Duration::from_secs(10);

/// Hard envelope ceiling for the detached replay solve.
const BASE_RECHECK_DETACHED_ENVELOPE_CAP: std::time::Duration = std::time::Duration::from_secs(12);

/// Hard envelope for a detached replay solve with the given soft cap:
/// 1.5x soft cap + scheduling grace, ceilinged at
/// [`BASE_RECHECK_DETACHED_ENVELOPE_CAP`]. Scaling with the encoder's own
/// timeout keeps short-budget callers (unit tests, diagnostic probes) from
/// stalling up to 12s on a pathological replay of a small stack.
fn detached_replay_envelope(soft_cap: std::time::Duration) -> std::time::Duration {
    soft_cap
        .checked_add(soft_cap / 2)
        .and_then(|value| value.checked_add(std::time::Duration::from_millis(100)))
        .unwrap_or(BASE_RECHECK_DETACHED_ENVELOPE_CAP)
        .min(BASE_RECHECK_DETACHED_ENVELOPE_CAP)
}

/// Whether this encoder runs in the long-budget (harness) regime where the
/// encoder-preserving base recheck and its abort-shape rescue are worthwhile.
/// Mirrors the base-recheck tiering threshold.
pub(in crate::verify) fn base_recheck_long_budget(encoder: &AYEncoder) -> bool {
    base_recheck_long_budget_timeout(encoder.solver().timeout())
}

/// Timeout-value form of [`base_recheck_long_budget`] for callers that hold a
/// request/base timeout rather than a live encoder.
pub(in crate::verify) fn base_recheck_long_budget_timeout(
    timeout: Option<std::time::Duration>,
) -> bool {
    matches!(timeout, Some(timeout) if timeout >= BASE_RECHECK_PROBE_MIN_TIMEOUT)
}

/// Who owns the encoder handed to [`run_base_recheck_preserving_encoder`],
/// i.e. what a hard-timed-out in-worker recheck would actually cost (#basereq).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(in crate::verify) enum BaseRecheckEncoderDisposition {
    /// The caller's LIVE incremental encoder: losing it to an abandoned
    /// hard-timeout worker permanently costs every remaining obligation slice,
    /// so a pathological detached base replay must SKIP the in-worker recheck
    /// and report the rescue-eligible pathology demotion instead.
    Live,
    /// A DISPOSABLE encoder built solely for a fresh base recheck (#2414
    /// rescue callbacks): losing it costs nothing, so a pathological detached
    /// base replay still ATTEMPTS the bounded in-worker recheck — that is
    /// where the recovery lanes live (closure-instance materialization, the
    /// #result_own bridge-forall exemption, the tiered incremental solve with
    /// its ground-instance flush, and the validated fresh-native-replay
    /// recovery) — before giving up on a fresh witness.
    Disposable,
}

/// Collapse the bounded in-worker recheck ATTEMPT that runs after the
/// detached replay of a pathological base hard-timed out on a DISPOSABLE
/// fresh-recheck encoder (#basereq).
///
/// Only two outcomes are decisive and pass through untouched:
/// - `Verified` — a positive non-vacuity witness produced by the EXISTING,
///   unchanged acceptance gates in `resolve_base_sat_result` (closure-lane
///   confirmed SAT, bridge-forall-exempt model-validated replay SAT, tiered
///   incremental SAT, or the validated fresh-native-replay recovery). This can
///   only LIFT the pathology demotion of an obligation whose goal was already
///   proven UNSAT; it never manufactures an accept.
/// - the explicit [`VACUOUS_PROOF_MESSAGE`] — the attempt proved the base
///   UNSAT, so the fail-closed vacuity demotion must stand.
///
/// Every other outcome (soft solver-limited Unknowns, a hard-timeout `Abort`)
/// maps back to [`BASE_RECHECK_PATHOLOGY_MESSAGE`], preserving the exact
/// pre-attempt diagnostic, the fresh-recheck memoization behavior (the
/// message is a `SolverMessage`, so multi-slice callers cache it instead of
/// re-churning per slice) and the PreconditionsOnly escalation triggers. The
/// continuation shape (Continue/Abort) is preserved so a placeholder encoder
/// left behind by an aborted attempt is never presented as live.
fn collapse_disposable_recheck_attempt(attempt: ResolveContinuation) -> ResolveContinuation {
    match attempt {
        ResolveContinuation::Continue(result @ VerificationResult::Verified(_)) => {
            debug!(
                "pathological base solve rescued by the bounded in-worker recheck \
                 attempt on the disposable fresh-recheck encoder (#2414)"
            );
            ResolveContinuation::Continue(result)
        }
        ResolveContinuation::Continue(VerificationResult::Unknown(
            UnknownReason::SolverMessage(message),
        )) if message == VACUOUS_PROOF_MESSAGE => ResolveContinuation::Continue(
            VerificationResult::Unknown(UnknownReason::SolverMessage(message)),
        ),
        attempt => {
            debug!(
                "bounded in-worker recheck attempt after a pathological detached base \
                 solve was not decisive; keeping the pathological-base demotion (#2414)"
            );
            let demotion = VerificationResult::Unknown(UnknownReason::SolverMessage(
                BASE_RECHECK_PATHOLOGY_MESSAGE.to_string(),
            ));
            match attempt {
                ResolveContinuation::Continue(_) => ResolveContinuation::Continue(demotion),
                ResolveContinuation::Abort(_) => ResolveContinuation::Abort(demotion),
            }
        }
    }
}

/// Base vacuity recheck that NEVER risks the caller's live encoder.
///
/// `run_base_recheck_with_tight_timeout` hands the live encoder to a
/// hard-timeout worker; when ay churns past its soft caps (observed:
/// rederiving an identical LRA contradictory_variable_bounds conflict
/// thousands of times), the envelope expires and the encoder is permanently
/// lost to the abandoned worker — killing every remaining obligation slice of
/// an already-proven function (#index_range, #cell03).
///
/// This wrapper first runs the base recheck DETACHED: it flushes the current
/// base stack into a native replay artifact (pure serialization on the caller
/// thread) and re-solves it on a fresh solver owned by the worker. Outcomes:
///
/// - **validated SAT** → base consistent → the proof was genuine → `Verified`.
/// - **UNSAT** → base contradictory → VACUOUS demotion (fail-closed;
///   identical stack, so a genuinely vacuous base can never confirm SAT).
/// - **hard-timeout** → the base solve is pathological. On a
///   [`BaseRecheckEncoderDisposition::Live`] encoder, running the classic
///   encoder-owning recheck would very likely lose the live encoder too:
///   latch `pathology_latch` (so the caller's REMAINING slices skip straight
///   to the rescue instead of burning budget / leaking more workers) and
///   report a solver-limited `Unknown(Timeout)` — the demotion stands unless
///   the #2414 fresh base recheck (its own encoder) produces a positive SAT
///   witness. On a [`BaseRecheckEncoderDisposition::Disposable`] encoder
///   (the fresh rescue itself), losing the encoder costs nothing, so ATTEMPT
///   the bounded classic recheck for a fresh witness instead of skipping —
///   see [`collapse_disposable_recheck_attempt`] (#basereq).
/// - **inconclusive** (fast Unknown / parse failure / no worker) → fall back
///   to the classic incremental recheck, preserving its full decision power.
///
/// Live callers must only use this when a fresh base recheck rescue is
/// available downstream; otherwise the classic recheck's full decision power
/// is strictly better.
pub(in crate::verify) fn run_base_recheck_preserving_encoder(
    encoder: &mut AYEncoder,
    pathology_latch: &std::cell::Cell<bool>,
    disposition: BaseRecheckEncoderDisposition,
) -> ResolveContinuation {
    use crate::verify::hard_timeout::{
        run_detached_replay_solve_with_hard_timeout, DetachedReplayOutcome,
    };

    if encoder.solver_panic_reason().is_some() {
        return ResolveContinuation::Continue(unknown_result_from_encoder(encoder));
    }

    // #result_own: for bases carrying the enum-payload / UF-ctor bridge
    // universals, the detached FULL-base replay below cannot return SAT (ay
    // reports `quantifier-unhandled`) and — on a larger base such as
    // `Result::transpose` — hard-times-out, latching the pathology demotion
    // before the in-worker recheck (and its exemption) ever runs. Try the
    // native, bridge-forall-exempting fresh SAT check FIRST, so these bases are
    // confirmed consistent in milliseconds instead of demoted. Falls through to
    // the detached/classic path on anything but a model-validated SAT.
    if let Some(result) = try_bridge_forall_exempt_base_recheck(encoder) {
        return ResolveContinuation::Continue(result);
    }

    // Long-budget regime only: the detached phase exists to protect
    // multi-slice HARNESS obligations (solver timeouts of 60-150s) whose
    // pathological base solves would otherwise eat the live encoder. Short-
    // budget callers (unit tests, diagnostic probes — the same regime that
    // skips base-recheck tiering) keep the classic recheck's exact behavior:
    // spawning an extra fresh solver per verified slice there measurably
    // starves the suite's worker pool and wall-clock budgets.
    let original_timeout = encoder.solver().timeout();
    if !base_recheck_long_budget(encoder) {
        return run_base_recheck_with_tight_timeout(encoder);
    }

    // An earlier slice of this obligation already hit a pathological base
    // solve. Both the detached replay and the classic incremental recheck of
    // the SAME base would churn again (and the classic one would eat the live
    // encoder), so skip straight to the demotable solver-limited Unknown that
    // routes to the #2414 fresh rescue.
    if pathology_latch.get() {
        debug!(
            "base recheck pathology latched for this obligation; deferring \
             directly to the fresh base recheck rescue (#2414)"
        );
        return ResolveContinuation::Continue(VerificationResult::Unknown(
            UnknownReason::SolverMessage(BASE_RECHECK_PATHOLOGY_MESSAGE.to_string()),
        ));
    }

    // Export the base stack with a tight soft cap recorded in the artifact so
    // the detached fresh solve times itself out well inside the envelope.
    let detached_soft_cap = original_timeout
        .map(|timeout| timeout.min(BASE_RECHECK_DETACHED_SOFT_CAP))
        .unwrap_or(BASE_RECHECK_DETACHED_SOFT_CAP);
    encoder.set_timeout(Some(detached_soft_cap));
    encoder.refresh_native_replay_json();
    encoder.set_timeout(original_timeout);

    if let Some(replay_json) = encoder.native_replay_json().map(str::to_owned) {
        match run_detached_replay_solve_with_hard_timeout(
            replay_json,
            detached_replay_envelope(detached_soft_cap),
        ) {
            DetachedReplayOutcome::Completed(Some(details)) => {
                if let Some(result) = classify_base_replay_details(&details) {
                    return ResolveContinuation::Continue(result);
                }
                // Fast inconclusive replay: the classic incremental recheck
                // may still decide (warm solver state, closure ground
                // instances), so fall through.
            }
            DetachedReplayOutcome::TimedOut => {
                pathology_latch.set(true);
                if disposition == BaseRecheckEncoderDisposition::Disposable {
                    // #basereq: this encoder was built solely for the fresh
                    // base recheck — losing it to a hard-timeout worker costs
                    // nothing. Instead of skipping fail-closed (which made the
                    // "fresh base recheck witness required" demotion terminal:
                    // the rescue's own sub-solve was the thing skipping),
                    // attempt the bounded classic in-worker recheck under its
                    // existing tight envelope (`BASE_RECHECK_FULL_CAP`,
                    // 1.5x + grace = 22.6s). Acceptance gates are unchanged;
                    // a non-decisive attempt keeps the pathology demotion.
                    debug!(
                        "detached base replay solve hard-timed out on a disposable \
                         fresh-recheck encoder; attempting the bounded in-worker \
                         base recheck for a fresh witness (#2414, #basereq)"
                    );
                    return collapse_disposable_recheck_attempt(
                        run_base_recheck_with_tight_timeout(encoder),
                    );
                }
                debug!(
                    "detached base replay solve hard-timed out; reporting the \
                     pathological-base demotion instead of risking the live encoder (#2414)"
                );
                return ResolveContinuation::Continue(VerificationResult::Unknown(
                    UnknownReason::SolverMessage(BASE_RECHECK_PATHOLOGY_MESSAGE.to_string()),
                ));
            }
            DetachedReplayOutcome::Completed(None) | DetachedReplayOutcome::Unavailable => {}
        }
    }

    run_base_recheck_with_tight_timeout(encoder)
}

/// Short probe timeout for the base recheck (#2674).
///
/// 5 seconds is sufficient: SAT base contexts (the common case) resolve in
/// <1s because the solver just needs any satisfying assignment. UNSAT base
/// contexts (contradictory preconditions) are also fast via conflict analysis.
/// Only genuinely hard quantifier-laden bases need the full timeout.
const BASE_RECHECK_PROBE_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(5);

/// Minimum solver timeout before the base recheck probe is worthwhile.
const BASE_RECHECK_PROBE_MIN_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(10);

/// Maximum timeout for the base recheck full solve after the probe (#2674).
///
/// When the base recheck 5s probe returns Unknown, the full solve is capped
/// at 15s instead of using the original solver timeout (e.g., 60s). Since
/// Unknown base results remain visible gaps, spending more than 15s on the
/// base recheck is wasted wall-clock time.
/// For a 60s solver timeout, this saves up to 45s per obligation slice.
const BASE_RECHECK_FULL_CAP: std::time::Duration = std::time::Duration::from_secs(15);

/// Tiered base recheck: short probe then full solve (#2674).
///
/// Mirrors `tiered_check_sat` but with a shorter probe timeout (5s vs 10s)
/// because the base context is simpler than the full negated-goal context.
///
/// The full solve after the probe skips the retry (#2674): the base recheck
/// is a vacuity guard, not the primary proof. If it returns Unknown, the
/// result remains a visible verification gap rather than a clean proof.
fn tiered_base_recheck(encoder: &mut AYEncoder) -> ay_dpll::api::SolveResult {
    let original_timeout = encoder.solver().timeout();

    let should_tier = match original_timeout {
        Some(timeout) if timeout >= BASE_RECHECK_PROBE_MIN_TIMEOUT => true,
        _ => false,
    };

    if !should_tier {
        // For short timeouts, a single check_sat is sufficient.
        // Skip retry: the base recheck Unknown result is handled by
        // prefer_non_vacuous_core_on_incomplete_base.
        return encoder.check_sat();
    }

    // Phase 1: Short probe.
    encoder.set_timeout(Some(BASE_RECHECK_PROBE_TIMEOUT));
    let probe_result = encoder.check_sat();
    encoder.set_timeout(original_timeout);

    match probe_result {
        ay_dpll::api::SolveResult::Unknown => {
            tracing::debug!(
                probe_timeout_ms = BASE_RECHECK_PROBE_TIMEOUT.as_millis(),
                "base recheck: probe returned Unknown, proceeding to capped full solve (#2674)"
            );
            // Capped full solve without retry (#2674): the base recheck is a
            // vacuity guard. Unknown results are surfaced as visible gaps, so
            // we cap the full solve at 15s instead of the original solver
            // timeout (e.g., 60s) while still giving the solver time to find
            // most SAT/UNSAT results.
            //
            // The 15s cap was chosen because:
            // - SAT base contexts (the common case) resolve in <1s
            // - UNSAT base contexts are caught by the 5s probe
            // - Only quantifier-laden bases need more time, and those remain
            //   visible Unknowns if the capped solve cannot classify them
            let capped_timeout = original_timeout.map(|t| t.min(BASE_RECHECK_FULL_CAP));
            encoder.set_timeout(capped_timeout);
            let result = encoder.check_sat();
            encoder.set_timeout(original_timeout);
            result
        }
        definitive => definitive,
    }
}

/// Resolve a negated-postcondition SAT check into a [`VerificationResult`]
/// without vacuity checking.
///
/// Standard semantics:
/// - **UNSAT** → postcondition proved → [`VerificationResult::Verified(_)`]
/// - **SAT** → counterexample found → [`VerificationResult::Failed`]
/// - **Unknown** → delegate to [`unknown_result_from_encoder`]
///
/// Uses [`tiered_check_sat`] (#2674 Phase 4) for the full axiom path: a
/// short initial probe resolves most obligations quickly without consuming
/// the full solver timeout budget.
pub(in crate::verify) fn resolve_sat_result_without_vacuity(
    encoder: &mut AYEncoder,
) -> VerificationResult {
    if encoder.solver_panic_reason().is_some() {
        return unknown_result_from_encoder(encoder);
    }

    let result = tiered_check_sat(encoder);
    match result {
        ay_dpll::api::SolveResult::Unsat(_) => resolve_unsat_without_vacuity(encoder),
        ay_dpll::api::SolveResult::Sat => {
            if let Some(result) = fail_closed_solver_context_result(encoder, "SAT counterexample") {
                return result;
            }
            let model = encoder.get_model();
            VerificationResult::Failed(Counterexample::from_encoder_model(encoder, model))
        }
        _ => unknown_result_from_encoder(encoder),
    }
}

/// Attach proof authority to an already-accepted UNSAT on the current stack.
///
/// The long-lived incremental encoder deliberately runs with
/// `set_produce_proofs(false)` (`encoder/constructors.rs`), so
/// [`extract_proof_summary`] returns `None` for an ordinary incremental
/// `Unsat` and the verdict reaches the mandatory authority boundary as a
/// certificate-free `Verified(None)` — demoted to `Unknown(ProofTrusted)`
/// even though the refutation is real. That constructor's own comment states
/// the contract: "authority lanes use isolated strict replay and attach its
/// artifact". This is that attachment, and it is the same helper the loop
/// lane already uses for an accepted loop UNSAT
/// (`verify/loops/encoder_setup.rs::verified_with_exact_strict_replay`).
///
/// It cannot manufacture a verdict. Every caller has already established an
/// accepted UNSAT for the current scoped obligation; the replay adds and drops
/// nothing, and `authorize_current_stack_unsat_with_strict_proof` yields
/// `Some` only when the identical stack is again UNSAT with a fully verified,
/// trust-free, hole-free certificate. A declined replay leaves `None`, i.e.
/// exactly the `Verified(None)` this path produced before, and the boundary
/// downgrades it as before.
pub(super) fn accepted_unsat_proof_authority(
    encoder: &mut AYEncoder,
) -> Option<crate::verify::ProofCertificateSummary> {
    if let Some(summary) = extract_proof_summary(encoder.solver()) {
        return Some(summary);
    }
    encoder.authorize_current_stack_unsat_with_strict_proof()
}

fn resolve_unsat_without_vacuity(encoder: &mut AYEncoder) -> VerificationResult {
    if has_accepted_unsat_evidence(encoder) {
        let summary = accepted_unsat_proof_authority(encoder);
        return VerificationResult::Verified(summary);
    }

    debug!(
        reason = ?rejected_unsat_evidence_reason(encoder),
        "UNSAT solve lacked accepted evidence; rerunning with UNSAT shortcuts disabled"
    );

    let result = encoder.with_negated_goal_label_prefix(
        PROOF_REQUIRED_NEGATED_GOAL_LABEL_PREFIX.to_string(),
        tiered_check_sat,
    );
    match result {
        ay_dpll::api::SolveResult::Unsat(_) if has_accepted_unsat_evidence(encoder) => {
            let summary = accepted_unsat_proof_authority(encoder);
            VerificationResult::Verified(summary)
        }
        ay_dpll::api::SolveResult::Unsat(_) => {
            VerificationResult::Unknown(rejected_unsat_evidence_reason(encoder))
        }
        ay_dpll::api::SolveResult::Sat => {
            if let Some(result) = fail_closed_solver_context_result(encoder, "SAT counterexample") {
                return result;
            }
            let model = encoder.get_model();
            VerificationResult::Failed(Counterexample::from_encoder_model(encoder, model))
        }
        _ => unknown_result_from_encoder(encoder),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{tests::helpers::*, verify::hard_timeout::ResolveContinuation};

    // ── collect_body_let_assume_assumptions ──────────────────────────

    #[test]
    fn test_collect_let_assume_empty_on_non_let_assume() {
        let expr = gt(var("x"), int(0));
        let assumptions = collect_body_let_assume_assumptions(&expr);
        assert!(assumptions.is_empty());
    }

    #[test]
    fn test_collect_let_assume_single() {
        let assumption = gt(var("x"), int(0));
        let expr = let_assume(assumption.clone(), var("y"));
        let assumptions = collect_body_let_assume_assumptions(&expr);
        assert_eq!(assumptions.len(), 1);
        // The assumption should be the gt(var("x"), int(0)) expression.
        assert!(
            matches!(
                assumptions[0],
                PureExpr::BinOp(_, trust_wp_core::formula::BinOp::Gt, _)
            ),
            "expected a Gt BinOp assumption"
        );
    }

    #[test]
    fn test_collect_let_assume_nested() {
        // LetAssume(a1, LetAssume(a2, body))
        let inner = let_assume(eq(var("y"), int(1)), var("z"));
        let outer = let_assume(gt(var("x"), int(0)), inner);
        let assumptions = collect_body_let_assume_assumptions(&outer);
        assert_eq!(
            assumptions.len(),
            2,
            "should find both LetAssume assumptions"
        );
    }

    #[test]
    fn test_collect_let_assume_inside_binop() {
        // and(let_assume(a, body), true) — LetAssume inside a BinOp
        let assume_expr = let_assume(bool_expr(true), var("x"));
        let expr = and(assume_expr, bool_expr(true));
        let assumptions = collect_body_let_assume_assumptions(&expr);
        assert_eq!(assumptions.len(), 1);
    }

    #[test]
    fn test_collect_let_assume_int_literal_empty() {
        let expr = int(42);
        let assumptions = collect_body_let_assume_assumptions(&expr);
        assert!(assumptions.is_empty());
    }

    // ── prefer_non_vacuous_core_on_incomplete_base ──────────────────

    #[test]
    fn test_incomplete_base_recheck_is_not_overridden() {
        let core = VerificationResult::Verified(None);
        let base =
            ResolveContinuation::Continue(VerificationResult::Unknown(UnknownReason::Incomplete));
        let result = prefer_non_vacuous_core_on_incomplete_base(core, base);
        assert!(
            matches!(
                result,
                ResolveContinuation::Continue(VerificationResult::Unknown(
                    UnknownReason::Incomplete
                ))
            ),
            "solver-limited base recheck must remain a visible gap"
        );
    }

    #[test]
    fn test_quantifier_limited_base_recheck_is_not_overridden() {
        let core = VerificationResult::Verified(None);
        let base = ResolveContinuation::Continue(VerificationResult::Unknown(
            UnknownReason::QuantifierRoundLimit,
        ));
        let result = prefer_non_vacuous_core_on_incomplete_base(core, base);
        assert!(
            matches!(
                result,
                ResolveContinuation::Continue(VerificationResult::Unknown(
                    UnknownReason::QuantifierRoundLimit
                ))
            ),
            "quantifier-limited base recheck must remain a visible gap"
        );
    }

    #[test]
    fn test_do_not_override_vacuous_proof_message() {
        let core = VerificationResult::Verified(None);
        let base = ResolveContinuation::Continue(VerificationResult::Unknown(
            UnknownReason::SolverMessage(VACUOUS_PROOF_MESSAGE.to_string()),
        ));
        let result = prefer_non_vacuous_core_on_incomplete_base(core, base);
        // The vacuity signal must not be overridden.
        assert!(
            matches!(
                result,
                ResolveContinuation::Continue(VerificationResult::Unknown(
                    UnknownReason::SolverMessage(ref msg)
                )) if msg == VACUOUS_PROOF_MESSAGE
            ),
            "vacuous proof message should not be overridden"
        );
    }

    #[test]
    fn test_prefer_base_when_core_is_not_verified() {
        let core = VerificationResult::Unknown(UnknownReason::Incomplete);
        let base =
            ResolveContinuation::Continue(VerificationResult::Unknown(UnknownReason::Incomplete));
        let result = prefer_non_vacuous_core_on_incomplete_base(core, base);
        // When core is inconclusive, base should be returned as-is.
        assert!(
            matches!(
                result,
                ResolveContinuation::Continue(VerificationResult::Unknown(
                    UnknownReason::Incomplete
                ))
            ),
            "should return base when core is inconclusive"
        );
    }

    #[test]
    fn test_prefer_base_when_base_is_verified() {
        let core = VerificationResult::Verified(Some(crate::verify::ProofCertificateSummary {
            strict_verified: true,
            restricted_rule_subset: false,
            trust_count: 0,
            trust_fallback_count: 0,
            hole_count: 0,
            theory_lemma_count: 1,
            resolution_count: 17,
            farkas_certificate_count: 1,
            lrat_present: true,
            alethe_text: Some("strict-core-proof".to_string()),
        }));
        let base = ResolveContinuation::Continue(VerificationResult::Verified(None));
        let result = prefer_non_vacuous_core_on_incomplete_base(core, base);
        let ResolveContinuation::Continue(VerificationResult::Verified(Some(summary))) = result
        else {
            panic!("Verified base must retain the scoped proof certificate");
        };
        assert_eq!(summary.resolution_count, 17);
        assert_eq!(summary.alethe_text.as_deref(), Some("strict-core-proof"));
    }

    #[test]
    fn test_prefer_base_when_base_is_abort() {
        let core = VerificationResult::Verified(None);
        let base = ResolveContinuation::Abort(VerificationResult::Unknown(UnknownReason::Timeout));
        let result = prefer_non_vacuous_core_on_incomplete_base(core, base);
        assert!(
            matches!(result, ResolveContinuation::Abort(_)),
            "Abort should pass through unchanged"
        );
    }

    #[test]
    fn detached_base_pathology_is_solver_limited_for_fresh_relaxation() {
        let reason = UnknownReason::SolverMessage(BASE_RECHECK_PATHOLOGY_MESSAGE.to_string());
        assert!(
            fresh_base_recheck_is_solver_limited(&reason),
            "a detached Full-base hard timeout must reach the preconditions-only SAT witness lane"
        );
    }

    // ── prefer_non_vacuous_core_on_fresh_base_recheck ───────────────

    #[test]
    fn test_fresh_recheck_passes_through_non_vacuous_base() {
        let core = VerificationResult::Verified(None);
        let base = ResolveContinuation::Continue(VerificationResult::Verified(None));
        let result = prefer_non_vacuous_core_on_fresh_base_recheck(core, base, None, true);
        assert!(
            matches!(
                result,
                ResolveContinuation::Continue(VerificationResult::Verified(_))
            ),
            "non-vacuous base should pass through"
        );
    }

    #[test]
    fn test_fresh_recheck_passes_through_when_core_not_verified() {
        let core = VerificationResult::Unknown(UnknownReason::Incomplete);
        let base = ResolveContinuation::Continue(VerificationResult::Unknown(
            UnknownReason::SolverMessage(VACUOUS_PROOF_MESSAGE.to_string()),
        ));
        let result = prefer_non_vacuous_core_on_fresh_base_recheck(core, base, None, true);
        // Core is inconclusive, so base should be returned as-is.
        assert!(
            matches!(
                result,
                ResolveContinuation::Continue(VerificationResult::Unknown(_))
            ),
            "should return vacuous base when core is inconclusive"
        );
    }

    #[test]
    fn test_fresh_recheck_returns_vacuous_base_when_no_recheck_fn() {
        let core = VerificationResult::Verified(None);
        let base = ResolveContinuation::Continue(VerificationResult::Unknown(
            UnknownReason::SolverMessage(VACUOUS_PROOF_MESSAGE.to_string()),
        ));
        let result = prefer_non_vacuous_core_on_fresh_base_recheck(core, base, None, true);
        assert!(
            matches!(
                result,
                ResolveContinuation::Continue(VerificationResult::Unknown(_))
            ),
            "vacuous base without recheck fn should stay vacuous"
        );
    }

    #[test]
    fn test_fresh_recheck_calls_recheck_and_accepts_verified() {
        let core = VerificationResult::Verified(None);
        let base = ResolveContinuation::Continue(VerificationResult::Unknown(
            UnknownReason::SolverMessage(VACUOUS_PROOF_MESSAGE.to_string()),
        ));
        let recheck_fn: Box<FreshBaseRecheckFn<'_>> =
            Box::new(|| Ok(VerificationResult::Verified(None)));
        let result = prefer_non_vacuous_core_on_fresh_base_recheck(
            core,
            base,
            Some(recheck_fn.as_ref()),
            true,
        );
        assert!(
            matches!(
                result,
                ResolveContinuation::Continue(VerificationResult::Verified(_))
            ),
            "fresh recheck returning Verified should rescue core result"
        );
    }

    #[test]
    fn test_fresh_recheck_calls_recheck_and_accepts_incomplete() {
        let core = VerificationResult::Verified(None);
        let base = ResolveContinuation::Continue(VerificationResult::Unknown(
            UnknownReason::SolverMessage(VACUOUS_PROOF_MESSAGE.to_string()),
        ));
        let recheck_fn: Box<FreshBaseRecheckFn<'_>> =
            Box::new(|| Ok(VerificationResult::Unknown(UnknownReason::Incomplete)));
        let result = prefer_non_vacuous_core_on_fresh_base_recheck(
            core,
            base,
            Some(recheck_fn.as_ref()),
            true,
        );
        assert!(
            matches!(
                result,
                ResolveContinuation::Continue(VerificationResult::Verified(_))
            ),
            "fresh recheck returning Incomplete should rescue core result"
        );
    }

    #[test]
    fn test_fresh_recheck_calls_recheck_and_accepts_quantifier_unhandled() {
        let core = VerificationResult::Verified(None);
        let base = ResolveContinuation::Continue(VerificationResult::Unknown(
            UnknownReason::SolverMessage(VACUOUS_PROOF_MESSAGE.to_string()),
        ));
        let recheck_fn: Box<FreshBaseRecheckFn<'_>> = Box::new(|| {
            Ok(VerificationResult::Unknown(
                UnknownReason::QuantifierUnhandled,
            ))
        });
        let result = prefer_non_vacuous_core_on_fresh_base_recheck(
            core,
            base,
            Some(recheck_fn.as_ref()),
            true,
        );
        assert!(
            matches!(
                result,
                ResolveContinuation::Continue(VerificationResult::Verified(_))
            ),
            "fresh recheck returning QuantifierUnhandled should rescue core result"
        );
    }

    #[test]
    fn test_fresh_recheck_calls_recheck_and_returns_failed() {
        let core = VerificationResult::Verified(None);
        let base = ResolveContinuation::Continue(VerificationResult::Unknown(
            UnknownReason::SolverMessage(VACUOUS_PROOF_MESSAGE.to_string()),
        ));
        let recheck_fn: Box<FreshBaseRecheckFn<'_>> =
            Box::new(|| Ok(VerificationResult::Failed(Counterexample::empty())));
        let result = prefer_non_vacuous_core_on_fresh_base_recheck(
            core,
            base,
            Some(recheck_fn.as_ref()),
            true,
        );
        assert!(
            matches!(
                result,
                ResolveContinuation::Continue(VerificationResult::Failed(_))
            ),
            "fresh recheck returning Failed should replace core"
        );
    }

    #[test]
    fn test_fresh_recheck_error_returns_vacuous_base() {
        let core = VerificationResult::Verified(None);
        let base = ResolveContinuation::Continue(VerificationResult::Unknown(
            UnknownReason::SolverMessage(VACUOUS_PROOF_MESSAGE.to_string()),
        ));
        let recheck_fn: Box<FreshBaseRecheckFn<'_>> = Box::new(|| {
            Err(crate::error::EncodingError::Unsupported {
                message: "test error".to_string(),
                span: None,
                contract_text: None,
            })
        });
        let result = prefer_non_vacuous_core_on_fresh_base_recheck(
            core,
            base,
            Some(recheck_fn.as_ref()),
            true,
        );
        assert!(
            matches!(
                result,
                ResolveContinuation::Continue(VerificationResult::Unknown(_))
            ),
            "error in recheck should fall back to vacuous base"
        );
    }

    // ── unknown_result_from_encoder ─────────────────────────────────

    #[test]
    fn test_unknown_result_no_panic_no_reason() {
        let encoder = AYEncoder::new();
        let result = unknown_result_from_encoder(&encoder);
        // Fresh encoder has no panic, no cached reason — should produce Unspecified.
        assert!(
            matches!(
                result,
                VerificationResult::Unknown(UnknownReason::Unspecified)
            ),
            "fresh encoder should produce Unknown(Unspecified), got {result:?}"
        );
    }

    // ── VACUOUS_PROOF_MESSAGE ───────────────────────────────────────

    #[test]
    fn test_vacuous_proof_message_is_stable() {
        assert!(
            VACUOUS_PROOF_MESSAGE.contains("vacuous"),
            "message should contain 'vacuous'"
        );
        assert!(
            VACUOUS_PROOF_MESSAGE.contains("UNSAT"),
            "message should contain 'UNSAT'"
        );
    }

    // ── resolve_base_sat_result (via encoder) ───────────────────────

    #[test]
    fn test_resolve_base_sat_on_trivially_unsat() {
        // Declare x, assert x > 0 AND x < 0 — base is UNSAT (contradictory).
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", ay_dpll::api::Sort::Int)
            .unwrap();
        let zero = encoder.solver_mut().int_const(0);
        let gt_zero = encoder.solver_mut().gt(x, zero);
        encoder.assert_term(gt_zero);
        let lt_zero = encoder.solver_mut().lt(x, zero);
        encoder.assert_term(lt_zero);

        let result = resolve_base_sat_result(&mut encoder);
        assert!(
            matches!(
                result,
                VerificationResult::Unknown(UnknownReason::SolverMessage(ref msg))
                if msg == VACUOUS_PROOF_MESSAGE
            ),
            "UNSAT base should produce vacuous proof message, got {result:?}"
        );
    }

    #[test]
    fn test_resolve_base_sat_on_trivially_sat() {
        // Declare x, assert x > 0 — base is SAT (consistent).
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", ay_dpll::api::Sort::Int)
            .unwrap();
        let zero = encoder.solver_mut().int_const(0);
        let gt_zero = encoder.solver_mut().gt(x, zero);
        encoder.assert_term(gt_zero);

        let result = resolve_base_sat_result(&mut encoder);
        assert!(
            matches!(result, VerificationResult::Verified(None)),
            "SAT base should produce Verified(None), got {result:?}"
        );
    }

    // ── resolve_sat_result_without_vacuity (via encoder) ────────────

    #[test]
    fn test_resolve_without_vacuity_unsat() {
        // Assert false — UNSAT.
        let mut encoder = AYEncoder::new();
        let f = encoder.solver_mut().bool_const(false);
        encoder.assert_term(f);

        let result = resolve_sat_result_without_vacuity(&mut encoder);
        assert!(
            matches!(result, VerificationResult::Verified(_)),
            "UNSAT should be Verified, got {result:?}"
        );
    }

    #[test]
    fn test_resolve_without_vacuity_sat() {
        // Assert x > 0 — SAT (counterexample exists).
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", ay_dpll::api::Sort::Int)
            .unwrap();
        let zero = encoder.solver_mut().int_const(0);
        let gt = encoder.solver_mut().gt(x, zero);
        encoder.assert_term(gt);

        let result = resolve_sat_result_without_vacuity(&mut encoder);
        assert!(
            matches!(result, VerificationResult::Failed(_)),
            "SAT should be Failed, got {result:?}"
        );
    }

    // ── check_sat_with_retry ────────────────────────────────────────

    #[test]
    fn test_check_sat_with_retry_returns_unsat() {
        let mut encoder = AYEncoder::new();
        let f = encoder.solver_mut().bool_const(false);
        encoder.assert_term(f);
        let result = check_sat_with_retry(&mut encoder);
        assert!(
            matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
            "expected Unsat, got {result:?}"
        );
    }

    #[test]
    fn test_check_sat_with_retry_returns_sat() {
        let mut encoder = AYEncoder::new();
        let t = encoder.solver_mut().bool_const(true);
        encoder.assert_term(t);
        let result = check_sat_with_retry(&mut encoder);
        assert!(
            matches!(result, ay_dpll::api::SolveResult::Sat),
            "expected Sat, got {result:?}"
        );
    }

    // ── tiered_check_sat ───────────────────────────────────────────────

    #[test]
    fn test_tiered_check_sat_unsat_no_timeout() {
        // Without a timeout, tiered_check_sat should fall back to
        // check_sat_with_retry and still return the correct result.
        let mut encoder = AYEncoder::new();
        let f = encoder.solver_mut().bool_const(false);
        encoder.assert_term(f);

        let result = tiered_check_sat(&mut encoder);
        assert!(
            matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
            "expected Unsat without timeout, got {result:?}"
        );
    }

    #[test]
    fn test_tiered_check_sat_sat_no_timeout() {
        // Without a timeout, tiered_check_sat should fall back to
        // check_sat_with_retry and still return the correct result.
        let mut encoder = AYEncoder::new();
        let t = encoder.solver_mut().bool_const(true);
        encoder.assert_term(t);

        let result = tiered_check_sat(&mut encoder);
        assert!(
            matches!(result, ay_dpll::api::SolveResult::Sat),
            "expected Sat without timeout, got {result:?}"
        );
    }

    #[test]
    fn test_tiered_check_sat_unsat_with_short_timeout() {
        // With a short timeout (< TIERED_PROBE_MIN_FULL_TIMEOUT), tiered
        // solving is skipped and we fall back to check_sat_with_retry.
        let mut encoder = AYEncoder::new();
        encoder.set_timeout(Some(std::time::Duration::from_secs(5)));
        let f = encoder.solver_mut().bool_const(false);
        encoder.assert_term(f);

        let result = tiered_check_sat(&mut encoder);
        assert!(
            matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
            "expected Unsat with short timeout, got {result:?}"
        );
        // Verify timeout is preserved.
        assert_eq!(
            encoder.solver().timeout(),
            Some(std::time::Duration::from_secs(5)),
            "timeout should be preserved after tiered_check_sat"
        );
    }

    #[test]
    fn test_tiered_check_sat_unsat_with_long_timeout() {
        // With a long timeout (>= TIERED_PROBE_MIN_FULL_TIMEOUT), the tiered
        // probe fires first. For a trivially UNSAT problem, it resolves in
        // the probe phase without needing the full timeout.
        let mut encoder = AYEncoder::new();
        let long_timeout = std::time::Duration::from_mins(1);
        encoder.set_timeout(Some(long_timeout));
        let f = encoder.solver_mut().bool_const(false);
        encoder.assert_term(f);

        let result = tiered_check_sat(&mut encoder);
        assert!(
            matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
            "expected Unsat with long timeout, got {result:?}"
        );
        // Verify the original timeout is restored.
        assert_eq!(
            encoder.solver().timeout(),
            Some(long_timeout),
            "original timeout should be restored after tiered probe"
        );
    }

    #[test]
    fn test_tiered_check_sat_sat_with_long_timeout() {
        // With a long timeout, the tiered probe should resolve SAT quickly.
        let mut encoder = AYEncoder::new();
        let long_timeout = std::time::Duration::from_mins(1);
        encoder.set_timeout(Some(long_timeout));
        let x = encoder
            .get_or_declare_var("x", ay_dpll::api::Sort::Int)
            .unwrap();
        let zero = encoder.solver_mut().int_const(0);
        let gt = encoder.solver_mut().gt(x, zero);
        encoder.assert_term(gt);

        let result = tiered_check_sat(&mut encoder);
        assert!(
            matches!(result, ay_dpll::api::SolveResult::Sat),
            "expected Sat with long timeout, got {result:?}"
        );
        // Verify the original timeout is restored.
        assert_eq!(
            encoder.solver().timeout(),
            Some(long_timeout),
            "original timeout should be restored after tiered probe"
        );
    }

    #[test]
    fn test_tiered_check_sat_preserves_timeout_on_boundary() {
        // Test with timeout exactly at TIERED_PROBE_MIN_FULL_TIMEOUT (15s).
        // This should trigger tiered solving since >= 15s.
        let mut encoder = AYEncoder::new();
        let boundary_timeout = TIERED_PROBE_MIN_FULL_TIMEOUT;
        encoder.set_timeout(Some(boundary_timeout));
        let f = encoder.solver_mut().bool_const(false);
        encoder.assert_term(f);

        let result = tiered_check_sat(&mut encoder);
        assert!(
            matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
            "expected Unsat at boundary timeout, got {result:?}"
        );
        assert_eq!(
            encoder.solver().timeout(),
            Some(boundary_timeout),
            "boundary timeout should be preserved"
        );
    }

    #[test]
    fn test_tiered_check_sat_skips_tier_below_boundary() {
        // Test with timeout just below TIERED_PROBE_MIN_FULL_TIMEOUT (14s).
        // This should skip tiered solving since < 15s.
        let mut encoder = AYEncoder::new();
        let below_boundary = std::time::Duration::from_secs(14);
        encoder.set_timeout(Some(below_boundary));
        let t = encoder.solver_mut().bool_const(true);
        encoder.assert_term(t);

        let result = tiered_check_sat(&mut encoder);
        assert!(
            matches!(result, ay_dpll::api::SolveResult::Sat),
            "expected Sat below boundary timeout, got {result:?}"
        );
        assert_eq!(
            encoder.solver().timeout(),
            Some(below_boundary),
            "timeout should be preserved when tiering is skipped"
        );
    }

    // ── tiered probe-decline routing (#129 leg B) ──────────────────────

    #[test]
    fn test_tiered_probe_decline_reaches_full_solve_and_stays_unknown() {
        // Routing pin (#129 leg B): a probe DECLINE must reach the full solve.
        //
        // `forall x. f(x+1) > f(x)` puts arithmetic inside every candidate
        // trigger, so E-matching cannot instantiate it and CEGQI does not
        // converge: ay's probe declines it as Unknown(QuantifierUnhandled)
        // in well under the probe budget (measured ~0.3ms at ay 3d1bd442d).
        // The removed 71dfb30 short-circuit treated that probe verdict as
        // authoritative and skipped the full solve by construction; this pin
        // asserts the routing instead — the result must come from the
        // FullSolve phase, never from the probe.
        //
        // Fail-closed pin, same test: a decline the full solve ALSO cannot
        // close stays Unknown — routing never manufactures an accept.
        let mut encoder = AYEncoder::new_with_quantifiers();
        encoder.set_timeout(Some(TIERED_PROBE_MIN_FULL_TIMEOUT));

        let expr = forall(
            "x",
            gt(
                logic_fn_call("f", vec![add(var("x"), int(1))]),
                logic_fn_call("f", vec![var("x")]),
            ),
        );
        let term = encoder
            .encode_pure(&expr)
            .expect("triggerless forall should encode");
        encoder.assert_term(term);

        let (result, phase) = tiered_check_sat_with_phase(&mut encoder);

        assert_eq!(
            phase,
            TieredSolvePhase::FullSolve,
            "a probe decline must be routed to the full solve, not \
             short-circuited on the probe verdict (#129 leg B); got {result:?}"
        );
        assert!(
            matches!(result, ay_dpll::api::SolveResult::Unknown),
            "a decline the full solve cannot close must stay Unknown \
             (fail-closed), got {result:?}"
        );
        assert!(
            encoder
                .last_unknown_reason()
                .is_some_and(crate::shared_types::UnknownReason::is_quantifier),
            "the decline reason should remain quantifier-classed, got {:?}",
            encoder.last_unknown_reason()
        );
        assert_eq!(
            encoder.solver().timeout(),
            Some(TIERED_PROBE_MIN_FULL_TIMEOUT),
            "original timeout should be restored after the routed full solve"
        );
    }

    // ── tiered solve constants ─────────────────────────────────────────

    #[test]
    fn test_tiered_probe_timeout_is_reasonable() {
        // The probe timeout should be shorter than the minimum full timeout
        // threshold, otherwise tiered solving wastes budget.
        assert!(
            TIERED_PROBE_TIMEOUT < TIERED_PROBE_MIN_FULL_TIMEOUT,
            "probe timeout ({:?}) must be < min full timeout ({:?})",
            TIERED_PROBE_TIMEOUT,
            TIERED_PROBE_MIN_FULL_TIMEOUT,
        );
    }

    #[test]
    fn test_tiered_probe_timeout_values() {
        assert_eq!(
            TIERED_PROBE_TIMEOUT,
            std::time::Duration::from_secs(10),
            "probe timeout should be 10s"
        );
        assert_eq!(
            TIERED_PROBE_MIN_FULL_TIMEOUT,
            std::time::Duration::from_secs(15),
            "min full timeout should be 15s"
        );
    }

    // ── tiered base recheck ───────────────────────────────────────────

    #[test]
    fn test_tiered_base_recheck_unsat_trivial() {
        // Contradictory base: x > 0 AND x < 0 → UNSAT.
        let mut encoder = AYEncoder::new();
        encoder.set_timeout(Some(std::time::Duration::from_mins(1)));
        let x = encoder
            .get_or_declare_var("x", ay_dpll::api::Sort::Int)
            .unwrap();
        let zero = encoder.solver_mut().int_const(0);
        let gt_zero = encoder.solver_mut().gt(x, zero);
        encoder.assert_term(gt_zero);
        let lt_zero = encoder.solver_mut().lt(x, zero);
        encoder.assert_term(lt_zero);

        let result = tiered_base_recheck(&mut encoder);
        assert!(
            matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
            "contradictory base should be Unsat, got {result:?}"
        );
        // Timeout should be preserved.
        assert_eq!(
            encoder.solver().timeout(),
            Some(std::time::Duration::from_mins(1)),
            "timeout should be preserved after tiered base recheck"
        );
    }

    #[test]
    fn test_tiered_base_recheck_sat_trivial() {
        // Consistent base: x > 0 → SAT.
        let mut encoder = AYEncoder::new();
        encoder.set_timeout(Some(std::time::Duration::from_mins(1)));
        let x = encoder
            .get_or_declare_var("x", ay_dpll::api::Sort::Int)
            .unwrap();
        let zero = encoder.solver_mut().int_const(0);
        let gt_zero = encoder.solver_mut().gt(x, zero);
        encoder.assert_term(gt_zero);

        let result = tiered_base_recheck(&mut encoder);
        assert!(
            matches!(result, ay_dpll::api::SolveResult::Sat),
            "consistent base should be Sat, got {result:?}"
        );
        assert_eq!(
            encoder.solver().timeout(),
            Some(std::time::Duration::from_mins(1)),
            "timeout should be preserved after tiered base recheck"
        );
    }

    #[test]
    fn test_tiered_base_recheck_skips_tier_for_short_timeout() {
        // With a short timeout (< BASE_RECHECK_PROBE_MIN_TIMEOUT), tiered
        // base recheck should fall back to check_sat_with_retry.
        let mut encoder = AYEncoder::new();
        encoder.set_timeout(Some(std::time::Duration::from_secs(5)));
        let x = encoder
            .get_or_declare_var("x", ay_dpll::api::Sort::Int)
            .unwrap();
        let zero = encoder.solver_mut().int_const(0);
        let gt_zero = encoder.solver_mut().gt(x, zero);
        encoder.assert_term(gt_zero);

        let result = tiered_base_recheck(&mut encoder);
        assert!(
            matches!(result, ay_dpll::api::SolveResult::Sat),
            "expected Sat with short timeout, got {result:?}"
        );
        assert_eq!(
            encoder.solver().timeout(),
            Some(std::time::Duration::from_secs(5)),
            "short timeout should be preserved"
        );
    }

    #[test]
    fn test_base_recheck_probe_timeout_is_reasonable() {
        assert!(
            BASE_RECHECK_PROBE_TIMEOUT < BASE_RECHECK_PROBE_MIN_TIMEOUT,
            "base recheck probe timeout ({:?}) must be < min timeout ({:?})",
            BASE_RECHECK_PROBE_TIMEOUT,
            BASE_RECHECK_PROBE_MIN_TIMEOUT,
        );
    }

    #[test]
    fn test_base_recheck_constants() {
        assert_eq!(
            BASE_RECHECK_PROBE_TIMEOUT,
            std::time::Duration::from_secs(5),
            "base recheck probe timeout should be 5s"
        );
        assert_eq!(
            BASE_RECHECK_PROBE_MIN_TIMEOUT,
            std::time::Duration::from_secs(10),
            "base recheck min timeout should be 10s"
        );
        assert_eq!(
            BASE_RECHECK_FULL_CAP,
            std::time::Duration::from_secs(15),
            "base recheck full solve cap should be 15s"
        );
        assert!(
            BASE_RECHECK_FULL_CAP > BASE_RECHECK_PROBE_TIMEOUT,
            "full cap ({:?}) must be > probe timeout ({:?})",
            BASE_RECHECK_FULL_CAP,
            BASE_RECHECK_PROBE_TIMEOUT,
        );
    }

    // ── axiom_free_solve_with_sat_extended (#2692) ─────────────────────

    #[test]
    fn test_extended_axiom_free_probe_unsat_trivial() {
        // Assert false — extended probe should find UNSAT.
        let mut encoder = AYEncoder::new();
        let f = encoder.solver_mut().bool_const(false);
        encoder.assert_term(f);

        let result = axiom_free_solve_with_sat_extended(&mut encoder);
        assert!(
            matches!(result, AxiomFreeOutcome::Unsat),
            "trivially UNSAT should be found by extended probe, got {result:?}"
        );
    }

    #[test]
    fn test_extended_axiom_free_probe_sat_trivial() {
        // Assert x > 0 — extended probe should find SAT with counterexample.
        let mut encoder = AYEncoder::new();
        let x = encoder
            .get_or_declare_var("x", ay_dpll::api::Sort::Int)
            .unwrap();
        let zero = encoder.solver_mut().int_const(0);
        let gt = encoder.solver_mut().gt(x, zero);
        encoder.assert_term(gt);

        let result = axiom_free_solve_with_sat_extended(&mut encoder);
        assert!(
            matches!(result, AxiomFreeOutcome::Sat(_)),
            "SAT problem should produce counterexample, got {result:?}"
        );
    }

    #[test]
    fn test_extended_axiom_free_probe_preserves_timeout() {
        let mut encoder = AYEncoder::new();
        let original = std::time::Duration::from_mins(1);
        encoder.set_timeout(Some(original));
        let f = encoder.solver_mut().bool_const(false);
        encoder.assert_term(f);

        let _result = axiom_free_solve_with_sat_extended(&mut encoder);
        assert_eq!(
            encoder.solver().timeout(),
            Some(original),
            "extended probe should restore original timeout"
        );
    }

    #[test]
    fn test_extended_axiom_free_probe_uses_shorter_when_original_is_small() {
        // When the original timeout is shorter than 5s, the extended probe
        // should use the original timeout (not exceed it).
        let mut encoder = AYEncoder::new();
        let short = std::time::Duration::from_secs(2);
        encoder.set_timeout(Some(short));
        let f = encoder.solver_mut().bool_const(false);
        encoder.assert_term(f);

        let result = axiom_free_solve_with_sat_extended(&mut encoder);
        assert!(
            matches!(result, AxiomFreeOutcome::Unsat),
            "should still find UNSAT with short timeout, got {result:?}"
        );
        assert_eq!(
            encoder.solver().timeout(),
            Some(short),
            "short original timeout should be preserved"
        );
    }

    // ── collapse_disposable_recheck_attempt (#basereq) ───────────────

    #[test]
    fn disposable_recheck_attempt_passes_through_verified_witness() {
        let result = collapse_disposable_recheck_attempt(ResolveContinuation::Continue(
            VerificationResult::Verified(None),
        ));
        assert!(
            matches!(
                result,
                ResolveContinuation::Continue(VerificationResult::Verified(_))
            ),
            "a positive non-vacuity witness from the bounded attempt must rescue the recheck"
        );
    }

    #[test]
    fn disposable_recheck_attempt_passes_through_vacuous_finding() {
        let result = collapse_disposable_recheck_attempt(ResolveContinuation::Continue(
            VerificationResult::Unknown(UnknownReason::SolverMessage(
                VACUOUS_PROOF_MESSAGE.to_string(),
            )),
        ));
        assert!(
            matches!(
                result,
                ResolveContinuation::Continue(VerificationResult::Unknown(
                    UnknownReason::SolverMessage(ref message)
                )) if message == VACUOUS_PROOF_MESSAGE
            ),
            "an explicit vacuity finding must stand (fail-closed), got {result:?}"
        );
    }

    #[test]
    fn disposable_recheck_attempt_maps_soft_unknown_to_pathology_demotion() {
        let result = collapse_disposable_recheck_attempt(ResolveContinuation::Continue(
            VerificationResult::Unknown(UnknownReason::Incomplete),
        ));
        assert!(
            matches!(
                result,
                ResolveContinuation::Continue(VerificationResult::Unknown(
                    UnknownReason::SolverMessage(ref message)
                )) if message == BASE_RECHECK_PATHOLOGY_MESSAGE
            ),
            "a non-decisive attempt must keep the pathological-base demotion, got {result:?}"
        );
    }

    #[test]
    fn disposable_recheck_attempt_preserves_abort_shape_on_hard_timeout() {
        let result = collapse_disposable_recheck_attempt(ResolveContinuation::Abort(
            VerificationResult::Unknown(UnknownReason::Timeout),
        ));
        assert!(
            matches!(
                result,
                ResolveContinuation::Abort(VerificationResult::Unknown(
                    UnknownReason::SolverMessage(ref message)
                )) if message == BASE_RECHECK_PATHOLOGY_MESSAGE
            ),
            "an aborted attempt must keep the Abort shape (placeholder encoder) \
             and the pathology demotion, got {result:?}"
        );
    }
}
