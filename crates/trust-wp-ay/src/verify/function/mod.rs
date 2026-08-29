// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Function contract verification.
//!
//! Contains [`verify_function_with_modes`] for verifying postconditions of
//! pure (non-mutable-borrow) functions.
//!
//! Submodules:
//! - [`axiom_detection`]: Axiom-only function classification, existential witness
//!   extraction, and trust-wp-level Skolemization.
//! - [`alias_constraints`]: By-value alias constraints and invariant receiver extraction.
//!
//! Shared utilities (`flatten_ghost_implications`, `infer_result_sort`,
//! `assert_current_chain_alias_constraints`) moved to `verify/shared_constraints.rs`
//! per #1939.

mod alias_constraints;
pub(crate) mod axiom_detection;
mod bitwise_bv_proof;
mod bitwise_bv_proof_general;
pub(in crate::verify) mod obligation;
pub(in crate::verify) mod result_binding;

// Re-exports for parent module (verify/mod.rs) and tests.
use std::{
    collections::{HashMap, HashSet},
    panic::AssertUnwindSafe,
    sync::Arc,
};

pub(super) use alias_constraints::{
    assert_by_value_alias_constraints, extract_invariant_receiver_var,
};
#[cfg(test)]
pub(super) use axiom_detection::expr_contains_embedded_existential;
#[cfg(test)]
pub(super) use axiom_detection::expr_contains_embedded_universal;
#[cfg(test)]
pub(super) use axiom_detection::has_open_logic_fns;
#[cfg(test)]
pub(super) use axiom_detection::instantiate_embedded_existentials_with_body_witness;
pub(super) use axiom_detection::is_axiom_only_function;
#[cfg(test)]
pub(super) use axiom_detection::is_universal_quantifier;
#[cfg(test)]
pub(super) use axiom_detection::skolemize_negated_universal;
use ay_dpll::api::Term;
use tracing::debug;
use trust_wp_core::{
    formula::{
        internal::tuple_lowering::{
            tuple_field_logic_fn_name, tuple_logic_fn_arity, tuple_logic_fn_name,
        },
        BinOp, ExprSort, Pattern, PureExpr, UnOp,
    },
    logic::{type_invariant_method_name, LogicFnDef, LogicMode, TypeInvariantDef},
};

use self::obligation::verify_single_obligation_slice;
use super::{
    catch_ay_sort_panics_outcome, is_trivially_true_postcondition, logic_fn_equality_matches_body,
    pipeline::{requirement_entails_postcondition, run_verification_pipeline, PipelineOptions},
    postcondition_false_via_logic_bodies, postcondition_true_via_logic_bodies, process_isolation,
    recursive_logic_fn_equality_matches_evaluation,
    recursive_postcondition_matches_evaluation_under_requires,
    requirements_imply_postcondition_via_logic_bodies,
    result_equals_return_expr_via_logic_body_with_requires,
    result_postcondition_contradicts_return_expr,
    result_postcondition_contradicts_return_expr_via_logic_bodies,
    result_postcondition_matches_return_expr,
    result_postcondition_matches_return_expr_via_logic_bodies,
    setup::{setup_verification_encoder, VerificationSetup},
    types::VerificationBase,
    Counterexample, UnknownReason, VerificationOutcome, VerificationRequest, VerificationResult,
};
use crate::{
    encoder::{unsoundness, AYEncoder, AssertionPhase, LogicGroundInstantiationMode},
    error::EncodingError,
};

#[derive(Clone, Copy)]
enum FreshFunctionBaseMode {
    Full,
    AxiomLight,
    /// Preconditions-only base recheck for non-vacuity confirmation (#popcount).
    ///
    /// Asserts ONLY the preconditions (plus structural type/alias constraints),
    /// dropping the fresh-result body binding. Used as a sound non-vacuity probe
    /// when the same-encoder base recheck is a solver-limited `Unknown` whose
    /// ambiguity comes from opaque conversion functions (e.g. `bv2nat`) in the
    /// result definition rather than from contradictory preconditions.
    ///
    /// Soundness: this asserts a strict SUBSET of the `Full` base assertions
    /// (it drops only the fresh-result definition `result = body`). The
    /// fresh-result variable is unconstrained elsewhere, so for any model of the
    /// preconditions the dropped equality is satisfiable by choosing `result`
    /// equal to the (integer) value the body denotes. Hence:
    ///   PreconditionsOnly SAT  ⟺  preconditions SAT  ⟺  base non-vacuous.
    /// A genuinely vacuous proof (contradictory preconditions) makes
    /// PreconditionsOnly UNSAT, which is reported non-`Verified` and still
    /// demotes the obligation.
    PreconditionsOnly,
}

fn fresh_function_base_recheck(
    base: &VerificationBase<'_>,
    context_exprs: &[&PureExpr],
    mode: FreshFunctionBaseMode,
) -> Result<VerificationResult, EncodingError> {
    let preconditions_only = matches!(mode, FreshFunctionBaseMode::PreconditionsOnly);
    let empty_ensures: &[PureExpr] = &[];
    let empty_context_exprs: &[&PureExpr] = &[];
    let setup_ensures = if preconditions_only {
        empty_ensures
    } else {
        base.ensures
    };
    let setup_context_exprs = if preconditions_only {
        empty_context_exprs
    } else {
        context_exprs
    };

    // This recheck bootstraps a SECOND encoder over the same clause set after
    // the primary solve's demotion baseline was taken. Its bootstrap re-fires
    // the same declaration-scan sort fallbacks the primary baseline already
    // forgave as bootstrap false positives (#994, #2623) — without absorption
    // they double-count as genuine deltas and demote obligations that the
    // primary encoding proved without any new approximation (recursive_variant
    // logic-fn identity axioms, for example). Absorb exactly this setup's
    // bootstrap-phase increments; post-bootstrap increments stay counted.
    let unsoundness_before_setup = unsoundness::snapshot();
    let setup_result = setup_verification_encoder(&VerificationSetup {
        requires: base.requires,
        // A preconditions-only witness must also be preconditions-only during
        // bootstrap. Feeding the discarded postcondition/body into setup keeps
        // their goal-only logic functions and defining quantifiers live even
        // though no assertion references them. With AY 0.4 those irrelevant
        // quantifiers can make a trivially satisfiable base hard-time out,
        // preventing the fail-closed vacuity guard from recovering a positive
        // SAT witness. Filter declarations from exactly the retained base.
        ensures: setup_ensures,
        context_exprs: setup_context_exprs,
        result_expr: if preconditions_only {
            None
        } else {
            base.return_expr
        },
        ghost_context: base.ghost_context,
        logic_fns: base.logic_fns,
        mode_overrides: base.mode_overrides,
        type_invariants: base.type_invariants,
        track: base.track.unwrap_or_default(),
        timeout: base.timeout,
        type_constants: base.type_constants,
        closure_captures: base.closure_captures,
        adt_decls: base.adt_decls.as_ref(),
        adt_field_ranges: base.adt_field_ranges.as_ref(),
    })?;
    unsoundness::absorb_secondary_bootstrap_false_positives(
        &unsoundness_before_setup,
        &setup_result.post_bootstrap_snapshot,
    );
    let mut encoder = setup_result.encoder;
    encoder.set_total_int_arithmetic(base.total_int_arithmetic);
    encoder.set_logic_ground_mode(base.logic_ground_mode);
    if let Some(ranges) = base.adt_field_ranges.clone() {
        encoder.set_adt_field_ranges(ranges);
    }

    if let Some(ghost_exprs) = base.ghost_context {
        for ghost_expr in ghost_exprs {
            let term = encoder.encode_pure(ghost_expr)?;
            encoder.assert_term(term);
        }
        super::shared_constraints::flatten_ghost_implications(&mut encoder, ghost_exprs)?;
        super::shared_constraints::instantiate_precondition_foralls_for_ghost(
            &mut encoder,
            base.requires,
            base.ensures,
            ghost_exprs,
        )?;
        super::shared_constraints::assert_ghost_alias_method_congruence(
            &mut encoder,
            base.requires,
            base.ensures,
            ghost_exprs,
        )?;
    }
    super::assert_container_element_invariants(&mut encoder, base.requires, base.type_invariants)?;
    // PreconditionsOnly drops the fresh-result body binding: it is purely a
    // non-vacuity probe over the preconditions. The result definition only
    // constrains a fresh variable and never adds inconsistency to a consistent
    // precondition set, so omitting it preserves the SAT/UNSAT verdict of the
    // preconditions while removing the opaque conversion terms that make the
    // Full recheck solver-limited. (#popcount)
    if !matches!(mode, FreshFunctionBaseMode::PreconditionsOnly)
        && !result_binding::should_use_slice_local_match_result_binding(
            base.return_expr,
            base.ensures,
        )
    {
        result_binding::assert_result_body_binding(
            &mut encoder,
            base.return_expr,
            base.ensures,
            base.requires,
        )?;
    }
    assert_by_value_alias_constraints(&mut encoder)?;

    if let Some(captures) = base.closure_captures {
        super::assert_closure_capture_projections(&mut encoder, captures, "")?;
        super::assert_captured_param_type_invariants(
            &mut encoder,
            captures,
            base.type_invariants,
            base.requires,
        )?;
    }

    let body_assumptions = base
        .return_expr
        .map(super::solver_tail::collect_body_let_assume_assumptions)
        .unwrap_or_default();
    if matches!(mode, FreshFunctionBaseMode::Full) {
        super::solver_tail::assert_standard_axioms(&mut encoder, base.requires, &body_assumptions)?;
        encoder.maybe_assert_logic_ground_instances()?;
    }
    Ok(super::solver_tail::resolve_base_sat_result_with_tight_timeout(&mut encoder))
}

/// Verify a function contract with optional per-function mode overrides.
///
/// Accepts a [`VerificationRequest`] bundle to change the
/// effective visibility mode of logic functions without deep-cloning
/// `LogicFnDef` structs. Used by the driver for module-level scoping. (#564)
///
/// `type_constants` provides concrete values for type-level constants like
/// `Self::MIN` and `Self::MAX`. When verifying specs for integer methods
/// (e.g., `i32::checked_add`), the driver passes constants from
/// [`type_constants_for_int`](crate::type_constants_for_int) so the encoder
/// resolves `Self::MIN@`/`Self::MAX@` to concrete integer values. (#688)
#[tracing::instrument(
    name = "trust_wp::verify_function_with_modes",
    level = "debug",
    skip_all,
    fields(
        requires = request.base.requires.len(),
        ensures = request.base.ensures.len(),
        track = ?request.base.track
    )
)]
pub fn verify_function_with_modes(
    request: VerificationRequest<'_>,
) -> Result<VerificationResult, EncodingError> {
    Ok(legacy_result_from_outcome(
        verify_function_with_modes_outcome(request)?,
    ))
}

fn legacy_result_from_outcome(outcome: VerificationOutcome) -> VerificationResult {
    if !matches!(outcome.result, VerificationResult::Verified(_)) {
        return outcome.result;
    }
    if verified_outcome_has_accepted_evidence(&outcome) {
        return outcome.result;
    }
    VerificationResult::Unknown(legacy_verified_evidence_gap_reason(&outcome, "function"))
}

fn verified_outcome_has_accepted_evidence(outcome: &VerificationOutcome) -> bool {
    outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .is_some_and(|evidence| evidence.accepted_for_consumer)
}

fn legacy_verified_evidence_gap_reason(
    outcome: &VerificationOutcome,
    scope: &str,
) -> UnknownReason {
    let detail = outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .map_or_else(
            || "missing solver evidence".to_string(),
            |evidence| {
                evidence
                    .consumer_rejection
                    .clone()
                    .unwrap_or_else(|| "solver evidence was not accepted for consumers".to_string())
            },
        );
    UnknownReason::SolverMessage(format!(
        "verified {scope} result lacks accepted solver evidence: {detail}"
    ))
}

/// Verify a function contract and return the result with solver provenance.
#[tracing::instrument(
    name = "trust_wp::verify_function_with_modes_outcome",
    level = "debug",
    skip_all,
    fields(
        requires = request.base.requires.len(),
        ensures = request.base.ensures.len(),
        track = ?request.base.track
    )
)]
pub fn verify_function_with_modes_outcome(
    request: VerificationRequest<'_>,
) -> Result<VerificationOutcome, EncodingError> {
    // Silently drop mode_overrides when lengths don't match (#2316, #2700).
    // mode_overrides is computed from the full logic_fn_defs set, but
    // logic_fns may be a filtered subset. Rather than aborting verification,
    // drop the overrides so filter_logic_functions_for_goal falls back to
    // default mode scoping.
    let mut request = request;
    if let (Some(logic_fns), Some(mode_overrides)) =
        (request.base.logic_fns, request.base.mode_overrides)
    {
        if mode_overrides.len() != logic_fns.len() {
            tracing::debug!(
                modes_len = mode_overrides.len(),
                fns_len = logic_fns.len(),
                "mode_overrides length mismatch in verify_function — dropping overrides (#2316)"
            );
            request.base.mode_overrides = None;
        }
    }

    process_isolation::run_outcome_in_child(request.base.timeout, || {
        // Wrap the entire verification pipeline in catch_unwind to isolate ay
        // sort mismatch panics (#997). Uses shared helper (#1111).
        //
        // Demotion (Verified → Unknown for encoding approximations) is now
        // applied INSIDE verify_function_with_modes_inner using a post-bootstrap
        // snapshot as the baseline. This absorbs false-positive
        // SortFallbackToIntFromLogicFn increments from sort hint collection
        // (bootstrap calls infer_expr_sort on LogicFnCall subexpressions before
        // declarations exist). (#994, #2106)
        catch_ay_sort_panics_outcome(AssertUnwindSafe(|| {
            verify_function_with_modes_inner(request)
        }))
    })
    .map(VerificationOutcome::apply_mandatory_proof_authority)
}

fn verify_function_with_modes_inner(
    request: VerificationRequest<'_>,
) -> Result<VerificationOutcome, EncodingError> {
    let base = request.base;
    let requires = base.requires;
    let ensures = base.ensures;
    let ghost_context = base.ghost_context;
    let return_expr = base.return_expr;
    let logic_fns = base.logic_fns;
    let type_invariants = base.type_invariants;
    let track = base.track.unwrap_or_default();
    let closure_captures = base.closure_captures;
    let encode_vc_span = tracing::trace_span!(
        "encode_vc",
        requires = requires.len(),
        ensures = ensures.len(),
        track = ?track
    );
    let encode_vc_guard = encode_vc_span.enter();

    // Debug output for tracing subscribers.

    debug!("=== verify_function ===");
    debug!("  track: {track:?}");
    debug!("  requires: {requires:?}");
    debug!("  ensures: {ensures:?}");
    debug!("  return_expr: {return_expr:?}");
    if let Some(fns) = logic_fns {
        for f in fns {
            debug!(
                "  logic_fn {}: params={:?}, body={:?}",
                f.name(),
                f.params(),
                f.body()
            );
        }
    }
    debug!(
        "  ghost_context ({}):",
        ghost_context.map_or(0, <[PureExpr]>::len)
    );
    match closure_captures {
        Some(caps) if !caps.is_empty() => {
            debug!("  closure_captures: {} info(s)", caps.len());
            for cap in caps {
                debug!(
                    "    def_id={}, param_name={:?}, captures={:?}",
                    cap.def_id(),
                    cap.param_name(),
                    cap.captures()
                        .iter()
                        .map(trust_wp_core::closure::CaptureField::name)
                        .collect::<Vec<_>>()
                );
            }
        }
        _ => debug!("  closure_captures: none"),
    }

    let precheck_demotion_baseline = base
        .unsoundness_snapshot
        .clone()
        .unwrap_or_else(unsoundness::snapshot);
    if requirements_are_obviously_contradictory(requires) {
        return Ok(VerificationOutcome::without_provenance(
            VerificationResult::Unknown(UnknownReason::SolverMessage(
                super::solver_tail::VACUOUS_PROOF_MESSAGE.to_string(),
            )),
        ));
    }
    if let Some(result) =
        precheck_recursive_postconditions(requires, ensures, logic_fns, base.mode_overrides)
    {
        if let Some(result) = demote_non_verified_precheck(&precheck_demotion_baseline, result) {
            return Ok(VerificationOutcome::without_provenance(result));
        }
    }
    if let Some(result) = precheck_recursive_zero_bound_structural_induction(
        requires,
        ensures,
        return_expr,
        logic_fns,
        base.mode_overrides,
    ) {
        if let Some(result) = demote_non_verified_precheck(&precheck_demotion_baseline, result) {
            return Ok(VerificationOutcome::without_provenance(result));
        }
    }
    if let Some(result) = precheck_recursive_adt_lemma_structural_induction(
        ensures,
        return_expr,
        logic_fns,
        base.mode_overrides,
    ) {
        // The ADT-structural-induction precheck is a hard shortcut: when the
        // recognised shape applies, the obligation is discharged directly by
        // the structural-induction argument (see precheck docs) and we skip
        // the SMT solver entirely. Unlike the integer-recursion preckecks
        // that merely emit ground instances for the solver, here the
        // soundness argument lives entirely in the precheck. To keep the
        // This lane has no AY-checkable certificate yet, so its provisional
        // structural provenance remains outside mandatory proof authority via
        // `super::structural_induction_verified_outcome`.
        let demoted = super::demote_if_unsound(&precheck_demotion_baseline, result.clone());
        if matches!(demoted, VerificationResult::Verified(_)) {
            return Ok(super::structural_induction_verified_outcome());
        }
        return Ok(VerificationOutcome::without_provenance(demoted));
    }
    if let Some(result) = precheck_ground_disabled_recursive_body(
        base.logic_ground_mode,
        ensures,
        return_expr,
        logic_fns,
    ) {
        return Ok(VerificationOutcome::without_provenance(
            super::demote_if_unsound(&precheck_demotion_baseline, result),
        ));
    }
    if let Some(result) =
        precheck_recursive_seq_relation_postconditions(ensures, return_expr, logic_fns)
    {
        return Ok(VerificationOutcome::without_provenance(
            super::demote_if_unsound(&precheck_demotion_baseline, result),
        ));
    }
    if let Some(result) = precheck_type_invariant_postconditions(
        requires,
        ensures,
        return_expr,
        base.type_invariants,
        logic_fns,
    ) {
        if let Some(result) = demote_non_verified_precheck(&precheck_demotion_baseline, result) {
            return Ok(VerificationOutcome::without_provenance(result));
        }
    }
    if let Some(result) =
        precheck_result_match_ite_constructor_postconditions(requires, ensures, return_expr)
    {
        if let Some(result) = demote_non_verified_precheck(&precheck_demotion_baseline, result) {
            return Ok(VerificationOutcome::without_provenance(result));
        }
    }
    if let Some(result) =
        precheck_result_constructor_match_postconditions(requires, ensures, return_expr)
    {
        if let Some(result) = demote_non_verified_precheck(&precheck_demotion_baseline, result) {
            return Ok(VerificationOutcome::without_provenance(result));
        }
    }
    if let Some(result) = precheck_ghost_context_postconditions(
        requires,
        ensures,
        return_expr,
        ghost_context,
        logic_fns,
    ) {
        if let Some(result) = demote_non_verified_precheck(&precheck_demotion_baseline, result) {
            return Ok(VerificationOutcome::without_provenance(result));
        }
    }
    if let Some(result) =
        precheck_logic_body_postconditions(requires, ensures, return_expr, logic_fns)
    {
        if let Some(result) = demote_non_verified_precheck(&precheck_demotion_baseline, result) {
            return Ok(VerificationOutcome::without_provenance(result));
        }
    }
    let context_exprs: Vec<&PureExpr> = return_expr.into_iter().collect();
    let fresh_base_recheck_base = base.clone();
    // The fresh base recheck depends only on the BASE (requires + result-body
    // binding), which is identical for every obligation slice of this
    // function — memoize the result so a multi-slice function with a
    // pathological base pays for at most ONE fresh rebuild + solve instead of
    // one per rescued slice. Sound: same inputs, same verdict.
    let fresh_base_recheck_cache: std::cell::RefCell<Option<VerificationResult>> =
        std::cell::RefCell::new(None);
    let fresh_base_recheck = || {
        if let Some(cached) = fresh_base_recheck_cache.borrow().clone() {
            return Ok(cached);
        }
        // Full base recheck first: this is the faithful vacuity guard (base =
        // requires ∧ result-body binding). When it is a solver-limited Unknown
        // — typically because the result definition contains an opaque
        // conversion (e.g. `bv2nat` over a SWAR computation) that plain LIA
        // cannot model-validate — fall back to a preconditions-only probe. That
        // probe drops only the fresh-result definition (a strict relaxation),
        // so a SAT/Verified result soundly establishes the base is non-vacuous
        // without ever asserting an unproven goal. (#popcount)
        let full = fresh_function_base_recheck(
            &fresh_base_recheck_base,
            &context_exprs,
            FreshFunctionBaseMode::Full,
        )?;
        // Diagnostic: this is the ONLY visibility into the fresh rescue's
        // verdict when the same-encoder demotion was the rescue-eligible
        // pathology message. In particular it surfaces a Full-rebuild VACUOUS
        // that disagrees with a live base that never solved UNSAT — the
        // signature of a rebuild whose encoding minted approximation facts
        // the primary encoding never asserted (e.g. the Int-coerced
        // tuple-getter unfoldings on take_some_rest). Such a VACUOUS verdict
        // must still STAND (fail-closed): a PreconditionsOnly escalation
        // cannot soundly override it, because a genuine vacuity carried by
        // body-path assumptions (contradictory LetAssume facts over
        // consistent requires) is indistinguishable here from a fabricated
        // one — see tests::proof_assert_path_conditions::
        // proof_assert_contradictory_conditions_vacuous, which is exactly
        // that shape and must keep demoting. The faithful fix is on the
        // rebuild-encoding side (sort-faithful tuple getters), not on the
        // recheck routing. (#2414)
        debug!("fresh base recheck Full result: {full:?} (#2414)");
        // The PreconditionsOnly escalation on a TIMED-OUT Full recheck is
        // restricted to the long-budget (harness) regime: in short-budget
        // unit-test runs the extra fresh solve blows the tests' own
        // wall-clock budgets, and the pre-change behavior there stopped at
        // the Full result. Incomplete/quantifier-limited Full results (the
        // original #popcount escalation triggers) escalate in every regime.
        let escalate_on_timeout =
            super::solver_tail::base_recheck_long_budget_timeout(fresh_base_recheck_base.timeout);
        let result = if matches!(&full, VerificationResult::Unknown(reason)
            if super::solver_tail::fresh_base_recheck_is_solver_limited(reason)
                && (escalate_on_timeout || !reason.is_timeout()))
        {
            let escalated = fresh_function_base_recheck(
                &fresh_base_recheck_base,
                &context_exprs,
                FreshFunctionBaseMode::PreconditionsOnly,
            )?;
            debug!("fresh base recheck PreconditionsOnly escalation result: {escalated:?} (#2414)");
            escalated
        } else {
            full
        };
        // Only memoize DECISIVE verdicts (Verified / Failed / the explicit
        // VACUOUS demotion). Solver-limited Unknowns can be transient (load,
        // envelope expiry) and caching one would poison the rescue for every
        // remaining slice of the obligation.
        if !matches!(&result, VerificationResult::Unknown(_))
            || matches!(
                &result,
                VerificationResult::Unknown(UnknownReason::SolverMessage(_))
            )
        {
            *fresh_base_recheck_cache.borrow_mut() = Some(result.clone());
        }
        Ok(result)
    };
    let literal_false_base_recheck = || {
        fresh_function_base_recheck(
            &fresh_base_recheck_base,
            &context_exprs,
            FreshFunctionBaseMode::AxiomLight,
        )
    };
    let mode_overrides = base.mode_overrides;
    let pipeline_options = PipelineOptions {
        context_exprs: &context_exprs,
        mut_borrow_final_values: None,
        mutation_continued_params: None,
        closure_capture_debug_prefix: "",
        axiom_debug_label: "function",
        fresh_base_recheck: Some(&fresh_base_recheck),
        literal_false_base_recheck: Some(&literal_false_base_recheck),
        structural_verified_shortcuts: false,
        slice_length_stable_vars: None,
        // The plain lane passes `base.ensures`/`base.requires` to the
        // pipeline untransformed, so they are already the
        // PreparedAssertion-side claim source.
        proof_assert_prepared_source: None,
    };
    let (result, provenance) = run_verification_pipeline(
        base,
        &pipeline_options,
        |ctx| {
            if !result_binding::should_use_slice_local_match_result_binding(
                ctx.return_expr,
                ctx.ensures,
            ) {
                let result_free_logic_tautology = ctx.return_expr.is_none()
                    && ctx
                        .ensures
                        .iter()
                        .all(|ensure| postcondition_true_via_logic_bodies(ensure, logic_fns));
                if !result_free_logic_tautology {
                    result_binding::assert_result_body_binding(
                        ctx.encoder,
                        ctx.return_expr,
                        ctx.ensures,
                        ctx.requires,
                    )?;
                }
            }
            // Signed W-window hints for the bitwise BV bridge — sound here
            // because this pipeline asserts every premise in `ctx.requires`
            // (see `register_signed_window_hints` soundness note).
            ctx.encoder.register_signed_window_hints(ctx.requires);
            assert_ground_tuple_destructor_instances(ctx.encoder, ctx.requires)?;
            assert_type_invariant_precheck_facts(
                ctx.encoder,
                ctx.requires,
                ctx.ensures,
                ctx.return_expr,
                type_invariants,
                logic_fns,
            )?;
            assert_recursive_zero_bound_structural_induction_facts(
                ctx.encoder,
                ctx.requires,
                ctx.ensures,
                ctx.return_expr,
                logic_fns,
                mode_overrides,
            )?;
            let asserted_recursive_unfoldings =
                assert_recursive_logic_fn_symbolic_unfoldings_for_goal_and_assumptions(
                    ctx.encoder,
                    ctx.ensures,
                    ctx.requires,
                    logic_fns,
                    mode_overrides,
                )?;
            // Bounded structural-induction lemma for recursive-datatype
            // `get`/`len` logic fns: when a postcondition needs
            // `forall i. 0<=i<len(l) ==> is-Some(get(l,i))`, discharge it via the
            // datatype's induction principle (base + step sub-proofs) and assert
            // the proven, E-matchable conclusion. SOUND — emits only a genuine
            // theorem, inert otherwise. (#all_zero Obl1)
            ctx.encoder.emit_bounded_get_some_structural_induction(
                ctx.ensures,
                logic_fns,
                mode_overrides,
            );
            assert_logic_proof_call_postconditions(
                ctx.encoder,
                ctx.requires,
                ctx.return_expr,
                logic_fns,
                mode_overrides,
            )?;
            if asserted_recursive_unfoldings
                && return_expr_contains_logic_proof_call(ctx.return_expr, logic_fns)
            {
                ctx.encoder
                    .set_logic_ground_mode(LogicGroundInstantiationMode::Disabled);
            }
            assert_by_value_alias_constraints(ctx.encoder)?;
            Ok(())
        },
        move || {
            drop(encode_vc_guard);
            tracing::trace_span!("solve").entered()
        },
        verify_single_obligation_slice,
    )?;
    Ok(VerificationOutcome::new(result, provenance))
}

fn demote_non_verified_precheck(
    baseline: &unsoundness::Snapshot,
    result: VerificationResult,
) -> Option<VerificationResult> {
    if matches!(result, VerificationResult::Verified(_)) {
        return None;
    }
    Some(super::demote_if_unsound(baseline, result))
}

fn assert_ground_tuple_destructor_instances(
    encoder: &mut AYEncoder,
    facts: &[PureExpr],
) -> Result<(), EncodingError> {
    for fact in facts {
        assert_ground_tuple_destructor_instances_in_expr(encoder, fact)?;
    }
    Ok(())
}

fn assert_ground_tuple_destructor_instances_in_expr(
    encoder: &mut AYEncoder,
    expr: &PureExpr,
) -> Result<(), EncodingError> {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            assert_ground_tuple_destructor_instances_in_expr(encoder, left)?;
            assert_ground_tuple_destructor_instances_in_expr(encoder, right)?;
        }
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            assert_tuple_destructors_for_equality(encoder, left, right)?;
            assert_tuple_destructors_for_equality(encoder, right, left)?;
        }
        _ => {}
    }
    Ok(())
}

fn assert_type_invariant_precheck_facts(
    encoder: &mut AYEncoder,
    requires: &[PureExpr],
    ensures: &[PureExpr],
    return_expr: Option<&PureExpr>,
    type_invariants: Option<&[TypeInvariantDef]>,
    logic_fns: Option<&[LogicFnDef]>,
) -> Result<(), EncodingError> {
    if !matches!(
        precheck_type_invariant_postconditions(
            requires,
            ensures,
            return_expr,
            type_invariants,
            logic_fns,
        ),
        Some(VerificationResult::Verified(_))
    ) {
        return Ok(());
    }
    let Some(return_expr) = return_expr else {
        return Ok(());
    };
    let Some(type_invariants) = type_invariants else {
        return Ok(());
    };
    for ensure in ensures {
        let Some(method) = result_type_invariant_method(ensure) else {
            continue;
        };
        let Some(inv) = type_invariants
            .iter()
            .find(|inv| type_invariant_method_name(inv.type_name()) == method)
        else {
            continue;
        };
        let mut substitutions = HashMap::new();
        substitutions.insert(inv.self_param().to_string(), return_expr.clone());
        let body = inv.body().substitute(&substitutions);
        let term = encoder.encode_pure(&body)?;
        let term = encoder.coerce_bool_operand(term);
        encoder.assert_term(term);
        let ensure_term = encoder.encode_pure(ensure)?;
        let ensure_term = encoder.coerce_bool_operand(ensure_term);
        encoder.assert_term(ensure_term);
    }
    Ok(())
}

fn assert_tuple_destructors_for_equality(
    encoder: &mut AYEncoder,
    target: &PureExpr,
    value: &PureExpr,
) -> Result<(), EncodingError> {
    let PureExpr::LogicFnCall { name, args } = value else {
        return Ok(());
    };
    if tuple_logic_fn_arity(name) != Some(args.len()) {
        return Ok(());
    }
    let mut numeric_fields = Vec::new();
    let mut numeric_args = Vec::new();
    for (index, arg) in args.iter().enumerate() {
        let field = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(index),
            args: vec![target.clone()],
        };
        let equality = PureExpr::BinOp(Arc::new(field.clone()), BinOp::Eq, Arc::new(arg.clone()));
        let term = encoder.encode_pure(&equality)?;
        encoder.assert_term(term);
        if matches!(
            encoder.infer_expr_sort_with_context(arg, None),
            ay_dpll::api::Sort::Int
        ) {
            let numeric_field = PureExpr::BinOp(
                Arc::new(field.clone()),
                BinOp::Add,
                Arc::new(PureExpr::Int(0)),
            );
            let numeric_equality =
                PureExpr::BinOp(Arc::new(numeric_field), BinOp::Eq, Arc::new(arg.clone()));
            let term = encoder.encode_pure(&numeric_equality)?;
            encoder.assert_term(term);
            numeric_fields.push(field);
            numeric_args.push(arg.clone());
        }
    }
    if numeric_fields.len() == args.len() && numeric_fields.len() >= 2 {
        let field_sum = fold_add_exprs(numeric_fields);
        let arg_sum = fold_add_exprs(numeric_args);
        let equality = PureExpr::BinOp(Arc::new(field_sum), BinOp::Eq, Arc::new(arg_sum));
        let term = encoder.encode_pure(&equality)?;
        encoder.assert_term(term);
    }
    Ok(())
}

fn fold_add_exprs(mut exprs: Vec<PureExpr>) -> PureExpr {
    let mut iter = exprs.drain(..);
    let first = iter
        .next()
        .expect("fold_add_exprs requires a non-empty vector");
    iter.fold(first, |acc, expr| {
        PureExpr::BinOp(Arc::new(acc), BinOp::Add, Arc::new(expr))
    })
}

fn assert_logic_proof_call_postconditions(
    encoder: &mut AYEncoder,
    caller_requires: &[PureExpr],
    return_expr: Option<&PureExpr>,
    logic_fns: Option<&[LogicFnDef]>,
    mode_overrides: Option<&[LogicMode]>,
) -> Result<(), EncodingError> {
    let (Some(return_expr), Some(logic_fns)) = (return_expr, logic_fns) else {
        return Ok(());
    };
    let mut guards = Vec::new();
    assert_logic_proof_call_postconditions_in_expr(
        encoder,
        return_expr,
        caller_requires,
        logic_fns,
        mode_overrides,
        &mut guards,
    )
}

fn assert_logic_proof_call_postconditions_in_expr(
    encoder: &mut AYEncoder,
    expr: &PureExpr,
    caller_requires: &[PureExpr],
    logic_fns: &[LogicFnDef],
    mode_overrides: Option<&[LogicMode]>,
    guards: &mut Vec<PureExpr>,
) -> Result<(), EncodingError> {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            assert_one_logic_proof_call_postcondition(
                encoder,
                name,
                args,
                expr,
                caller_requires,
                logic_fns,
                mode_overrides,
                guards,
            )?;
            for arg in args {
                assert_logic_proof_call_postconditions_in_expr(
                    encoder,
                    arg,
                    caller_requires,
                    logic_fns,
                    mode_overrides,
                    guards,
                )?;
            }
            Ok(())
        }
        PureExpr::BinOp(left, _, right) => {
            assert_logic_proof_call_postconditions_in_expr(
                encoder,
                left,
                caller_requires,
                logic_fns,
                mode_overrides,
                guards,
            )?;
            assert_logic_proof_call_postconditions_in_expr(
                encoder,
                right,
                caller_requires,
                logic_fns,
                mode_overrides,
                guards,
            )
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => assert_logic_proof_call_postconditions_in_expr(
            encoder,
            inner,
            caller_requires,
            logic_fns,
            mode_overrides,
            guards,
        ),
        PureExpr::MethodCall { receiver, args, .. } => {
            assert_logic_proof_call_postconditions_in_expr(
                encoder,
                receiver,
                caller_requires,
                logic_fns,
                mode_overrides,
                guards,
            )?;
            for arg in args {
                assert_logic_proof_call_postconditions_in_expr(
                    encoder,
                    arg,
                    caller_requires,
                    logic_fns,
                    mode_overrides,
                    guards,
                )?;
            }
            Ok(())
        }
        PureExpr::Let {
            var: _,
            value,
            body,
        } => {
            assert_logic_proof_call_postconditions_in_expr(
                encoder,
                value,
                caller_requires,
                logic_fns,
                mode_overrides,
                guards,
            )?;
            assert_logic_proof_call_postconditions_in_expr(
                encoder,
                body,
                caller_requires,
                logic_fns,
                mode_overrides,
                guards,
            )
        }
        PureExpr::LetAssume { assumption, body }
        | PureExpr::LetObligation {
            obligation: assumption,
            body,
        } => {
            guards.push(assumption.as_ref().clone());
            let result = assert_logic_proof_call_postconditions_in_expr(
                encoder,
                body,
                caller_requires,
                logic_fns,
                mode_overrides,
                guards,
            );
            guards.pop();
            result
        }
        PureExpr::Ite(cond, then_branch, else_branch) => {
            assert_logic_proof_call_postconditions_in_expr(
                encoder,
                cond,
                caller_requires,
                logic_fns,
                mode_overrides,
                guards,
            )?;

            guards.push(cond.as_ref().clone());
            assert_logic_proof_call_postconditions_in_expr(
                encoder,
                then_branch,
                caller_requires,
                logic_fns,
                mode_overrides,
                guards,
            )?;
            guards.pop();

            guards.push(PureExpr::UnOp(UnOp::Not, Arc::clone(cond)));
            let result = assert_logic_proof_call_postconditions_in_expr(
                encoder,
                else_branch,
                caller_requires,
                logic_fns,
                mode_overrides,
                guards,
            );
            guards.pop();
            result
        }
        PureExpr::Match { scrutinee, arms } => {
            assert_logic_proof_call_postconditions_in_expr(
                encoder,
                scrutinee,
                caller_requires,
                logic_fns,
                mode_overrides,
                guards,
            )?;
            for arm in arms {
                let guard_len = guards.len();
                if let Some(pattern_fact) = match_pattern_fact(scrutinee, &arm.pattern) {
                    guards.push(pattern_fact);
                }
                assert_logic_proof_call_postconditions_in_expr(
                    encoder,
                    &arm.body,
                    caller_requires,
                    logic_fns,
                    mode_overrides,
                    guards,
                )?;
                guards.truncate(guard_len);
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

fn match_pattern_fact(scrutinee: &PureExpr, pattern: &Pattern) -> Option<PureExpr> {
    pattern_value_expr(pattern)
        .map(|value| PureExpr::BinOp(Arc::new(scrutinee.clone()), BinOp::Eq, Arc::new(value)))
}

fn pattern_value_expr(pattern: &Pattern) -> Option<PureExpr> {
    match pattern {
        Pattern::Constructor { name, inner } => {
            let mut args = Vec::new();
            if let Some(inner) = inner.as_deref() {
                args.push(pattern_value_expr(inner)?);
            }
            Some(PureExpr::LogicFnCall {
                name: name.clone(),
                args,
            })
        }
        Pattern::Tuple(patterns) => Some(PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(patterns.len()),
            args: patterns
                .iter()
                .map(pattern_value_expr)
                .collect::<Option<Vec<_>>>()?,
        }),
        Pattern::Binding(name) => Some(PureExpr::Var(name.clone(), None)),
        Pattern::Alias { alias, pattern } => {
            pattern_value_expr(pattern).or_else(|| Some(PureExpr::Var(alias.clone(), None)))
        }
        Pattern::Wildcard => None,
        Pattern::Literal(value) => Some(value.clone()),
        _ => None,
    }
}

fn pure_expr_contains_quantifier(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| matches!(node, PureExpr::Forall { .. } | PureExpr::Exists { .. }))
}

fn assert_one_logic_proof_call_postcondition(
    encoder: &mut AYEncoder,
    name: &str,
    args: &[PureExpr],
    value: &PureExpr,
    caller_requires: &[PureExpr],
    logic_fns: &[LogicFnDef],
    mode_overrides: Option<&[LogicMode]>,
    guards: &[PureExpr],
) -> Result<(), EncodingError> {
    let Some(logic_fn) = logic_fns
        .iter()
        .find(|logic_fn| logic_fn.name() == name && logic_fn.params().len() == args.len())
    else {
        return Ok(());
    };
    let param_substitutions: HashMap<String, PureExpr> = logic_fn
        .params()
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    let mut substitutions = param_substitutions.clone();
    substitutions.insert("result".to_string(), value.clone());

    let instantiated_requires: Vec<PureExpr> = logic_fn
        .requires()
        .iter()
        .map(|require| require.substitute(&substitutions))
        .collect();
    let mut path_conditions = Vec::with_capacity(caller_requires.len() + guards.len());
    path_conditions.extend(caller_requires.iter().cloned());
    path_conditions.extend(guards.iter().cloned());
    if !path_conditions_imply_all(encoder, &path_conditions, &instantiated_requires)? {
        return Ok(());
    }

    for ensure in logic_fn.ensures() {
        let param_instantiated_ensure = ensure.substitute(&param_substitutions);
        let instantiated_ensure = ensure.substitute(&substitutions);
        assert_recursive_logic_fn_symbolic_unfoldings_for_exprs(
            encoder,
            std::slice::from_ref(&instantiated_ensure),
            Some(logic_fns),
            mode_overrides,
        )?;
        let replace_raw_match =
            AYEncoder::result_match_branch_instances_should_replace_raw(&param_instantiated_ensure);
        let branch_instances = if replace_raw_match {
            let result_term = encoder.encode_pure(value)?;
            encoder.encode_bound_result_match_branch_instances(
                &param_instantiated_ensure,
                result_term,
            )?
        } else {
            Vec::new()
        };
        let replace_raw_match = replace_raw_match && !branch_instances.is_empty();
        let guard = encode_logic_proof_call_path_condition_guard(encoder, &path_conditions)?;
        if !replace_raw_match && !pure_expr_contains_quantifier(&instantiated_ensure) {
            let ensure_term = encoder.encode_pure(&instantiated_ensure)?;
            let ensure_term = encoder.coerce_bool_operand(ensure_term);
            let asserted = guard_logic_proof_call_fact(encoder, guard, ensure_term);
            encoder.assert_term(asserted);
        }
        for branch_instance in branch_instances {
            let branch_instance = encoder.coerce_bool_operand(branch_instance);
            let asserted = guard_logic_proof_call_fact(encoder, guard, branch_instance);
            encoder.assert_term(asserted);
        }
    }
    Ok(())
}

fn encode_logic_proof_call_path_condition_guard(
    encoder: &mut AYEncoder,
    path_conditions: &[PureExpr],
) -> Result<Option<Term>, EncodingError> {
    let mut antecedents = Vec::with_capacity(path_conditions.len());
    for antecedent in path_conditions {
        let term = encoder.encode_pure(antecedent)?;
        antecedents.push(encoder.coerce_bool_operand(term));
    }
    Ok(match antecedents.as_slice() {
        [] => None,
        [antecedent] => Some(*antecedent),
        _ => Some(encoder.solver_mut().and_many(&antecedents)),
    })
}

fn guard_logic_proof_call_fact(encoder: &mut AYEncoder, guard: Option<Term>, fact: Term) -> Term {
    match guard {
        Some(guard) => encoder.solver_mut().implies(guard, fact),
        None => fact,
    }
}

fn assert_recursive_logic_fn_symbolic_unfoldings_for_exprs(
    encoder: &mut AYEncoder,
    exprs: &[PureExpr],
    logic_fns: Option<&[LogicFnDef]>,
    mode_overrides: Option<&[LogicMode]>,
) -> Result<bool, EncodingError> {
    assert_recursive_logic_fn_symbolic_unfoldings_for_goal_and_assumptions(
        encoder,
        exprs,
        &[],
        logic_fns,
        mode_overrides,
    )
}

/// Like [`assert_recursive_logic_fn_symbolic_unfoldings_for_exprs`], but also
/// collects the bounded 1-step unfold on recursive-fn terms that appear in
/// `assumption_exprs` (the obligation's `requires`, which carry the injected
/// variant-gated recursive-induction hypotheses).
///
/// The hypothesis for a recursive `#[logic]` lemma introduces a recursive-fn
/// application at the *recursive* arguments — e.g. `num_of_pos(i, j+1, t)` for
/// `lemma_num_of_pos_increasing` — that is NOT syntactically present in the
/// goal. Without its one-step unfold the solver cannot relate the IH term to
/// the goal's `num_of_pos(i, j, t)`, so the lemma's own postcondition stays
/// unprovable. Unfolding the assumption terms supplies exactly that bridge.
///
/// SOUND: each emitted fact is a requires- and path-guarded instance of the
/// total logic fn's own defining equation (`emit_guarded_recursive_unfolding_facts`),
/// i.e. a true consequence of its definition. Adding a true fact can only ever
/// help discharge a genuinely-valid goal; it can never manufacture a spurious
/// UNSAT (false-accept). TERMINATING: a single collection pass over the goal
/// AND assumption expressions; the `f(smaller)` terms each unfold introduces are
/// pushed into `facts` and are NOT re-collected, so there is no unfolding
/// cascade (a global step-forall, by contrast, diverges — confirmed earlier).
fn assert_recursive_logic_fn_symbolic_unfoldings_for_goal_and_assumptions(
    encoder: &mut AYEncoder,
    exprs: &[PureExpr],
    assumption_exprs: &[PureExpr],
    logic_fns: Option<&[LogicFnDef]>,
    mode_overrides: Option<&[LogicMode]>,
) -> Result<bool, EncodingError> {
    let Some(logic_fns) = logic_fns else {
        return Ok(false);
    };
    let mut facts = Vec::new();
    let mut seen = HashSet::new();
    // One collection pass over the goal expressions followed by the assumption
    // (requires/IH) expressions, sharing a single `seen` set so a term present
    // in both is unfolded once. The unfolded bodies land in `facts` and are
    // never re-scanned, so this stays a single non-cascading pass.
    for expr in exprs.iter().chain(assumption_exprs.iter()) {
        collect_recursive_logic_fn_symbolic_unfoldings(
            expr,
            logic_fns,
            mode_overrides,
            &mut facts,
            &mut seen,
        );
    }
    if facts.is_empty() {
        return Ok(false);
    }

    encoder.register_sort_hints(&facts);
    encoder.register_formula_sort_hints(&facts);
    for fact in &facts {
        // A recursive logic-fn unfolding fact is the *defining axiom* for that
        // function over the matched constructor arm (e.g.
        // `is-Cons(self) => diff(self) = a@ - diff(tail(self))`). If encoding
        // the arm body forces a sort-coercion bridge on a recursive self-call
        // argument — typically because the recursive ADT field was modelled as
        // `Int` rather than the recursive datatype, so `diff(tail(self))`
        // becomes `diff(__apply_coerce…)` over a *fresh, disconnected* constant
        // — the axiom no longer faithfully relates `diff(self)` to its own
        // recursion. ay-dpll can then return an incomplete/false UNSAT against
        // an otherwise-satisfiable negated goal (the recursion site is severed),
        // closing a mathematically false obligation (e.g. the subtraction-based
        // `diff(self) >= 0`). Treat such a corrupted unfolding as a dropped spec
        // axiom (HIGH risk) so `demote_if_unsound` downgrades any resulting
        // `Verified` to `Unknown`. This is sound and surgical: genuine
        // non-negative-sum inductions are discharged by
        // `precheck_recursive_adt_lemma_structural_induction` before reaching
        // this path, and correctly-typed recursive datatypes need no coercion
        // here, so their unfolding axioms are left untouched. (#soundness)
        let coercion_before = unsoundness::snapshot();
        let term = encoder.encode_pure(fact)?;
        let coercion_after = unsoundness::snapshot();
        if unfolding_recursive_call_was_coerced(&coercion_before, &coercion_after) {
            unsoundness::increment(unsoundness::UnsoundnessCategory::SpecAxiomDropped);
        }
        encoder.assert_term(term);
    }
    Ok(true)
}

/// Whether encoding a recursive-logic-fn unfolding fact triggered a
/// `SortCoercionBridge` increment — i.e. an argument (the recursive self-call's
/// argument, in practice) had to be replaced by a fresh, unconstrained constant
/// of the function's declared domain sort. Such a coercion severs the recursion
/// relation encoded by the unfolding axiom, so the unfolding can no longer be
/// trusted as a faithful definition of the function.
fn unfolding_recursive_call_was_coerced(
    before: &unsoundness::Snapshot,
    after: &unsoundness::Snapshot,
) -> bool {
    let delta = unsoundness::delta(before, after);
    delta
        .get(&unsoundness::UnsoundnessCategory::SortCoercionBridge)
        .is_some_and(|&count| count > 0)
}

fn collect_recursive_logic_fn_symbolic_unfoldings(
    expr: &PureExpr,
    logic_fns: &[LogicFnDef],
    mode_overrides: Option<&[LogicMode]>,
    facts: &mut Vec<PureExpr>,
    seen: &mut HashSet<String>,
) {
    expr.for_each_recursive(|node| {
        let PureExpr::LogicFnCall { name, args } = node else {
            return;
        };
        let Some((index, logic_fn)) = logic_fns
            .iter()
            .enumerate()
            .find(|(_, logic_fn)| logic_fn.name() == name && logic_fn.params().len() == args.len())
        else {
            return;
        };
        if !logic_fn.is_recursive()
            || logic_fn.is_opaque()
            || effective_logic_mode(logic_fn, index, mode_overrides) != LogicMode::Open
        {
            return;
        }

        let substitutions: HashMap<String, PureExpr> = logic_fn
            .params()
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        let mut guards: Vec<PureExpr> = logic_fn
            .requires()
            .iter()
            .map(|require| require.substitute(&substitutions))
            .collect();
        let call = PureExpr::LogicFnCall {
            name: name.clone(),
            args: args.clone(),
        };
        let body = logic_fn.body().substitute(&substitutions);
        emit_guarded_recursive_unfolding_facts(&call, &body, &mut guards, facts, seen);
    });
}

fn emit_guarded_recursive_unfolding_facts(
    call: &PureExpr,
    body: &PureExpr,
    guards: &mut Vec<PureExpr>,
    facts: &mut Vec<PureExpr>,
    seen: &mut HashSet<String>,
) {
    match body {
        PureExpr::Ite(cond, then_branch, else_branch) => {
            guards.push(cond.as_ref().clone());
            emit_guarded_recursive_unfolding_facts(call, then_branch, guards, facts, seen);
            guards.pop();

            guards.push(PureExpr::UnOp(UnOp::Not, Arc::clone(cond)));
            emit_guarded_recursive_unfolding_facts(call, else_branch, guards, facts, seen);
            guards.pop();
        }
        _ => {
            let equality =
                PureExpr::BinOp(Arc::new(call.clone()), BinOp::Eq, Arc::new(body.clone()));
            let fact = imply_all(guards, equality);
            if seen.insert(format!("{fact:?}")) {
                facts.push(fact);
            }
        }
    }
}

fn imply_all(antecedents: &[PureExpr], consequent: PureExpr) -> PureExpr {
    if antecedents.is_empty() {
        return consequent;
    }
    let antecedent = fold_and_exprs(antecedents.to_vec());
    PureExpr::BinOp(Arc::new(antecedent), BinOp::Implies, Arc::new(consequent))
}

fn fold_and_exprs(mut exprs: Vec<PureExpr>) -> PureExpr {
    let mut iter = exprs.drain(..);
    let first = iter
        .next()
        .expect("fold_and_exprs requires a non-empty vector");
    iter.fold(first, |acc, expr| {
        PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(expr))
    })
}

fn path_conditions_imply_all(
    encoder: &mut AYEncoder,
    antecedents: &[PureExpr],
    consequents: &[PureExpr],
) -> Result<bool, EncodingError> {
    if consequents.is_empty() {
        return Ok(true);
    }

    let original_timeout = encoder.solver().timeout();
    let original_ground_mode = encoder.logic_ground_mode();
    let precheck_timeout = std::time::Duration::from_millis(500);
    let effective_timeout = match original_timeout {
        Some(timeout) if timeout <= precheck_timeout => timeout,
        _ => precheck_timeout,
    };
    encoder.set_timeout(Some(effective_timeout));
    encoder.set_logic_ground_mode(LogicGroundInstantiationMode::Disabled);
    encoder.push_scope()?;

    let result = (|| -> Result<bool, EncodingError> {
        for antecedent in antecedents {
            let term = encoder.encode_pure(antecedent)?;
            let term = encoder.coerce_bool_operand(term);
            encoder.assert_term(term);
        }
        let mut consequent_terms = Vec::with_capacity(consequents.len());
        for consequent in consequents {
            let term = encoder.encode_pure(consequent)?;
            consequent_terms.push(encoder.coerce_bool_operand(term));
        }
        let all_consequents = if consequent_terms.len() == 1 {
            consequent_terms
                .into_iter()
                .next()
                .expect("single consequent present")
        } else {
            encoder.solver_mut().and_many(&consequent_terms)
        };
        let violation = encoder.solver_mut().not(all_consequents);
        encoder.assert_term(violation);
        Ok(matches!(
            encoder.check_sat(),
            ay_dpll::api::SolveResult::Unsat(_)
        ))
    })();

    let pop_result = encoder.pop_scope();
    encoder.set_timeout(original_timeout);
    encoder.set_logic_ground_mode(original_ground_mode);
    pop_result?;
    result
}

fn precheck_result_constructor_match_postconditions(
    requires: &[PureExpr],
    ensures: &[PureExpr],
    return_expr: Option<&PureExpr>,
) -> Option<VerificationResult> {
    if ensures.is_empty() {
        return None;
    }
    let mut saw_match = false;
    for ensure in ensures {
        if result_match_postcondition_follows_return_constructor(requires, ensure, return_expr) {
            saw_match = true;
            continue;
        }
        return None;
    }
    saw_match.then_some(VerificationResult::Verified(None))
}

fn result_match_postcondition_follows_return_constructor(
    requires: &[PureExpr],
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
) -> bool {
    result_match_constructor_prechecked_body(requires, ensure, return_expr).is_some()
}

pub(super) fn result_match_constructor_prechecked_body(
    requires: &[PureExpr],
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
) -> Option<PureExpr> {
    let PureExpr::Match { scrutinee, arms } = ensure else {
        return None;
    };
    if !matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == "result") {
        return None;
    }
    let Some((return_ctor, tuple_arity, args)) = return_constructor_precheck_args(return_expr)
    else {
        return None;
    };
    let tuple_fallback_is_unambiguous = tuple_arity.is_some()
        && arms
            .iter()
            .filter(|arm| matches!(arm.pattern, Pattern::Constructor { .. }))
            .count()
            == 1;
    arms.iter().find_map(|arm| {
        let Pattern::Constructor { name, inner } = &arm.pattern else {
            return None;
        };
        let pattern_ctor = crate::encoder::match_enc::short_constructor_name(name);
        let matches_named_ctor = return_ctor.as_deref() == Some(pattern_ctor);
        let matches_tuple_body = tuple_fallback_is_unambiguous
            && tuple_arity == constructor_pattern_arity(inner.as_deref());
        if !matches_named_ctor && !matches_tuple_body {
            return None;
        }
        let mut substitutions = HashMap::new();
        if !collect_constructor_pattern_arg_substitutions(
            inner.as_deref(),
            &args,
            &mut substitutions,
        ) {
            return None;
        }
        let body = arm.body.substitute(&substitutions);
        postcondition_true_under_context(requires, None, &body).then_some(body)
    })
}

fn return_constructor_precheck_args(
    return_expr: Option<&PureExpr>,
) -> Option<(Option<String>, Option<usize>, Vec<PureExpr>)> {
    match return_expr? {
        PureExpr::LogicFnCall { name, args } => {
            let tuple_arity = tuple_logic_fn_arity(name);
            let ctor = tuple_arity
                .is_none()
                .then(|| crate::encoder::match_enc::short_constructor_name(name).to_string());
            Some((ctor, tuple_arity, args.clone()))
        }
        expr @ PureExpr::Var(_, Some(ExprSort::Tuple(arity))) if *arity >= 1 => {
            let arity = usize::from(*arity);
            let args = (0..arity)
                .map(|index| PureExpr::LogicFnCall {
                    name: tuple_field_logic_fn_name(index),
                    args: vec![(*expr).clone()],
                })
                .collect();
            Some((None, Some(arity), args))
        }
        _ => None,
    }
}

fn constructor_pattern_arity(pattern: Option<&Pattern>) -> Option<usize> {
    match pattern {
        None => Some(0),
        Some(Pattern::Binding(_))
        | Some(Pattern::Literal(_))
        | Some(Pattern::Wildcard)
        | Some(Pattern::Constructor { .. }) => Some(1),
        Some(Pattern::Tuple(patterns)) => Some(patterns.len()),
        Some(Pattern::Alias { pattern, .. }) => constructor_pattern_arity(Some(pattern)),
        Some(_) => None,
    }
}

fn precheck_result_match_ite_constructor_postconditions(
    requires: &[PureExpr],
    ensures: &[PureExpr],
    return_expr: Option<&PureExpr>,
) -> Option<VerificationResult> {
    if ensures.is_empty() {
        return None;
    }
    let Some(PureExpr::Ite(cond, then_expr, else_expr)) = return_expr else {
        return None;
    };

    let mut saw_match = false;
    for (clause_idx, ensure) in ensures.iter().enumerate() {
        let Some(then_body) = selected_result_match_arm_body(ensure, then_expr) else {
            return None;
        };
        let Some(else_body) = selected_result_match_arm_body(ensure, else_expr) else {
            return None;
        };
        saw_match = true;

        if !postcondition_true_under_context(requires, Some((cond, true)), &then_body) {
            if postcondition_false_under_context(requires, Some((cond, true)), &then_body) {
                return Some(precheck_failed_for_clause(clause_idx, ensure));
            }
            return None;
        }
        if !postcondition_true_under_context(requires, Some((cond, false)), &else_body) {
            if postcondition_false_under_context(requires, Some((cond, false)), &else_body) {
                return Some(precheck_failed_for_clause(clause_idx, ensure));
            }
            return None;
        }
    }

    saw_match.then_some(VerificationResult::Verified(None))
}

/// Build a `Failed` result for a function-level precheck that has identified
/// the specific ensures clause that contradicts the body. The empty
/// counterexample carries no bindings (the precheck path bypasses the
/// solver), but tagging the clause text lets the driver render a precise
/// "violated ensures #N: <clause>" line instead of the generic
/// "postcondition(s): ..." dump (Phase 8a).
fn precheck_failed_for_clause(clause_idx: usize, ensure: &PureExpr) -> VerificationResult {
    VerificationResult::Failed(Counterexample::empty()).tag_violated_postcondition(
        super::PostconditionInfo {
            clause_idx,
            contract_text: ensure.to_string(),
            span: None,
        },
    )
}

fn selected_result_match_arm_body(ensure: &PureExpr, return_branch: &PureExpr) -> Option<PureExpr> {
    let PureExpr::Match { scrutinee, arms } = ensure else {
        return None;
    };
    if !matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == "result") {
        return None;
    }
    let PureExpr::LogicFnCall { name, args } = return_branch else {
        return None;
    };
    let return_ctor = crate::encoder::match_enc::short_constructor_name(name);
    for arm in arms {
        let Pattern::Constructor { name, inner } = &arm.pattern else {
            continue;
        };
        if crate::encoder::match_enc::short_constructor_name(name) != return_ctor {
            continue;
        }
        let mut substitutions = HashMap::new();
        if collect_constructor_pattern_arg_substitutions(inner.as_deref(), args, &mut substitutions)
        {
            return Some(arm.body.substitute(&substitutions));
        }
    }
    None
}

fn postcondition_true_under_context(
    requires: &[PureExpr],
    branch: Option<(&PureExpr, bool)>,
    expr: &PureExpr,
) -> bool {
    let mut substitutions = HashMap::new();
    if let Some((PureExpr::Var(name, _), value)) = branch {
        substitutions.insert(name.clone(), PureExpr::Bool(value));
    }
    let substituted_expr;
    let expr = if substitutions.is_empty() {
        expr
    } else {
        substituted_expr = expr.substitute(&substitutions);
        &substituted_expr
    };

    // ACCEPTING path: a `true` here returns `Verified` with no solver call, so
    // the folders must not see through a prophecy (tract19).
    if is_trivially_true_postcondition(expr)
        || matches!(
            eval_simple_bool_literal(expr, ProphecyFold::Opaque),
            Some(true)
        )
    {
        return true;
    }

    if requires.iter().any(|require| {
        let substituted_require;
        let require = if substitutions.is_empty() {
            require
        } else {
            substituted_require = require.substitute(&substitutions);
            &substituted_require
        };
        same_expr(require, expr)
            || matches!(require, PureExpr::BinOp(left, BinOp::And, right)
                if same_expr(left, expr) || same_expr(right, expr))
    }) {
        return true;
    }

    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            postcondition_true_under_context(requires, branch, left)
                && postcondition_true_under_context(requires, branch, right)
        }
        PureExpr::BinOp(left, BinOp::Or, right) => {
            postcondition_true_under_context(requires, branch, left)
                || postcondition_true_under_context(requires, branch, right)
        }
        PureExpr::BinOp(left, BinOp::Implies, right) => {
            simple_false_postcondition(left, ProphecyFold::Opaque)
                || postcondition_true_under_context(requires, branch, right)
        }
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            same_expr(left, right)
                || eval_simple_int_literal(left, ProphecyFold::Opaque)
                    .zip(eval_simple_int_literal(right, ProphecyFold::Opaque))
                    .is_some_and(|(left, right)| left == right)
                || branch_context_forces_equality(requires, branch, left, right)
        }
        PureExpr::BinOp(left, BinOp::Ge, right) => {
            requirements_imply_ge(requires, left, right)
                || branch_context_implies_ge(branch, left, right)
        }
        PureExpr::BinOp(left, BinOp::Le, right) => {
            requirements_imply_ge(requires, right, left)
                || branch_context_implies_ge(branch, right, left)
        }
        _ => false,
    }
}

fn postcondition_false_under_context(
    requires: &[PureExpr],
    branch: Option<(&PureExpr, bool)>,
    expr: &PureExpr,
) -> bool {
    // REFUSING path (its only outcome is `precheck_failed_for_clause`), so the
    // permissive fold is retained for behavioural continuity. (tract19)
    simple_false_postcondition(expr, ProphecyFold::Collapse)
        || branch_context_has_strict_boundary_counterexample(requires, branch, expr)
}

fn branch_context_has_strict_boundary_counterexample(
    requires: &[PureExpr],
    branch: Option<(&PureExpr, bool)>,
    expr: &PureExpr,
) -> bool {
    let Some((cond, true)) = branch else {
        return false;
    };
    let PureExpr::BinOp(cond_left, cond_op, cond_right) = cond else {
        return false;
    };
    let PureExpr::BinOp(expr_left, expr_op, expr_right) = expr else {
        return false;
    };
    match (cond_op, expr_op) {
        (BinOp::Ge, BinOp::Gt) | (BinOp::Le, BinOp::Lt)
            if same_expr(cond_left, expr_left) && same_expr(cond_right, expr_right) =>
        {
            boundary_value_allowed_by_requirements(requires, cond_left, cond_right)
        }
        _ => false,
    }
}

fn boundary_value_allowed_by_requirements(
    requires: &[PureExpr],
    var_expr: &PureExpr,
    value_expr: &PureExpr,
) -> bool {
    let (PureExpr::Var(name, _), PureExpr::Int(value)) = (var_expr, value_expr) else {
        return false;
    };
    let mut bounds = HashMap::new();
    for require in requires {
        collect_simple_var_bounds(require, &mut bounds);
    }
    bounds.get(name).is_none_or(|(lower, upper)| {
        lower.is_none_or(|lower| lower <= *value) && upper.is_none_or(|upper| *value <= upper)
    })
}

fn branch_context_forces_equality(
    requires: &[PureExpr],
    branch: Option<(&PureExpr, bool)>,
    left: &PureExpr,
    right: &PureExpr,
) -> bool {
    let Some((cond, branch_value)) = branch else {
        return false;
    };
    match cond {
        PureExpr::BinOp(cond_left, BinOp::Gt, cond_right) if !branch_value => {
            expr_equiv_for_arithmetic(cond_left, left)
                && expr_equiv_for_arithmetic(cond_right, right)
                && requirements_imply_ge(requires, left, right)
        }
        PureExpr::BinOp(cond_left, BinOp::Lt, cond_right) if !branch_value => {
            expr_equiv_for_arithmetic(cond_left, right)
                && expr_equiv_for_arithmetic(cond_right, left)
                && requirements_imply_ge(requires, left, right)
        }
        PureExpr::BinOp(cond_left, BinOp::Lt, cond_right) if branch_value => {
            expr_equiv_for_arithmetic(cond_left, left)
                && expr_equiv_for_arithmetic(cond_right, right)
                && requirements_imply_ge(requires, left, right)
                && requirements_imply_ge(requires, right, left)
        }
        PureExpr::BinOp(cond_left, BinOp::Gt, cond_right) if branch_value => {
            expr_equiv_for_arithmetic(cond_left, right)
                && expr_equiv_for_arithmetic(cond_right, left)
                && requirements_imply_ge(requires, left, right)
                && requirements_imply_ge(requires, right, left)
        }
        _ => false,
    }
}

fn branch_context_implies_ge(
    branch: Option<(&PureExpr, bool)>,
    left: &PureExpr,
    right: &PureExpr,
) -> bool {
    let Some((cond, branch_value)) = branch else {
        return false;
    };
    match cond {
        PureExpr::BinOp(cond_left, BinOp::Ge | BinOp::Gt, cond_right) if branch_value => {
            expr_equiv_for_arithmetic(cond_left, left)
                && expr_equiv_for_arithmetic(cond_right, right)
        }
        PureExpr::BinOp(cond_left, BinOp::Le | BinOp::Lt, cond_right) if branch_value => {
            expr_equiv_for_arithmetic(cond_left, right)
                && expr_equiv_for_arithmetic(cond_right, left)
        }
        PureExpr::BinOp(cond_left, BinOp::Gt, cond_right) if !branch_value => {
            expr_equiv_for_arithmetic(cond_left, right)
                && expr_equiv_for_arithmetic(cond_right, left)
        }
        PureExpr::BinOp(cond_left, BinOp::Lt, cond_right) if !branch_value => {
            expr_equiv_for_arithmetic(cond_left, left)
                && expr_equiv_for_arithmetic(cond_right, right)
        }
        _ => false,
    }
}

fn requirements_imply_ge(requires: &[PureExpr], left: &PureExpr, right: &PureExpr) -> bool {
    requires
        .iter()
        .any(|require| requirement_implies_ge(require, left, right))
}

fn collect_constructor_pattern_arg_substitutions(
    pattern: Option<&Pattern>,
    args: &[PureExpr],
    substitutions: &mut HashMap<String, PureExpr>,
) -> bool {
    match (pattern, args) {
        (None, []) => true,
        (Some(Pattern::Binding(name)), [arg]) => {
            substitutions.insert(name.clone(), arg.clone());
            substitutions.insert(format!("*{name}"), arg.clone());
            true
        }
        (Some(Pattern::Tuple(patterns)), args) if patterns.len() == args.len() => patterns
            .iter()
            .zip(args)
            .all(|(pattern, arg)| collect_pattern_arg_substitution(pattern, arg, substitutions)),
        _ => false,
    }
}

fn collect_pattern_arg_substitution(
    pattern: &Pattern,
    arg: &PureExpr,
    substitutions: &mut HashMap<String, PureExpr>,
) -> bool {
    match pattern {
        Pattern::Binding(name) => {
            substitutions.insert(name.clone(), arg.clone());
            substitutions.insert(format!("*{name}"), arg.clone());
            true
        }
        Pattern::Literal(expected) => same_expr(expected, arg),
        Pattern::Wildcard => true,
        Pattern::Tuple(patterns) => {
            let PureExpr::LogicFnCall { args, .. } = arg else {
                return false;
            };
            patterns.len() == args.len()
                && patterns.iter().zip(args).all(|(pattern, arg)| {
                    collect_pattern_arg_substitution(pattern, arg, substitutions)
                })
        }
        Pattern::Constructor { name, inner } => {
            let PureExpr::LogicFnCall {
                name: arg_name,
                args,
            } = arg
            else {
                return false;
            };
            crate::encoder::match_enc::short_constructor_name(name)
                == crate::encoder::match_enc::short_constructor_name(arg_name)
                && collect_constructor_pattern_arg_substitutions(
                    inner.as_deref(),
                    args,
                    substitutions,
                )
        }
        Pattern::Alias { alias, pattern } => {
            substitutions.insert(alias.clone(), arg.clone());
            collect_pattern_arg_substitution(pattern, arg, substitutions)
        }
        _ => false,
    }
}

fn precheck_ghost_context_postconditions(
    requires: &[PureExpr],
    ensures: &[PureExpr],
    return_expr: Option<&PureExpr>,
    ghost_context: Option<&[PureExpr]>,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> Option<VerificationResult> {
    if ensures.is_empty() {
        return None;
    }
    let mut saw_context_match = false;
    for ensure in ensures {
        if result_postcondition_matches_return_expr_via_context_fact(
            ensure,
            return_expr,
            ghost_context,
            logic_fns,
        ) || result_postcondition_matches_return_expr_via_logic_bodies(
            ensure,
            logic_fns,
            return_expr,
            requires,
        ) || ghost_alias_postcondition_follows_requires(ensure, requires, ghost_context)
            || ghost_fset_len_postcondition_follows_requires(ensure, requires, ghost_context)
        {
            saw_context_match = true;
            continue;
        }
        return None;
    }
    saw_context_match.then_some(VerificationResult::Verified(None))
}

fn ghost_fset_len_postcondition_follows_requires(
    ensure: &PureExpr,
    requires: &[PureExpr],
    ghost_context: Option<&[PureExpr]>,
) -> bool {
    let Some((receiver, expected)) = len_eq_int_parts(ensure) else {
        return false;
    };
    let mut receivers = vec![receiver.clone()];
    if let Some(ghost_context) = ghost_context {
        for (left, right) in ghost_alias_pairs(ghost_context) {
            if same_expr(&receiver, left) {
                receivers.push(right.clone());
            }
            if same_expr(&receiver, right) {
                receivers.push(left.clone());
            }
        }
    }
    receivers.into_iter().any(|receiver| {
        infer_ghost_fset_len(requires, ensure, &receiver).is_some_and(|actual| actual == expected)
    })
}

#[derive(Default)]
struct GhostFsetFacts {
    contains: Vec<(PureExpr, i64)>,
    not_contains: Vec<(PureExpr, i64)>,
    lens: Vec<(PureExpr, i64)>,
    bools: Vec<(String, bool)>,
    conflict: bool,
}

impl GhostFsetFacts {
    fn insert_contains(&mut self, set: PureExpr, key: i64) -> bool {
        if self.has_contains(&set, key) {
            return false;
        }
        if self.has_not_contains(&set, key) {
            self.conflict = true;
            return false;
        }
        self.contains.push((set, key));
        true
    }

    fn insert_not_contains(&mut self, set: PureExpr, key: i64) -> bool {
        if self.has_not_contains(&set, key) {
            return false;
        }
        if self.has_contains(&set, key) {
            self.conflict = true;
            return false;
        }
        self.not_contains.push((set, key));
        true
    }

    fn insert_len(&mut self, set: PureExpr, len: i64) -> bool {
        if let Some(existing) = self.len_of(&set) {
            if existing != len {
                self.conflict = true;
            }
            return false;
        }
        self.lens.push((set, len));
        true
    }

    fn insert_bool(&mut self, name: &str, value: bool) -> bool {
        if let Some(existing) = self.bool_value(name) {
            if existing != value {
                self.conflict = true;
            }
            return false;
        }
        self.bools.push((name.to_string(), value));
        true
    }

    fn has_contains(&self, set: &PureExpr, key: i64) -> bool {
        self.contains
            .iter()
            .any(|(known_set, known_key)| *known_key == key && same_expr(known_set, set))
    }

    fn has_not_contains(&self, set: &PureExpr, key: i64) -> bool {
        self.not_contains
            .iter()
            .any(|(known_set, known_key)| *known_key == key && same_expr(known_set, set))
    }

    fn len_of(&self, set: &PureExpr) -> Option<i64> {
        self.lens
            .iter()
            .find(|(known_set, _)| same_expr(known_set, set))
            .map(|(_, len)| *len)
    }

    fn bool_value(&self, name: &str) -> Option<bool> {
        self.bools
            .iter()
            .find(|(known_name, _)| known_name == name)
            .map(|(_, value)| *value)
    }
}

struct FsetFrame {
    next: PureExpr,
    previous: PureExpr,
    except: i64,
}

struct FsetBoolDef {
    name: String,
    set: PureExpr,
    key: i64,
    negated: bool,
}

struct FsetLenRule {
    bool_name: String,
    bool_value: bool,
    next: PureExpr,
    previous: PureExpr,
    delta: i64,
}

fn infer_ghost_fset_len(
    requires: &[PureExpr],
    ensure: &PureExpr,
    receiver: &PureExpr,
) -> Option<i64> {
    let mut facts = GhostFsetFacts::default();
    let constants = collect_int_constants_for_ghost_fset(requires, ensure);
    let mut frames = Vec::new();
    let mut bool_defs = Vec::new();
    let mut len_rules = Vec::new();

    for require in requires {
        collect_initial_ghost_fset_facts(require, &constants, &mut facts);
        if let Some(frame) = fset_frame_forall_parts(require) {
            frames.push(frame);
        }
        if let Some(def) = fset_bool_def_parts(require) {
            bool_defs.push(def);
        }
        if let Some(rule) = fset_len_rule_parts(require) {
            len_rules.push(rule);
        }
    }

    for _ in 0..32 {
        let mut changed = false;
        let known_contains = facts.contains.clone();
        let known_not_contains = facts.not_contains.clone();
        for frame in &frames {
            for (set, key) in &known_contains {
                if *key != frame.except && same_expr(set, &frame.previous) {
                    changed |= facts.insert_contains(frame.next.clone(), *key);
                }
                if *key != frame.except && same_expr(set, &frame.next) {
                    changed |= facts.insert_contains(frame.previous.clone(), *key);
                }
            }
            for (set, key) in &known_not_contains {
                if *key != frame.except && same_expr(set, &frame.previous) {
                    changed |= facts.insert_not_contains(frame.next.clone(), *key);
                }
                if *key != frame.except && same_expr(set, &frame.next) {
                    changed |= facts.insert_not_contains(frame.previous.clone(), *key);
                }
            }
        }

        for def in &bool_defs {
            if facts.has_contains(&def.set, def.key) {
                changed |= facts.insert_bool(&def.name, !def.negated);
            }
            if facts.has_not_contains(&def.set, def.key) {
                changed |= facts.insert_bool(&def.name, def.negated);
            }
        }

        for rule in &len_rules {
            if facts.bool_value(&rule.bool_name) == Some(rule.bool_value) {
                if let Some(base_len) = facts.len_of(&rule.previous) {
                    changed |= facts.insert_len(rule.next.clone(), base_len + rule.delta);
                }
            }
        }

        if facts.conflict {
            return None;
        }
        if !changed {
            break;
        }
    }

    facts.len_of(receiver)
}

fn collect_initial_ghost_fset_facts(
    expr: &PureExpr,
    constants: &[i64],
    facts: &mut GhostFsetFacts,
) {
    if let Some((set, key)) = contains_int_parts(expr) {
        let _ = facts.insert_contains(set, key);
        return;
    }
    if let Some((set, key)) = not_contains_int_parts(expr) {
        let _ = facts.insert_not_contains(set, key);
        return;
    }
    if let Some((set, len)) = len_eq_int_parts(expr) {
        let _ = facts.insert_len(set, len);
        return;
    }
    if let PureExpr::Forall { var, body, .. } = expr {
        if let Some(set) = forall_not_contains_parts(var, body) {
            for &constant in constants {
                let _ = facts.insert_not_contains(set.clone(), constant);
            }
        }
    }
}

fn contains_int_parts(expr: &PureExpr) -> Option<(PureExpr, i64)> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if method != "contains" || args.len() != 1 {
        return None;
    }
    let PureExpr::Int(key) = args[0] else {
        return None;
    };
    Some((receiver.as_ref().clone(), key))
}

fn not_contains_int_parts(expr: &PureExpr) -> Option<(PureExpr, i64)> {
    let PureExpr::UnOp(UnOp::Not, inner) = expr else {
        return None;
    };
    contains_int_parts(inner)
}

fn len_eq_int_parts(expr: &PureExpr) -> Option<(PureExpr, i64)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return None;
    };
    len_int_side(left, right).or_else(|| len_int_side(right, left))
}

fn len_int_side(len_expr: &PureExpr, int_expr: &PureExpr) -> Option<(PureExpr, i64)> {
    let PureExpr::Int(value) = int_expr else {
        return None;
    };
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = len_expr
    else {
        return None;
    };
    if method != "len" || !args.is_empty() {
        return None;
    }
    Some((receiver.as_ref().clone(), *value))
}

fn forall_not_contains_parts(var: &str, body: &PureExpr) -> Option<PureExpr> {
    let PureExpr::UnOp(UnOp::Not, inner) = body else {
        return None;
    };
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = inner.as_ref()
    else {
        return None;
    };
    if method == "contains" && matches!(args.as_slice(), [PureExpr::Var(name, _)] if name == var) {
        Some(receiver.as_ref().clone())
    } else {
        None
    }
}

fn fset_frame_forall_parts(expr: &PureExpr) -> Option<FsetFrame> {
    let PureExpr::Forall { var, body, .. } = expr else {
        return None;
    };
    let PureExpr::BinOp(condition, BinOp::Implies, consequence) = body.as_ref() else {
        return None;
    };
    let except = ne_bound_int_parts(condition, var)?;
    let PureExpr::BinOp(left, BinOp::Eq, right) = consequence.as_ref() else {
        return None;
    };
    let (next, previous) = contains_bound_pair_parts(left, right, var)?;
    Some(FsetFrame {
        next,
        previous,
        except,
    })
}

fn ne_bound_int_parts(expr: &PureExpr, var: &str) -> Option<i64> {
    let PureExpr::BinOp(left, BinOp::Ne, right) = expr else {
        return None;
    };
    match (left.as_ref(), right.as_ref()) {
        (PureExpr::Var(name, _), PureExpr::Int(value)) if name == var => Some(*value),
        (PureExpr::Int(value), PureExpr::Var(name, _)) if name == var => Some(*value),
        _ => None,
    }
}

fn contains_bound_pair_parts(
    left: &PureExpr,
    right: &PureExpr,
    var: &str,
) -> Option<(PureExpr, PureExpr)> {
    let left_receiver = contains_bound_receiver(left, var)?;
    let right_receiver = contains_bound_receiver(right, var)?;
    Some((left_receiver, right_receiver))
}

fn contains_bound_receiver(expr: &PureExpr, var: &str) -> Option<PureExpr> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if method == "contains" && matches!(args.as_slice(), [PureExpr::Var(name, _)] if name == var) {
        Some(receiver.as_ref().clone())
    } else {
        None
    }
}

fn fset_bool_def_parts(expr: &PureExpr) -> Option<FsetBoolDef> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return None;
    };
    bool_def_side(left, right).or_else(|| bool_def_side(right, left))
}

fn bool_def_side(name_expr: &PureExpr, value_expr: &PureExpr) -> Option<FsetBoolDef> {
    let PureExpr::Var(name, _) = name_expr else {
        return None;
    };
    if let Some((set, key)) = contains_int_parts(value_expr) {
        return Some(FsetBoolDef {
            name: name.clone(),
            set,
            key,
            negated: false,
        });
    }
    if let Some((set, key)) = not_contains_int_parts(value_expr) {
        return Some(FsetBoolDef {
            name: name.clone(),
            set,
            key,
            negated: true,
        });
    }
    None
}

fn fset_len_rule_parts(expr: &PureExpr) -> Option<FsetLenRule> {
    let PureExpr::BinOp(condition, BinOp::Implies, consequence) = expr else {
        return None;
    };
    let (bool_name, bool_value) = bool_condition_parts(condition)?;
    let PureExpr::BinOp(left, BinOp::Eq, right) = consequence.as_ref() else {
        return None;
    };
    let (next, previous, delta) =
        len_delta_eq_parts(left, right).or_else(|| len_delta_eq_parts(right, left))?;
    Some(FsetLenRule {
        bool_name,
        bool_value,
        next,
        previous,
        delta,
    })
}

fn bool_condition_parts(expr: &PureExpr) -> Option<(String, bool)> {
    match expr {
        PureExpr::Var(name, _) => Some((name.clone(), true)),
        PureExpr::UnOp(UnOp::Not, inner) => {
            if let PureExpr::Var(name, _) = inner.as_ref() {
                Some((name.clone(), false))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn len_delta_eq_parts(next_expr: &PureExpr, rhs: &PureExpr) -> Option<(PureExpr, PureExpr, i64)> {
    let next = len_receiver(next_expr)?;
    if let Some(previous) = len_receiver(rhs) {
        return Some((next, previous, 0));
    }
    let PureExpr::BinOp(left, op @ (BinOp::Add | BinOp::Sub), right) = rhs else {
        return None;
    };
    let previous = len_receiver(left)?;
    let PureExpr::Int(delta) = right.as_ref() else {
        return None;
    };
    let delta = if *op == BinOp::Add { *delta } else { -*delta };
    Some((next, previous, delta))
}

fn len_receiver(expr: &PureExpr) -> Option<PureExpr> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if method == "len" && args.is_empty() {
        Some(receiver.as_ref().clone())
    } else {
        None
    }
}

fn collect_int_constants_for_ghost_fset(requires: &[PureExpr], ensure: &PureExpr) -> Vec<i64> {
    let mut constants = Vec::new();
    for expr in requires.iter().chain(std::iter::once(ensure)) {
        expr.for_each_recursive(|node| {
            if let PureExpr::Int(value) = node {
                if !constants.contains(value) {
                    constants.push(*value);
                }
            }
        });
    }
    constants
}

fn ghost_alias_postcondition_follows_requires(
    ensure: &PureExpr,
    requires: &[PureExpr],
    ghost_context: Option<&[PureExpr]>,
) -> bool {
    if requires.iter().any(|require| same_expr(require, ensure)) {
        return true;
    }
    let Some(ghost_context) = ghost_context else {
        return false;
    };
    let aliases = ghost_alias_pairs(ghost_context);
    aliases.iter().any(|(left, right)| {
        receiver_alias_rewrite(ensure, left, right)
            .as_ref()
            .is_some_and(|rewritten| requires.iter().any(|require| same_expr(require, rewritten)))
            || receiver_alias_rewrite(ensure, right, left)
                .as_ref()
                .is_some_and(|rewritten| {
                    requires.iter().any(|require| same_expr(require, rewritten))
                })
    })
}

fn ghost_alias_pairs(ghost_context: &[PureExpr]) -> Vec<(&PureExpr, &PureExpr)> {
    ghost_context
        .iter()
        .filter_map(|fact| {
            let PureExpr::BinOp(left, BinOp::Eq, right) = fact else {
                return None;
            };
            Some((left.as_ref(), right.as_ref()))
        })
        .collect()
}

fn receiver_alias_rewrite(expr: &PureExpr, from: &PureExpr, to: &PureExpr) -> Option<PureExpr> {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let rewritten_receiver = if same_expr(receiver, from) {
                Some(to.clone())
            } else {
                receiver_alias_rewrite(receiver, from, to)
            };
            let mut changed = false;
            let receiver = if let Some(receiver) = rewritten_receiver {
                changed = true;
                receiver
            } else {
                receiver.as_ref().clone()
            };
            let args: Vec<PureExpr> = args
                .iter()
                .map(|arg| {
                    if let Some(rewritten) = receiver_alias_rewrite(arg, from, to) {
                        changed = true;
                        rewritten
                    } else {
                        arg.clone()
                    }
                })
                .collect();
            changed.then(|| PureExpr::MethodCall {
                receiver: std::sync::Arc::new(receiver),
                method: method.clone(),
                args,
            })
        }
        PureExpr::BinOp(left, op, right) => {
            let left_rewritten = receiver_alias_rewrite(left, from, to);
            let right_rewritten = receiver_alias_rewrite(right, from, to);
            if left_rewritten.is_none() && right_rewritten.is_none() {
                return None;
            }
            Some(PureExpr::BinOp(
                std::sync::Arc::new(left_rewritten.unwrap_or_else(|| left.as_ref().clone())),
                *op,
                std::sync::Arc::new(right_rewritten.unwrap_or_else(|| right.as_ref().clone())),
            ))
        }
        PureExpr::UnOp(op, inner) => receiver_alias_rewrite(inner, from, to)
            .map(|inner| PureExpr::UnOp(*op, std::sync::Arc::new(inner))),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            let cond_rewritten = receiver_alias_rewrite(cond, from, to);
            let then_rewritten = receiver_alias_rewrite(then_expr, from, to);
            let else_rewritten = receiver_alias_rewrite(else_expr, from, to);
            if cond_rewritten.is_none() && then_rewritten.is_none() && else_rewritten.is_none() {
                return None;
            }
            Some(PureExpr::Ite(
                std::sync::Arc::new(cond_rewritten.unwrap_or_else(|| cond.as_ref().clone())),
                std::sync::Arc::new(then_rewritten.unwrap_or_else(|| then_expr.as_ref().clone())),
                std::sync::Arc::new(else_rewritten.unwrap_or_else(|| else_expr.as_ref().clone())),
            ))
        }
        PureExpr::View(inner) => receiver_alias_rewrite(inner, from, to)
            .map(|inner| PureExpr::View(std::sync::Arc::new(inner))),
        PureExpr::Deref(inner) => receiver_alias_rewrite(inner, from, to)
            .map(|inner| PureExpr::Deref(std::sync::Arc::new(inner))),
        PureExpr::Final(inner) => receiver_alias_rewrite(inner, from, to)
            .map(|inner| PureExpr::Final(std::sync::Arc::new(inner))),
        PureExpr::Old(inner) => receiver_alias_rewrite(inner, from, to)
            .map(|inner| PureExpr::Old(std::sync::Arc::new(inner))),
        PureExpr::LogicFnCall { name, args } => {
            let mut changed = false;
            let args: Vec<PureExpr> = args
                .iter()
                .map(|arg| {
                    if let Some(rewritten) = receiver_alias_rewrite(arg, from, to) {
                        changed = true;
                        rewritten
                    } else {
                        arg.clone()
                    }
                })
                .collect();
            changed.then(|| PureExpr::LogicFnCall {
                name: name.clone(),
                args,
            })
        }
        _ => None,
    }
}

pub(super) fn result_postcondition_matches_return_expr_via_context_fact(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    ghost_context: Option<&[PureExpr]>,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> bool {
    let (Some(return_expr), Some(ghost_context)) = (return_expr, ghost_context) else {
        return false;
    };
    let PureExpr::BinOp(left, BinOp::Eq, right) = ensure else {
        return false;
    };
    let expected = match (left.as_ref(), right.as_ref()) {
        (PureExpr::Var(name, _), expected) if name == "result" => expected,
        (expected, PureExpr::Var(name, _)) if name == "result" => expected,
        _ => return false,
    };
    ghost_context.iter().any(|fact| {
        context_fact_equates_exprs(fact, expected, return_expr)
            || logic_fns.is_some_and(|logic_fns| {
                let inlined_expected =
                    inline_expr_with_visible_logic_fns_for_context(expected, logic_fns);
                let inlined_return =
                    inline_expr_with_visible_logic_fns_for_context(return_expr, logic_fns);
                let inlined_fact = inline_expr_with_visible_logic_fns_for_context(fact, logic_fns);
                context_fact_equates_exprs(&inlined_fact, &inlined_expected, &inlined_return)
            })
    })
}

fn context_fact_equates_exprs(fact: &PureExpr, left: &PureExpr, right: &PureExpr) -> bool {
    let PureExpr::BinOp(fact_left, BinOp::Eq, fact_right) = fact else {
        return false;
    };
    (same_expr(fact_left, left) && same_expr(fact_right, right))
        || (same_expr(fact_left, right) && same_expr(fact_right, left))
}

fn inline_expr_with_visible_logic_fns_for_context(
    expr: &PureExpr,
    logic_fns: &[trust_wp_core::logic::LogicFnDef],
) -> PureExpr {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            let args: Vec<PureExpr> = args
                .iter()
                .map(|arg| inline_expr_with_visible_logic_fns_for_context(arg, logic_fns))
                .collect();
            let Some(logic_fn) = logic_fns.iter().find(|logic_fn| {
                logic_fn.name() == name
                    && logic_fn.params().len() == args.len()
                    && !logic_fn.is_opaque()
                    && logic_fn.mode() != LogicMode::Default
                    && logic_fn.requires().is_empty()
            }) else {
                return PureExpr::LogicFnCall {
                    name: name.clone(),
                    args,
                };
            };
            let substitutions: HashMap<String, PureExpr> =
                logic_fn.params().iter().cloned().zip(args).collect();
            inline_expr_with_visible_logic_fns_for_context(
                &logic_fn.body().substitute(&substitutions),
                logic_fns,
            )
        }
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            std::sync::Arc::new(inline_expr_with_visible_logic_fns_for_context(
                left, logic_fns,
            )),
            *op,
            std::sync::Arc::new(inline_expr_with_visible_logic_fns_for_context(
                right, logic_fns,
            )),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            std::sync::Arc::new(inline_expr_with_visible_logic_fns_for_context(
                inner, logic_fns,
            )),
        ),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let receiver = inline_expr_with_visible_logic_fns_for_context(receiver, logic_fns);
            let args: Vec<PureExpr> = args
                .iter()
                .map(|arg| inline_expr_with_visible_logic_fns_for_context(arg, logic_fns))
                .collect();
            let mut logic_args = Vec::with_capacity(args.len() + 1);
            logic_args.push(receiver.clone());
            logic_args.extend(args.iter().cloned());
            if let Some(logic_fn) = logic_fns.iter().find(|logic_fn| {
                logic_fn.name() == method
                    && logic_fn.params().len() == logic_args.len()
                    && !logic_fn.is_opaque()
                    && logic_fn.mode() != LogicMode::Default
                    && logic_fn.requires().is_empty()
            }) {
                let substitutions: HashMap<String, PureExpr> =
                    logic_fn.params().iter().cloned().zip(logic_args).collect();
                return inline_expr_with_visible_logic_fns_for_context(
                    &logic_fn.body().substitute(&substitutions),
                    logic_fns,
                );
            }
            PureExpr::MethodCall {
                receiver: std::sync::Arc::new(receiver),
                method: method.clone(),
                args,
            }
        }
        PureExpr::View(inner) => PureExpr::View(std::sync::Arc::new(
            inline_expr_with_visible_logic_fns_for_context(inner, logic_fns),
        )),
        PureExpr::Deref(inner) => PureExpr::Deref(std::sync::Arc::new(
            inline_expr_with_visible_logic_fns_for_context(inner, logic_fns),
        )),
        PureExpr::Final(inner) => PureExpr::Final(std::sync::Arc::new(
            inline_expr_with_visible_logic_fns_for_context(inner, logic_fns),
        )),
        PureExpr::Old(inner) => PureExpr::Old(std::sync::Arc::new(
            inline_expr_with_visible_logic_fns_for_context(inner, logic_fns),
        )),
        _ => expr.clone(),
    }
}

fn precheck_logic_body_postconditions(
    requires: &[PureExpr],
    ensures: &[PureExpr],
    return_expr: Option<&PureExpr>,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> Option<VerificationResult> {
    let mut all_handled = true;
    let mut saw_verified = false;

    for (clause_idx, ensure) in ensures.iter().enumerate() {
        if result_postcondition_matches_return_expr(ensure, return_expr, requires)
            || result_postcondition_matches_return_expr_via_logic_bodies(
                ensure,
                logic_fns,
                return_expr,
                requires,
            )
            || logic_fn_equality_matches_body(ensure, logic_fns)
            || postcondition_true_via_logic_bodies(ensure, logic_fns)
            || requirements_imply_postcondition_via_logic_bodies(
                ensure,
                logic_fns,
                return_expr,
                requires,
            )
            || result_equals_return_expr_via_logic_body_with_requires(
                ensure,
                logic_fns,
                return_expr,
                requires,
            )
        {
            saw_verified = true;
            continue;
        }

        if result_postcondition_contradicts_return_expr_via_logic_bodies(
            ensure,
            logic_fns,
            return_expr,
            requires,
        ) || result_postcondition_contradicts_return_expr(ensure, return_expr, requires)
            || postcondition_contradicts_return_expr_via_simple_logic(
                ensure,
                logic_fns,
                return_expr,
            )
            || postcondition_false_via_logic_bodies(ensure, logic_fns, requires)
        {
            return Some(precheck_failed_for_clause(clause_idx, ensure));
        }

        if result_equality_mentions_unregistered_logic_call(ensure, logic_fns) {
            return Some(precheck_failed_for_clause(clause_idx, ensure));
        }

        if result_equality_logic_fn_requires_contradict_requirements(ensure, logic_fns, requires) {
            return Some(precheck_failed_for_clause(clause_idx, ensure));
        }

        all_handled = false;
        break;
    }

    (all_handled && saw_verified).then_some(VerificationResult::Verified(None))
}

fn postcondition_contradicts_return_expr_via_simple_logic(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    return_expr: Option<&PureExpr>,
) -> bool {
    let (Some(logic_fns), Some(return_expr)) = (logic_fns, return_expr) else {
        return false;
    };
    let mut substitutions = HashMap::new();
    substitutions.insert("result".to_string(), return_expr.clone());
    let goal = ensure.substitute(&substitutions);
    let goal = inline_expr_with_visible_logic_fns_for_context(&goal, logic_fns);
    // REFUSING path (feeds `precheck_failed_for_clause`). (tract19)
    simple_false_postcondition(&goal, ProphecyFold::Collapse)
}

/// How the syntactic literal folders below treat `PureExpr::Final` (`^e`).
///
/// `^e` names the value a mutable borrow holds when it EXPIRES; the expression
/// underneath is the borrowed place's value in the CURRENT state. Reading a
/// literal value out of `^e` is therefore never a faithful evaluation — it is
/// the `^p == *p` inversion that the encoder's Fix A guard refuses.
///
/// It is nonetheless retained on the paths whose only possible answer is a
/// REFUSAL, because there it can misclassify but never manufacture a proof.
/// Every path whose `true` discharges an obligation must use
/// [`ProphecyFold::Opaque`]. (tract19, Final-collapse audit)
#[derive(Clone, Copy, PartialEq, Eq)]
enum ProphecyFold {
    /// `^e` is opaque: no literal value may be read out of it. REQUIRED
    /// wherever the answer can accept an obligation.
    Opaque,
    /// `^e` folds to `e`. Only legitimate where the answer is a refusal
    /// (`Unknown`/`Failed`) in every branch.
    Collapse,
}

fn simple_false_postcondition(expr: &PureExpr, fold: ProphecyFold) -> bool {
    match expr {
        PureExpr::Bool(false) => true,
        PureExpr::Bool(true) => false,
        PureExpr::UnOp(UnOp::Not, inner) => is_trivially_true_postcondition(inner),
        PureExpr::BinOp(left, BinOp::And, right) => {
            simple_false_postcondition(left, fold) || simple_false_postcondition(right, fold)
        }
        PureExpr::BinOp(left, BinOp::Or, right) => {
            simple_false_postcondition(left, fold) && simple_false_postcondition(right, fold)
        }
        PureExpr::BinOp(left, BinOp::Implies, right) => {
            is_trivially_true_postcondition(left) && simple_false_postcondition(right, fold)
        }
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            if let (Some(left), Some(right)) = (
                eval_simple_int_literal(left, fold),
                eval_simple_int_literal(right, fold),
            ) {
                return left != right;
            }
            if let (Some(left), Some(right)) = (
                eval_simple_bool_literal(left, fold),
                eval_simple_bool_literal(right, fold),
            ) {
                return left != right;
            }
            false
        }
        PureExpr::BinOp(left, BinOp::Ne, right) => same_expr(left, right),
        PureExpr::BinOp(left, BinOp::Lt, right) => eval_simple_int_literal(left, fold)
            .zip(eval_simple_int_literal(right, fold))
            .is_some_and(|(left, right)| left >= right),
        PureExpr::BinOp(left, BinOp::Le, right) => eval_simple_int_literal(left, fold)
            .zip(eval_simple_int_literal(right, fold))
            .is_some_and(|(left, right)| left > right),
        PureExpr::BinOp(left, BinOp::Gt, right) => eval_simple_int_literal(left, fold)
            .zip(eval_simple_int_literal(right, fold))
            .is_some_and(|(left, right)| left <= right),
        PureExpr::BinOp(left, BinOp::Ge, right) => eval_simple_int_literal(left, fold)
            .zip(eval_simple_int_literal(right, fold))
            .is_some_and(|(left, right)| left < right),
        _ => false,
    }
}

fn eval_simple_int_literal(expr: &PureExpr, fold: ProphecyFold) -> Option<i64> {
    match expr {
        PureExpr::Int(value) => Some(*value),
        PureExpr::UnOp(UnOp::Neg, inner) => eval_simple_int_literal(inner, fold)?.checked_neg(),
        PureExpr::BinOp(left, op, right) => {
            let left = eval_simple_int_literal(left, fold)?;
            let right = eval_simple_int_literal(right, fold)?;
            match op {
                BinOp::Add => left.checked_add(right),
                BinOp::Sub => left.checked_sub(right),
                BinOp::Mul => left.checked_mul(right),
                BinOp::Div => left.checked_div(right),
                BinOp::Mod => left.checked_rem(right),
                BinOp::DivTrunc => left.checked_div(right),
                BinOp::RemTrunc => left.checked_rem(right),
                _ => None,
            }
        }
        PureExpr::Final(inner) => match fold {
            ProphecyFold::Opaque => None,
            ProphecyFold::Collapse => eval_simple_int_literal(inner, fold),
        },
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::View(inner) => {
            eval_simple_int_literal(inner, fold)
        }
        _ => None,
    }
}

fn eval_simple_bool_literal(expr: &PureExpr, fold: ProphecyFold) -> Option<bool> {
    match expr {
        PureExpr::Bool(value) => Some(*value),
        PureExpr::UnOp(UnOp::Not, inner) => Some(!eval_simple_bool_literal(inner, fold)?),
        PureExpr::BinOp(left, op, right) => match op {
            BinOp::And => Some(
                eval_simple_bool_literal(left, fold)? && eval_simple_bool_literal(right, fold)?,
            ),
            BinOp::Or => Some(
                eval_simple_bool_literal(left, fold)? || eval_simple_bool_literal(right, fold)?,
            ),
            BinOp::Implies => Some(
                !eval_simple_bool_literal(left, fold)? || eval_simple_bool_literal(right, fold)?,
            ),
            BinOp::Eq => {
                if let (Some(left), Some(right)) = (
                    eval_simple_int_literal(left, fold),
                    eval_simple_int_literal(right, fold),
                ) {
                    return Some(left == right);
                }
                Some(
                    eval_simple_bool_literal(left, fold)? == eval_simple_bool_literal(right, fold)?,
                )
            }
            BinOp::Ne => {
                if let (Some(left), Some(right)) = (
                    eval_simple_int_literal(left, fold),
                    eval_simple_int_literal(right, fold),
                ) {
                    return Some(left != right);
                }
                Some(
                    eval_simple_bool_literal(left, fold)? != eval_simple_bool_literal(right, fold)?,
                )
            }
            BinOp::Lt => {
                Some(eval_simple_int_literal(left, fold)? < eval_simple_int_literal(right, fold)?)
            }
            BinOp::Le => {
                Some(eval_simple_int_literal(left, fold)? <= eval_simple_int_literal(right, fold)?)
            }
            BinOp::Gt => {
                Some(eval_simple_int_literal(left, fold)? > eval_simple_int_literal(right, fold)?)
            }
            BinOp::Ge => {
                Some(eval_simple_int_literal(left, fold)? >= eval_simple_int_literal(right, fold)?)
            }
            _ => None,
        },
        PureExpr::Final(inner) => match fold {
            ProphecyFold::Opaque => None,
            ProphecyFold::Collapse => eval_simple_bool_literal(inner, fold),
        },
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::View(inner) => {
            eval_simple_bool_literal(inner, fold)
        }
        _ => None,
    }
}

/// Syntactic vacuity precheck: are the premises obviously contradictory?
///
/// Uses [`ProphecyFold::Collapse`] deliberately. Its only outcome is
/// `Unknown(VACUOUS)` — a refusal — so a mis-folded `^e` here can cost an
/// honest solve but can never produce a proof.
///
/// ★ Known live consequence (tract19): the driver lowers a base local advanced
/// through a borrow chain to `Final(<its value expression>)`
/// (`mir_analysis/extract/substitution/visitor.rs`, #1581). When that value is
/// a constant, `bug/final_borrows::not_final_borrow_works` gets the premise
/// `View(Final(Int(1))) == 7`, this fold reads it as `1 == 7`, and the
/// obligation demotes as vacuous. That contradiction is FABRICATED. It is left
/// in place only because it is a refusal and because removing it does not make
/// the obligation provable: the same driver defect collapses `^r` and `^r1`
/// onto one carrier, so the honest encoding yields `7 + 7 == 9` instead. The
/// real repair is a per-borrow prophecy carrier plus an expiry-resolution fact
/// for locally-rooted borrows; until then the refusal stays, and no accepting
/// path is allowed to see through a prophecy.
fn requirements_are_obviously_contradictory(requires: &[PureExpr]) -> bool {
    let mut bounds: HashMap<String, (Option<i64>, Option<i64>)> = HashMap::new();
    for require in requires {
        if matches!(
            eval_simple_bool_literal(require, ProphecyFold::Collapse),
            Some(false)
        ) {
            return true;
        }
        collect_simple_var_bounds(require, &mut bounds);
    }
    bounds.values().any(|(lower, upper)| {
        lower
            .zip(*upper)
            .is_some_and(|(lower, upper)| lower > upper)
    })
}

fn collect_simple_var_bounds(
    expr: &PureExpr,
    bounds: &mut HashMap<String, (Option<i64>, Option<i64>)>,
) {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_simple_var_bounds(left, bounds);
            collect_simple_var_bounds(right, bounds);
        }
        _ => {
            if let Some((var, lower, upper)) = simple_var_int_bound(expr) {
                let entry = bounds.entry(var.to_string()).or_insert((None, None));
                if let Some(lower) = lower {
                    entry.0 = Some(entry.0.map_or(lower, |existing| existing.max(lower)));
                }
                if let Some(upper) = upper {
                    entry.1 = Some(entry.1.map_or(upper, |existing| existing.min(upper)));
                }
            }
        }
    }
}

fn simple_var_int_bound(expr: &PureExpr) -> Option<(&str, Option<i64>, Option<i64>)> {
    let PureExpr::BinOp(left, op, right) = expr else {
        return None;
    };
    match (left.as_ref(), op, right.as_ref()) {
        (PureExpr::Var(name, _), BinOp::Gt, PureExpr::Int(n)) => {
            Some((name, n.checked_add(1), None))
        }
        (PureExpr::Var(name, _), BinOp::Ge, PureExpr::Int(n)) => Some((name, Some(*n), None)),
        (PureExpr::Var(name, _), BinOp::Lt, PureExpr::Int(n)) => {
            Some((name, None, n.checked_sub(1)))
        }
        (PureExpr::Var(name, _), BinOp::Le, PureExpr::Int(n)) => Some((name, None, Some(*n))),
        (PureExpr::Var(name, _), BinOp::Eq, PureExpr::Int(n)) => Some((name, Some(*n), Some(*n))),
        (PureExpr::Int(n), BinOp::Lt, PureExpr::Var(name, _)) => {
            Some((name, n.checked_add(1), None))
        }
        (PureExpr::Int(n), BinOp::Le, PureExpr::Var(name, _)) => Some((name, Some(*n), None)),
        (PureExpr::Int(n), BinOp::Gt, PureExpr::Var(name, _)) => {
            Some((name, None, n.checked_sub(1)))
        }
        (PureExpr::Int(n), BinOp::Ge, PureExpr::Var(name, _)) => Some((name, None, Some(*n))),
        (PureExpr::Int(n), BinOp::Eq, PureExpr::Var(name, _)) => Some((name, Some(*n), Some(*n))),
        _ => None,
    }
}

fn result_equality_mentions_unregistered_logic_call(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> bool {
    if logic_fns.is_some_and(|logic_fns| !logic_fns.is_empty()) {
        return false;
    }
    let PureExpr::BinOp(left, BinOp::Eq, right) = ensure else {
        return false;
    };
    result_side_unregistered_logic_call(left, right)
        || result_side_unregistered_logic_call(right, left)
}

fn result_side_unregistered_logic_call(result_side: &PureExpr, value_side: &PureExpr) -> bool {
    matches!(result_side, PureExpr::Var(name, _) if name == "result")
        && matches!(value_side, PureExpr::LogicFnCall { name, .. } if !name.contains("::"))
}

fn result_equality_logic_fn_requires_contradict_requirements(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    requires: &[PureExpr],
) -> bool {
    let Some(logic_fns) = logic_fns else {
        return false;
    };
    let PureExpr::BinOp(left, BinOp::Eq, right) = ensure else {
        return false;
    };
    let logic_call = match (left.as_ref(), right.as_ref()) {
        (PureExpr::Var(name, _), call) if name == "result" => call,
        (call, PureExpr::Var(name, _)) if name == "result" => call,
        _ => return false,
    };
    let PureExpr::LogicFnCall { name, args } = logic_call else {
        return false;
    };
    let Some(logic_fn) = logic_fns
        .iter()
        .find(|f| f.name() == name && f.params().len() == args.len())
    else {
        return false;
    };
    if logic_fn.requires().is_empty() {
        return false;
    }

    let substitutions: HashMap<String, PureExpr> = logic_fn
        .params()
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    let instantiated_requires = logic_fn
        .requires()
        .iter()
        .map(|require| require.substitute(&substitutions));

    let mut bounds = HashMap::new();
    for require in requires {
        collect_simple_var_bounds(require, &mut bounds);
    }
    for require in instantiated_requires {
        collect_simple_var_bounds(&require, &mut bounds);
    }
    bounds.values().any(|(lower, upper)| {
        lower
            .zip(*upper)
            .is_some_and(|(lower, upper)| lower > upper)
    })
}

fn precheck_recursive_postconditions(
    requires: &[PureExpr],
    ensures: &[PureExpr],
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    mode_overrides: Option<&[LogicMode]>,
) -> Option<VerificationResult> {
    let mut saw_recursive = false;
    let mut all_prechecked = true;
    for ensure in ensures {
        if requirement_entails_postcondition(requires, ensure) {
            saw_recursive = true;
            continue;
        }
        if recursive_logic_fn_equality_matches_evaluation(ensure, logic_fns, mode_overrides) {
            saw_recursive = true;
            continue;
        }
        if recursive_postcondition_matches_evaluation_under_requires(
            ensure,
            requires,
            logic_fns,
            mode_overrides,
        ) {
            saw_recursive = true;
            continue;
        }
        // A postcondition that mentions a visible recursive logic fn but does
        // not match one of the recognised inductive-proof shapes above used to
        // trigger an early `Unknown` (without any solver call). That early
        // `Unknown` was spurious for program fns such as cell/02_fib `fib_memo`
        // (postcondition `result@ == fib(i@)`), whose body the precheck cannot
        // recognise but the solver can discharge. Falling through to
        // `all_prechecked = false` DEFERS the obligation to the solver instead.
        // SOUND: converting an early `Unknown` into a solver-defer can never
        // produce a false-accept (a sound solver only proves true goals).
        all_prechecked = false;
    }
    (saw_recursive && all_prechecked).then_some(VerificationResult::Verified(None))
}

fn return_expr_contains_logic_proof_call(
    return_expr: Option<&PureExpr>,
    logic_fns: Option<&[LogicFnDef]>,
) -> bool {
    let (Some(return_expr), Some(logic_fns)) = (return_expr, logic_fns) else {
        return false;
    };
    expr_contains_logic_proof_call(return_expr, logic_fns)
}

fn expr_contains_logic_proof_call(expr: &PureExpr, logic_fns: &[LogicFnDef]) -> bool {
    match expr {
        PureExpr::Let { var, value, body } => {
            if !body.free_vars().contains(var) {
                if let PureExpr::LogicFnCall { name, args } = value.as_ref() {
                    if logic_fns.iter().any(|logic_fn| {
                        logic_fn.name() == name
                            && logic_fn.params().len() == args.len()
                            && !logic_fn.ensures().is_empty()
                    }) {
                        return true;
                    }
                }
            }
            expr_contains_logic_proof_call(body, logic_fns)
        }
        PureExpr::LetAssume { assumption, body } => {
            expr_contains_logic_proof_call(assumption, logic_fns)
                || expr_contains_logic_proof_call(body, logic_fns)
        }
        PureExpr::LetObligation { obligation, body } => {
            expr_contains_logic_proof_call(obligation, logic_fns)
                || expr_contains_logic_proof_call(body, logic_fns)
        }
        PureExpr::Ite(cond, then_branch, else_branch) => {
            expr_contains_logic_proof_call(cond, logic_fns)
                || expr_contains_logic_proof_call(then_branch, logic_fns)
                || expr_contains_logic_proof_call(else_branch, logic_fns)
        }
        PureExpr::BinOp(left, _, right) => {
            expr_contains_logic_proof_call(left, logic_fns)
                || expr_contains_logic_proof_call(right, logic_fns)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_contains_logic_proof_call(inner, logic_fns),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            // A method-syntax call `receiver.method(args)` to a recursive
            // logic fn with ensures (e.g. `l.lemma_sum_nonneg()` inside a
            // `match` arm) is a logic proof call. The receiver counts as
            // the first parameter, so `params().len()` should equal
            // `args.len() + 1`. (#3xxx — recursive &self lemma induction)
            if logic_fns.iter().any(|logic_fn| {
                logic_fn.name() == method
                    && logic_fn.params().len() == args.len() + 1
                    && !logic_fn.ensures().is_empty()
            }) {
                return true;
            }
            expr_contains_logic_proof_call(receiver, logic_fns)
                || args
                    .iter()
                    .any(|arg| expr_contains_logic_proof_call(arg, logic_fns))
        }
        PureExpr::LogicFnCall { name, args } => {
            logic_fns.iter().any(|logic_fn| {
                logic_fn.name() == name
                    && logic_fn.params().len() == args.len()
                    && !logic_fn.ensures().is_empty()
            }) || args
                .iter()
                .any(|arg| expr_contains_logic_proof_call(arg, logic_fns))
        }
        PureExpr::Match { scrutinee, arms } => {
            // Descend into match arm bodies so recursive lemma calls inside
            // pattern arms (the canonical structural-induction shape) are
            // recognized as logic proof calls. (#3xxx)
            expr_contains_logic_proof_call(scrutinee, logic_fns)
                || arms
                    .iter()
                    .any(|arm| expr_contains_logic_proof_call(&arm.body, logic_fns))
        }
        _ => false,
    }
}

#[derive(Clone, Debug)]
struct RecursiveZeroBoundShape {
    function_name: String,
    param_name: String,
}

fn precheck_recursive_zero_bound_structural_induction(
    requires: &[PureExpr],
    ensures: &[PureExpr],
    return_expr: Option<&PureExpr>,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    mode_overrides: Option<&[LogicMode]>,
) -> Option<VerificationResult> {
    let shape = recursive_zero_sum_body_shape(return_expr?)?;
    let mut saw_lower_bound = false;
    for (clause_idx, ensure) in ensures.iter().enumerate() {
        match result_zero_bound_kind(ensure) {
            Some(ZeroBoundKind::Lower) => saw_lower_bound = true,
            Some(ZeroBoundKind::Upper) => {
                let var_expr = PureExpr::Var(shape.param_name.clone(), None);
                if boundary_value_allowed_by_requirements(requires, &var_expr, &PureExpr::Int(1)) {
                    return Some(precheck_failed_for_clause(clause_idx, ensure));
                }
                return None;
            }
            None => return None,
        }
    }

    if !saw_lower_bound {
        return None;
    }

    if recursive_zero_bound_spec_axiom_available(&shape, requires, logic_fns, mode_overrides) {
        return Some(VerificationResult::Verified(None));
    }

    None
}

fn assert_recursive_zero_bound_structural_induction_facts(
    encoder: &mut AYEncoder,
    requires: &[PureExpr],
    ensures: &[PureExpr],
    return_expr: Option<&PureExpr>,
    logic_fns: Option<&[LogicFnDef]>,
    mode_overrides: Option<&[LogicMode]>,
) -> Result<(), EncodingError> {
    if !matches!(
        precheck_recursive_zero_bound_structural_induction(
            requires,
            ensures,
            return_expr,
            logic_fns,
            mode_overrides
        ),
        Some(VerificationResult::Verified(_))
    ) {
        return Ok(());
    }

    let Some(shape) = return_expr.and_then(recursive_zero_sum_body_shape) else {
        return Ok(());
    };
    let Some(logic_fns) = logic_fns else {
        return Ok(());
    };
    let Some((_, logic_fn)) = logic_fns.iter().enumerate().find(|(index, logic_fn)| {
        logic_fn.name() == shape.function_name
            && logic_fn.is_recursive()
            && effective_logic_mode(logic_fn, *index, mode_overrides) == LogicMode::Default
            && logic_fn.params().len() == 1
    }) else {
        return Ok(());
    };

    let caller_param = shape.param_name.clone();
    let predecessor = PureExpr::BinOp(
        Arc::new(PureExpr::Var(caller_param.clone(), None)),
        BinOp::Sub,
        Arc::new(PureExpr::Int(1)),
    );
    let recursive_call = PureExpr::LogicFnCall {
        name: logic_fn.name().to_string(),
        args: vec![predecessor.clone()],
    };
    let param = logic_fn
        .params()
        .first()
        .expect("recursive zero-bound spec has one parameter")
        .clone();
    let mut param_substitutions = HashMap::new();
    param_substitutions.insert(param, predecessor);
    let mut result_substitutions = param_substitutions.clone();
    result_substitutions.insert("result".to_string(), recursive_call);

    let guards: Vec<PureExpr> = logic_fn
        .requires()
        .iter()
        .map(|require| require.substitute(&param_substitutions))
        .collect();
    let mut branch_guards = requires.to_vec();
    branch_guards.push(PureExpr::UnOp(
        UnOp::Not,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var(caller_param, None)),
            BinOp::Le,
            Arc::new(PureExpr::Int(0)),
        )),
    ));
    let mut facts = Vec::new();
    for ensure in logic_fn
        .ensures()
        .iter()
        .filter(|ensure| matches!(result_zero_bound_kind(ensure), Some(ZeroBoundKind::Lower)))
    {
        let instantiated = ensure.substitute(&result_substitutions);
        facts.push(imply_all(&guards, instantiated.clone()));
        facts.push(imply_all(&branch_guards, instantiated));
    }
    if facts.is_empty() {
        return Ok(());
    }

    encoder.register_sort_hints(&facts);
    encoder.register_formula_sort_hints(&facts);
    encoder.with_assertion_phase(AssertionPhase::GroundInstance, |encoder| {
        for fact in &facts {
            let term = encoder.encode_pure(fact)?;
            let term = encoder.coerce_bool_operand(term);
            encoder.assert_term(term);
        }
        Ok(())
    })
}

fn recursive_zero_bound_spec_axiom_available(
    shape: &RecursiveZeroBoundShape,
    requires: &[PureExpr],
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    mode_overrides: Option<&[LogicMode]>,
) -> bool {
    if !requirements_make_var_nonnegative(requires, &shape.param_name) {
        return false;
    }
    let Some(logic_fns) = logic_fns else {
        return false;
    };
    logic_fns.iter().enumerate().any(|(index, logic_fn)| {
        logic_fn.name() == shape.function_name
            && logic_fn.is_recursive()
            && effective_logic_mode(logic_fn, index, mode_overrides) == LogicMode::Default
            && logic_fn.params().len() == 1
            && logic_fn
                .params()
                .first()
                .is_some_and(|param| requirements_make_var_nonnegative(logic_fn.requires(), param))
            && logic_fn
                .ensures()
                .iter()
                .any(|ensure| matches!(result_zero_bound_kind(ensure), Some(ZeroBoundKind::Lower)))
    })
}

fn effective_logic_mode(
    logic_fn: &trust_wp_core::logic::LogicFnDef,
    index: usize,
    mode_overrides: Option<&[LogicMode]>,
) -> LogicMode {
    mode_overrides
        .and_then(|modes| modes.get(index))
        .copied()
        .unwrap_or_else(|| logic_fn.mode())
}

fn recursive_zero_sum_body_shape(expr: &PureExpr) -> Option<RecursiveZeroBoundShape> {
    let PureExpr::Ite(condition, then_branch, else_branch) = expr else {
        return None;
    };
    if !is_zero_literal(then_branch) {
        return None;
    }
    let shape = nonnegative_add_recursive_call_minus_one(else_branch)?;
    condition_is_var_le_zero(condition, &shape.param_name).then_some(shape)
}

fn nonnegative_add_recursive_call_minus_one(expr: &PureExpr) -> Option<RecursiveZeroBoundShape> {
    let PureExpr::BinOp(left, BinOp::Add, right) = expr else {
        return None;
    };
    var_plus_recursive_call_minus_one(left, right)
        .or_else(|| var_plus_recursive_call_minus_one(right, left))
}

fn var_plus_recursive_call_minus_one(
    var_expr: &PureExpr,
    call_expr: &PureExpr,
) -> Option<RecursiveZeroBoundShape> {
    let PureExpr::Var(param_name, _) = var_expr else {
        return None;
    };
    let PureExpr::LogicFnCall { name, args } = call_expr else {
        return None;
    };
    if args.len() != 1 || !expr_is_var_minus_one(&args[0], param_name) {
        return None;
    }
    Some(RecursiveZeroBoundShape {
        function_name: name.clone(),
        param_name: param_name.clone(),
    })
}

fn expr_is_var_minus_one(expr: &PureExpr, var_name: &str) -> bool {
    expr_is_var_minus_int(expr, var_name).is_some_and(|offset| offset == 1)
}

fn expr_is_var_minus_int(expr: &PureExpr, var_name: &str) -> Option<i64> {
    let PureExpr::BinOp(left, BinOp::Sub, right) = expr else {
        return None;
    };
    if matches!(left.as_ref(), PureExpr::Var(name, _) if name == var_name) {
        if let PureExpr::Int(offset) = right.as_ref() {
            return Some(*offset);
        }
    }
    None
}

fn condition_is_var_le_zero(expr: &PureExpr, var_name: &str) -> bool {
    let PureExpr::BinOp(left, op, right) = expr else {
        return false;
    };
    match op {
        BinOp::Le => var_named(left, var_name) && is_zero_literal(right),
        BinOp::Ge => is_zero_literal(left) && var_named(right, var_name),
        _ => false,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ZeroBoundKind {
    Lower,
    Upper,
}

fn result_zero_bound_kind(expr: &PureExpr) -> Option<ZeroBoundKind> {
    let PureExpr::BinOp(left, op, right) = expr else {
        return None;
    };
    match op {
        BinOp::Ge if var_named(left, "result") && is_zero_literal(right) => {
            Some(ZeroBoundKind::Lower)
        }
        BinOp::Le if is_zero_literal(left) && var_named(right, "result") => {
            Some(ZeroBoundKind::Lower)
        }
        BinOp::Le if var_named(left, "result") && is_zero_literal(right) => {
            Some(ZeroBoundKind::Upper)
        }
        BinOp::Ge if is_zero_literal(left) && var_named(right, "result") => {
            Some(ZeroBoundKind::Upper)
        }
        _ => None,
    }
}

fn requirements_make_var_nonnegative(requires: &[PureExpr], var_name: &str) -> bool {
    requires
        .iter()
        .any(|require| requirement_makes_var_nonnegative(require, var_name))
}

fn requirement_makes_var_nonnegative(expr: &PureExpr, var_name: &str) -> bool {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            requirement_makes_var_nonnegative(left, var_name)
                || requirement_makes_var_nonnegative(right, var_name)
        }
        PureExpr::BinOp(left, BinOp::Ge, right) => {
            var_named(left, var_name) && is_zero_literal(right)
        }
        PureExpr::BinOp(left, BinOp::Le, right) => {
            is_zero_literal(left) && var_named(right, var_name)
        }
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            (var_named(left, var_name) && is_zero_literal(right))
                || (is_zero_literal(left) && var_named(right, var_name))
        }
        _ => false,
    }
}

fn var_named(expr: &PureExpr, expected: &str) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == expected)
}

fn is_zero_literal(expr: &PureExpr) -> bool {
    matches!(expr, PureExpr::Int(0))
}

/// Structural-induction precheck for recursive `#[logic]` lemmas of shape
/// `f(self) >= 0` (or `f(self) > 0`) where:
///   * the lemma takes a single ADT-sorted receiver, has one ensures clause, and
///   * its body is `match self { Variant_i(...) => recurse-or-base, ... }`.
///
/// The lemma `lemma_sum_nonneg` from rusthorn `inc_some_list`/`inc_some_tree`
/// matches exactly this shape:
///
/// ```text
/// #[logic]
/// #[ensures(self.sum() >= 0)]
/// fn lemma_sum_nonneg(&self) {
///     match self {
///         Cons(_, l) => l.lemma_sum_nonneg(),
///         Nil => (),
///     }
/// }
/// ```
///
/// Soundness sketch (#trust-wp 4B):
/// Every constructor arm of `f`'s body returns either `0` or a sum of
/// non-negative components (`view`s of unsigned-int bindings) plus recursive
/// `f(sub_binding)` calls. The lemma's match arms cover the same constructors
/// and either base-case (`()`) or recursively invoke the lemma on the same
/// sub-bindings that `f` recurses on. Because each recursive call's argument
/// is a constructor sub-binding, it is structurally smaller; the spec axiom
/// is therefore a valid induction hypothesis, and `f(self) >= 0` follows by
/// unfolding `f`'s definition arm and adding the IH conclusions.
///
/// We accept the proof obligation when:
///   1. the function under test is recursive,
///   2. it has a single ADT-typed parameter,
///   3. its single ensures clause is `f(self) >= 0` for some recursive
///      one-parameter logic-fn `f` defined over the same scrutinee, and `f`'s
///      body decomposes the scrutinee with a match whose arms are either `0`
///      or sums of nonneg-integer terms and recursive `f(sub_binding)` calls,
///   4. the lemma's own body is `match self { ... }` and every arm body is
///      either the unit literal `()` or a let-chain of method/logic-fn calls
///      whose receivers are pattern bindings (i.e., the structural recursion
///      sites match `f`'s recursion sites).
fn precheck_recursive_adt_lemma_structural_induction(
    ensures: &[PureExpr],
    return_expr: Option<&PureExpr>,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    mode_overrides: Option<&[LogicMode]>,
) -> Option<VerificationResult> {
    if ensures.len() != 1 {
        debug!("adt_lemma_precheck: skip — ensures.len()={}", ensures.len());
        return None;
    }
    let body = return_expr?;
    let logic_fns = logic_fns?;

    let (self_param, lemma_arms) = match_on_var_arms(body)?;
    debug!(
        "adt_lemma_precheck: lemma body matches on `{}` with {} arms",
        self_param,
        lemma_arms.len()
    );
    let (helper_call_name, helper_arg_name) =
        recursive_helper_nonneg_ensures_shape(&ensures[0], self_param)?;
    debug!(
        "adt_lemma_precheck: ensures uses helper `{}` on `{}`",
        helper_call_name, helper_arg_name
    );
    if helper_arg_name != self_param {
        return None;
    }
    let (helper_index, helper_fn) = logic_fns.iter().enumerate().find(|(_, lf)| {
        lf.name() == helper_call_name
            && lf.params().len() == 1
            && lf.is_recursive()
            && !lf.is_opaque()
    })?;
    debug!(
        "adt_lemma_precheck: found helper `{}` at index {} (mode={:?})",
        helper_call_name,
        helper_index,
        effective_logic_mode(helper_fn, helper_index, mode_overrides)
    );
    // The helper must remain effectively `Open` (visible body) so its match
    // structure is observable for both the encoder and this precheck.
    if effective_logic_mode(helper_fn, helper_index, mode_overrides) != LogicMode::Open {
        debug!("adt_lemma_precheck: helper not Open");
        return None;
    }
    let helper_param = helper_fn.params().first()?.as_str();
    let helper_arms = match_on_var_arms(helper_fn.body())?;
    if helper_arms.0 != helper_param {
        debug!(
            "adt_lemma_precheck: helper scrutinee `{}` does not match helper param `{}`",
            helper_arms.0, helper_param
        );
        return None;
    }
    debug!(
        "adt_lemma_precheck: helper body has {} arms",
        helper_arms.1.len()
    );

    // Every helper arm body must be either a zero literal (base case) or a
    // sum of nonneg-int terms and recursive helper(sub_binding) calls.
    let mut helper_arm_recursive_sites: HashMap<String, Vec<String>> = HashMap::new();
    for arm in helper_arms.1 {
        let constructor = arm_constructor_name(&arm.pattern)?;
        let bindings = arm_constructor_bindings(&arm.pattern);
        let Some(recursive_targets) =
            helper_arm_nonneg_sum_recursive_targets(&arm.body, helper_call_name, &bindings)
        else {
            debug!(
                "adt_lemma_precheck: helper arm `{}` body is not a nonneg sum: {:?}",
                constructor, arm.body
            );
            return None;
        };
        debug!(
            "adt_lemma_precheck: helper arm `{}` recursion targets: {:?}",
            constructor, recursive_targets
        );
        helper_arm_recursive_sites.insert(constructor, recursive_targets);
    }

    // For every constructor arm in the lemma, ensure the helper has a
    // matching arm and the lemma arm body either base-cases (unit) or
    // recurses on each binding that the helper recurses on. (The precheck
    // does not require strict alignment — additional lemma calls are OK,
    // but the structurally recursive sub-bindings used by `f` must be
    // covered to make the induction sound.)
    for arm in lemma_arms {
        let constructor = arm_constructor_name(&arm.pattern)?;
        let bindings = arm_constructor_bindings(&arm.pattern);
        let Some(helper_targets) = helper_arm_recursive_sites.get(&constructor) else {
            debug!(
                "adt_lemma_precheck: lemma arm `{}` has no matching helper arm",
                constructor
            );
            return None;
        };
        let Some(lemma_recursion_targets) = lemma_arm_recursive_call_targets(&arm.body, &bindings)
        else {
            debug!(
                "adt_lemma_precheck: lemma arm `{}` body shape not recognized: {:?}",
                constructor, arm.body
            );
            return None;
        };
        debug!(
            "adt_lemma_precheck: lemma arm `{}` recursion targets: {:?}",
            constructor, lemma_recursion_targets
        );
        for target in helper_targets {
            if !lemma_recursion_targets.contains(target) {
                debug!(
                    "adt_lemma_precheck: lemma arm `{}` missing recursion on `{}`",
                    constructor, target
                );
                return None;
            }
        }
    }

    debug!("adt_lemma_precheck: VERIFIED");
    Some(VerificationResult::Verified(None))
}

/// If `body` is `Match { scrutinee: Var(name), arms }`, return `(name, arms)`.
fn match_on_var_arms(body: &PureExpr) -> Option<(&str, &[trust_wp_core::formula::MatchArm])> {
    let PureExpr::Match { scrutinee, arms } = body else {
        return None;
    };
    let scrutinee = strip_deref_view(scrutinee);
    let PureExpr::Var(name, _) = scrutinee else {
        return None;
    };
    Some((name.as_str(), arms.as_slice()))
}

/// Peel surface `Deref`/`View` nodes so `match *self` and `match self@` both
/// resolve to the underlying receiver variable.
fn strip_deref_view(expr: &PureExpr) -> &PureExpr {
    let mut current = expr;
    loop {
        match current {
            PureExpr::Deref(inner) | PureExpr::View(inner) => current = inner,
            other => return other,
        }
    }
}

/// Detect a `helper(self) >= 0` or `helper(self) > 0` ensures shape (in both
/// `LogicFnCall` and `MethodCall` orientations) and return `(helper_name,
/// receiver_name)`.
fn recursive_helper_nonneg_ensures_shape<'a>(
    ensure: &'a PureExpr,
    expected_receiver: &str,
) -> Option<(&'a str, &'a str)> {
    let PureExpr::BinOp(left, op, right) = ensure else {
        return None;
    };
    if !matches!(op, BinOp::Ge | BinOp::Gt) {
        return None;
    }
    if !is_zero_literal(right) {
        return None;
    }
    let call_target = strip_deref_view(left);
    match call_target {
        PureExpr::LogicFnCall { name, args } if args.len() == 1 => {
            let arg = strip_deref_view(&args[0]);
            let PureExpr::Var(arg_name, _) = arg else {
                return None;
            };
            (arg_name == expected_receiver).then_some((name.as_str(), arg_name.as_str()))
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if args.is_empty() => {
            let receiver_expr = strip_deref_view(receiver);
            let PureExpr::Var(receiver_name, _) = receiver_expr else {
                return None;
            };
            (receiver_name == expected_receiver)
                .then_some((method.as_str(), receiver_name.as_str()))
        }
        _ => None,
    }
}

/// Extract the constructor name of a top-level pattern (`Cons(_, l)` ->
/// `Cons`, `Nil` -> `Nil`). Returns `None` for wildcard/binding/tuple/literal
/// patterns.
fn arm_constructor_name(pattern: &Pattern) -> Option<String> {
    match pattern {
        Pattern::Constructor { name, .. } => Some(name.clone()),
        Pattern::Alias { pattern, .. } => arm_constructor_name(pattern),
        _ => None,
    }
}

/// Collect named bindings exposed by a constructor pattern's inner sub-pattern
/// (`Cons(_, l)` -> `["l"]`, `Node(tl, _, tr)` -> `["tl", "tr"]`). Wildcards
/// are silently skipped.
fn arm_constructor_bindings(pattern: &Pattern) -> Vec<String> {
    let mut bindings = Vec::new();
    pattern_bindings_into(pattern, &mut bindings);
    bindings
}

fn pattern_bindings_into(pattern: &Pattern, bindings: &mut Vec<String>) {
    match pattern {
        Pattern::Binding(name) => bindings.push(name.clone()),
        Pattern::Tuple(items) => {
            for item in items {
                pattern_bindings_into(item, bindings);
            }
        }
        Pattern::Constructor {
            inner: Some(inner), ..
        } => pattern_bindings_into(inner, bindings),
        Pattern::Alias {
            alias,
            pattern: inner,
        } => {
            bindings.push(alias.clone());
            pattern_bindings_into(inner, bindings);
        }
        Pattern::Constructor { inner: None, .. } | Pattern::Wildcard | Pattern::Literal(_) => {}
        // `Pattern` is `#[non_exhaustive]`; any future variants are treated as
        // opaque (no bindings exposed) so the precheck remains conservative.
        _ => {}
    }
}

/// For a helper arm body, detect a non-negative-sum shape and return the
/// sub-bindings on which `helper` recurses.
///
/// Accepted body shapes (recursively flattened over `+`):
///   * `0`  — base case, no recursive sites.
///   * `view_of(binding)` — `binding@` for an unsigned-integer pattern field;
///     contributes 0 recursive sites.
///   * `helper(binding)` / `binding.helper()` — contributes one recursive site
///     on `binding`.
///   * Any nested `Add` of the above.
///
/// Returns `None` if any operand is neither a zero literal, a `view` of a
/// pattern binding, nor a recursive helper call on a pattern binding.
fn helper_arm_nonneg_sum_recursive_targets(
    body: &PureExpr,
    helper_name: &str,
    bindings: &[String],
) -> Option<Vec<String>> {
    let mut targets = Vec::new();
    if collect_nonneg_sum_operands(body, helper_name, bindings, &mut targets) {
        Some(targets)
    } else {
        None
    }
}

fn collect_nonneg_sum_operands(
    expr: &PureExpr,
    helper_name: &str,
    bindings: &[String],
    targets: &mut Vec<String>,
) -> bool {
    match expr {
        PureExpr::Int(0) => true,
        PureExpr::BinOp(left, BinOp::Add, right) => {
            collect_nonneg_sum_operands(left, helper_name, bindings, targets)
                && collect_nonneg_sum_operands(right, helper_name, bindings, targets)
        }
        PureExpr::View(inner) => {
            // `binding@` — accepted as a nonneg contribution iff the binding
            // is a pattern variable. (The ADT field's integer type controls
            // sign; trust-wp's ADT-field range axioms handle u32/u64.)
            let inner = strip_deref_view(inner);
            matches!(inner, PureExpr::Var(name, _) if bindings.iter().any(|b| b == name))
        }
        PureExpr::LogicFnCall { name, args } if name == helper_name && args.len() == 1 => {
            let arg = strip_deref_view(&args[0]);
            if let PureExpr::Var(arg_name, _) = arg {
                if bindings.iter().any(|b| b == arg_name) {
                    targets.push(arg_name.clone());
                    return true;
                }
            }
            false
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == helper_name && args.is_empty() => {
            let receiver_expr = strip_deref_view(receiver);
            if let PureExpr::Var(receiver_name, _) = receiver_expr {
                if bindings.iter().any(|b| b == receiver_name) {
                    targets.push(receiver_name.clone());
                    return true;
                }
            }
            false
        }
        _ => false,
    }
}

/// For a lemma arm body, return the set of bindings that the lemma recurses
/// on via method-call / logic-fn-call statements. Accepted shapes:
///   * Unit literal `()` — base case (no recursion).
///   * A `Let { var: __stmtN, value: <call>, body: rest }` chain ending in
///     unit or another call. Each `value` must be a `MethodCall` or
///     `LogicFnCall` whose receiver/arg is a pattern binding.
///   * A trailing `MethodCall { receiver: Var(binding), .. }` /
///     `LogicFnCall { args: [Var(binding)] }`.
///
/// Returns `None` if any encountered node is not one of the above shapes.
fn lemma_arm_recursive_call_targets(body: &PureExpr, bindings: &[String]) -> Option<Vec<String>> {
    let mut targets = Vec::new();
    if collect_lemma_recursive_targets(body, bindings, &mut targets) {
        Some(targets)
    } else {
        None
    }
}

fn collect_lemma_recursive_targets(
    expr: &PureExpr,
    bindings: &[String],
    targets: &mut Vec<String>,
) -> bool {
    match expr {
        PureExpr::LogicFnCall { name, args } if is_unit_logic_fn(name) && args.is_empty() => true,
        PureExpr::Let { value, body, .. } => {
            statement_call_target(value, bindings, targets)
                && collect_lemma_recursive_targets(body, bindings, targets)
        }
        PureExpr::MethodCall { .. } | PureExpr::LogicFnCall { .. } => {
            statement_call_target(expr, bindings, targets)
        }
        PureExpr::Bool(true) => {
            // Some lemma bodies use `true` as a terminating trivial value
            // (e.g., when the recursion is purely in a leading statement).
            true
        }
        _ => false,
    }
}

fn statement_call_target(expr: &PureExpr, bindings: &[String], targets: &mut Vec<String>) -> bool {
    match expr {
        PureExpr::MethodCall { receiver, args, .. } if args.is_empty() => {
            let receiver_expr = strip_deref_view(receiver);
            if let PureExpr::Var(receiver_name, _) = receiver_expr {
                if bindings.iter().any(|b| b == receiver_name) {
                    targets.push(receiver_name.clone());
                    return true;
                }
            }
            false
        }
        PureExpr::LogicFnCall { args, .. } if args.len() == 1 => {
            let arg = strip_deref_view(&args[0]);
            if let PureExpr::Var(arg_name, _) = arg {
                if bindings.iter().any(|b| b == arg_name) {
                    targets.push(arg_name.clone());
                    return true;
                }
            }
            false
        }
        // Calls with no arguments (e.g., a side-effecting proof helper) are
        // tolerated only if they have no receiver/arg — they contribute no
        // recursion site but don't disqualify the arm.
        PureExpr::LogicFnCall { args, .. } if args.is_empty() => true,
        _ => false,
    }
}

fn is_unit_logic_fn(name: &str) -> bool {
    name == tuple_logic_fn_name(0)
}

fn precheck_recursive_seq_relation_postconditions(
    ensures: &[PureExpr],
    return_expr: Option<&PureExpr>,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> Option<VerificationResult> {
    if return_expr.is_some() || ensures.is_empty() {
        return None;
    }
    let logic_fns = logic_fns?;
    ensures
        .iter()
        .all(|ensure| recursive_seq_relation_postcondition(ensure, logic_fns))
        .then_some(VerificationResult::Unknown(UnknownReason::Unspecified))
}

fn recursive_seq_relation_postcondition(
    ensure: &PureExpr,
    logic_fns: &[trust_wp_core::logic::LogicFnDef],
) -> bool {
    let PureExpr::BinOp(left, op, right) = ensure else {
        return false;
    };
    if !matches!(
        op,
        BinOp::Le | BinOp::Lt | BinOp::Ge | BinOp::Gt | BinOp::Eq
    ) {
        return false;
    }
    let (
        PureExpr::LogicFnCall {
            name: left_name,
            args: left_args,
        },
        PureExpr::LogicFnCall {
            name: right_name,
            args: right_args,
        },
    ) = (left.as_ref(), right.as_ref())
    else {
        return false;
    };
    if left_name != right_name || left_args.len() != right_args.len() {
        return false;
    }
    logic_fns
        .iter()
        .find(|logic_fn| logic_fn.name() == left_name)
        .is_some_and(|logic_fn| {
            logic_fn_body_calls_itself(logic_fn) && logic_fn_body_uses_index_method(logic_fn)
        })
}

fn logic_fn_body_calls_itself(logic_fn: &trust_wp_core::logic::LogicFnDef) -> bool {
    let name = logic_fn.name();
    logic_fn.body().any_recursive(
        |node| matches!(node, PureExpr::LogicFnCall { name: call_name, .. } if call_name == name),
    )
}

fn logic_fn_body_uses_index_method(logic_fn: &trust_wp_core::logic::LogicFnDef) -> bool {
    logic_fn.body().any_recursive(|node| {
        matches!(
            node,
            PureExpr::MethodCall { method, .. } if method == "index"
        )
    })
}

fn same_expr(left: &PureExpr, right: &PureExpr) -> bool {
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(left, right)
}

fn precheck_type_invariant_postconditions(
    requires: &[PureExpr],
    ensures: &[PureExpr],
    return_expr: Option<&PureExpr>,
    type_invariants: Option<&[TypeInvariantDef]>,
    logic_fns: Option<&[LogicFnDef]>,
) -> Option<VerificationResult> {
    let return_expr = return_expr?;
    if ensures.is_empty() {
        return None;
    }

    let mut saw_invariant = false;
    for (clause_idx, ensure) in ensures.iter().enumerate() {
        let Some(method) = result_type_invariant_method(ensure) else {
            return None;
        };
        saw_invariant = true;
        let Some(inv) = type_invariants.and_then(|invariants| {
            invariants
                .iter()
                .find(|inv| type_invariant_method_name(inv.type_name()) == method)
        }) else {
            return Some(precheck_failed_for_clause(clause_idx, ensure));
        };
        let mut substitutions = std::collections::HashMap::new();
        substitutions.insert(inv.self_param().to_string(), return_expr.clone());
        let body = inv.body().substitute(&substitutions);
        if !type_invariant_body_follows_from_requirements(
            requires,
            &body,
            type_invariants,
            logic_fns,
        ) {
            if type_invariant_body_has_simple_counterexample(
                requires,
                &body,
                type_invariants,
                logic_fns,
            ) {
                return Some(precheck_failed_for_clause(clause_idx, ensure));
            }
            return None;
        }
    }

    saw_invariant.then_some(VerificationResult::Verified(None))
}

fn type_invariant_body_follows_from_requirements(
    requires: &[PureExpr],
    body: &PureExpr,
    type_invariants: Option<&[TypeInvariantDef]>,
    logic_fns: Option<&[LogicFnDef]>,
) -> bool {
    if requirements_include_expr(requires, body) {
        return true;
    }

    let expanded_requirements = expanded_type_invariant_requirements(
        requires,
        type_invariants.unwrap_or(&[]),
        logic_fns.unwrap_or(&[]),
    );
    requirements_include_expr(&expanded_requirements, body)
        || positive_invariant_body_follows_from_requirements(
            body,
            requires.iter().chain(expanded_requirements.iter()),
        )
}

pub(in crate::verify) fn type_invariant_body_has_simple_counterexample(
    requires: &[PureExpr],
    body: &PureExpr,
    type_invariants: Option<&[TypeInvariantDef]>,
    logic_fns: Option<&[LogicFnDef]>,
) -> bool {
    let expanded_requirements = expanded_type_invariant_requirements(
        requires,
        type_invariants.unwrap_or(&[]),
        logic_fns.unwrap_or(&[]),
    );
    positive_invariant_body_has_simple_counterexample(
        body,
        requires.iter().chain(expanded_requirements.iter()),
    )
}

fn expanded_type_invariant_requirements(
    requires: &[PureExpr],
    type_invariants: &[TypeInvariantDef],
    logic_fns: &[LogicFnDef],
) -> Vec<PureExpr> {
    let mut expanded = Vec::new();
    for require in requires {
        collect_expanded_type_invariant_requirements(
            require,
            type_invariants,
            logic_fns,
            &mut expanded,
        );
    }
    expanded
}

fn collect_expanded_type_invariant_requirements(
    require: &PureExpr,
    type_invariants: &[TypeInvariantDef],
    logic_fns: &[LogicFnDef],
    expanded: &mut Vec<PureExpr>,
) {
    match require {
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_expanded_type_invariant_requirements(
                left,
                type_invariants,
                logic_fns,
                expanded,
            );
            collect_expanded_type_invariant_requirements(
                right,
                type_invariants,
                logic_fns,
                expanded,
            );
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if args.is_empty() => {
            if let Some(inv) = type_invariants
                .iter()
                .find(|inv| type_invariant_method_name(inv.type_name()) == *method)
            {
                let mut substitutions = std::collections::HashMap::new();
                substitutions.insert(inv.self_param().to_string(), receiver.as_ref().clone());
                expanded.push(inv.body().substitute(&substitutions));
            }
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            // Inline open logic functions invoked via method syntax (#5): e.g.,
            // `self.sub_pre(rhs)` where `sub_pre` is an open logic predicate
            // expands to its body with `self -> receiver, rhs -> args[0]`. This
            // lets the precheck reason about user-defined predicates the same
            // way it reasons about type-invariant methods.
            if let Some(body) = inline_open_logic_method_call(method, receiver, args, logic_fns) {
                expanded.push(body);
            }
        }
        PureExpr::LogicFnCall { name, args } => {
            // Same as above, but for direct logic-function calls (non-method syntax).
            if let Some(body) = inline_open_logic_fn_call(name, args, logic_fns) {
                expanded.push(body);
            }
        }
        _ => {}
    }
}

/// Inline a method-syntax invocation of an open logic predicate by substituting
/// arguments into the body. Returns `None` if no matching open logic function
/// exists or arities disagree.
fn inline_open_logic_method_call(
    method: &str,
    receiver: &Arc<PureExpr>,
    args: &[PureExpr],
    logic_fns: &[LogicFnDef],
) -> Option<PureExpr> {
    let logic_fn = logic_fns.iter().find(|lf| {
        lf.mode() == LogicMode::Open
            && (lf.name() == method || lf.full_path().ends_with(&format!("::{method}")))
            && lf.params().len() == args.len() + 1
    })?;
    let mut substitutions = HashMap::new();
    let params = logic_fn.params();
    substitutions.insert(params[0].clone(), receiver.as_ref().clone());
    for (param, arg) in params[1..].iter().zip(args.iter()) {
        substitutions.insert(param.clone(), arg.clone());
    }
    Some(logic_fn.body().substitute(&substitutions))
}

/// Inline a `LogicFnCall` invocation of an open logic predicate by substituting
/// arguments into the body.
fn inline_open_logic_fn_call(
    name: &str,
    args: &[PureExpr],
    logic_fns: &[LogicFnDef],
) -> Option<PureExpr> {
    let logic_fn = logic_fns.iter().find(|lf| {
        lf.mode() == LogicMode::Open
            && (lf.name() == name || lf.full_path() == name)
            && lf.params().len() == args.len()
    })?;
    let mut substitutions = HashMap::new();
    for (param, arg) in logic_fn.params().iter().zip(args.iter()) {
        substitutions.insert(param.clone(), arg.clone());
    }
    Some(logic_fn.body().substitute(&substitutions))
}

fn positive_invariant_body_follows_from_requirements<'a>(
    body: &PureExpr,
    requirements: impl Iterator<Item = &'a PureExpr> + Clone,
) -> bool {
    let Some(expr) = strict_positive_goal_expr(body) else {
        return false;
    };
    expr_is_strictly_positive_under_requirements(expr, requirements)
}

fn strict_positive_goal_expr(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::BinOp(left, op, right) = expr else {
        return None;
    };
    match (left.as_ref(), op, right.as_ref()) {
        (value, BinOp::Gt, PureExpr::Int(0)) => Some(value),
        (PureExpr::Int(0), BinOp::Lt, value) => Some(value),
        (value, BinOp::Ge, PureExpr::Int(n)) if *n >= 1 => Some(value),
        (PureExpr::Int(n), BinOp::Le, value) if *n >= 1 => Some(value),
        _ => None,
    }
}

fn expr_is_strictly_positive_under_requirements<'a>(
    expr: &PureExpr,
    requirements: impl Iterator<Item = &'a PureExpr> + Clone,
) -> bool {
    if requirements
        .clone()
        .any(|require| requirement_implies_strict_positive(require, expr))
    {
        return true;
    }

    match expr {
        PureExpr::Int(value) => *value > 0,
        PureExpr::UnOp(UnOp::Neg, _) => false,
        PureExpr::BinOp(left, BinOp::Add, right) => {
            expr_is_strictly_positive_under_requirements(left, requirements.clone())
                && expr_is_strictly_positive_under_requirements(right, requirements)
        }
        PureExpr::BinOp(left, BinOp::Sub, right) => requirements
            .clone()
            .any(|require| requirement_implies_gt(require, left, right)),
        PureExpr::BinOp(left, BinOp::Mul, right) => {
            expr_is_strictly_positive_under_requirements(left, requirements.clone())
                && expr_is_strictly_positive_under_requirements(right, requirements)
        }
        PureExpr::BinOp(left, BinOp::Div, right) => {
            expr_is_strictly_positive_under_requirements(left, requirements.clone())
                && expr_is_strictly_positive_under_requirements(right, requirements.clone())
                && requirements
                    .clone()
                    .any(|require| requirement_implies_ge(require, left, right))
        }
        // `Final` is deliberately absent (tract19): this helper's `true`
        // discharges a positivity obligation with no solver call, and `^e > 0`
        // does not follow from `e > 0` — the prophecy names a state the
        // premise says nothing about.
        PureExpr::Old(inner) | PureExpr::Deref(inner) => {
            expr_is_strictly_positive_under_requirements(inner, requirements)
        }
        PureExpr::View(inner) => expr_is_strictly_positive_under_requirements(inner, requirements),
        _ => false,
    }
}

fn positive_invariant_body_has_simple_counterexample<'a>(
    body: &PureExpr,
    requirements: impl Iterator<Item = &'a PureExpr> + Clone,
) -> bool {
    let Some(expr) = strict_positive_goal_expr(body) else {
        return false;
    };
    expr_can_be_nonpositive_under_requirements(expr, requirements)
}

fn expr_can_be_nonpositive_under_requirements<'a>(
    expr: &PureExpr,
    requirements: impl Iterator<Item = &'a PureExpr> + Clone,
) -> bool {
    if expr_is_strictly_positive_under_requirements(expr, requirements.clone()) {
        return false;
    }

    match expr {
        PureExpr::Int(value) => *value <= 0,
        PureExpr::Var(_, _) => true,
        PureExpr::BinOp(left, BinOp::Add, right) => {
            expr_can_be_nonpositive_under_requirements(left, requirements.clone())
                || expr_can_be_nonpositive_under_requirements(right, requirements)
        }
        PureExpr::BinOp(left, BinOp::Sub, right) => !requirements
            .clone()
            .any(|require| requirement_implies_gt(require, left, right)),
        PureExpr::BinOp(left, BinOp::Mul, right) => {
            let left_positive =
                expr_is_strictly_positive_under_requirements(left, requirements.clone());
            let right_positive =
                expr_is_strictly_positive_under_requirements(right, requirements.clone());
            (left_positive
                && expr_can_be_nonpositive_under_requirements(right, requirements.clone()))
                || (right_positive
                    && expr_can_be_nonpositive_under_requirements(left, requirements.clone()))
                || (!left_positive && !right_positive)
        }
        PureExpr::Old(inner) | PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            expr_can_be_nonpositive_under_requirements(inner, requirements)
        }
        PureExpr::View(inner) => expr_can_be_nonpositive_under_requirements(inner, requirements),
        _ => false,
    }
}

fn requirement_implies_strict_positive(require: &PureExpr, expr: &PureExpr) -> bool {
    match require {
        PureExpr::BinOp(left, BinOp::And, right) => {
            requirement_implies_strict_positive(left, expr)
                || requirement_implies_strict_positive(right, expr)
        }
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            expr_equals_positive_literal(left, right, expr)
                || expr_equals_positive_literal(right, left, expr)
        }
        _ => strict_positive_goal_expr(require)
            .is_some_and(|positive_expr| expr_equiv_for_arithmetic(positive_expr, expr)),
    }
}

fn requirement_implies_ge(require: &PureExpr, left_expr: &PureExpr, right_expr: &PureExpr) -> bool {
    match require {
        PureExpr::BinOp(left, BinOp::And, right) => {
            requirement_implies_ge(left, left_expr, right_expr)
                || requirement_implies_ge(right, left_expr, right_expr)
        }
        PureExpr::BinOp(left, BinOp::Ge | BinOp::Gt, right) => {
            expr_equiv_for_arithmetic(left, left_expr)
                && expr_equiv_for_arithmetic(right, right_expr)
        }
        PureExpr::BinOp(left, BinOp::Le | BinOp::Lt, right) => {
            expr_equiv_for_arithmetic(left, right_expr)
                && expr_equiv_for_arithmetic(right, left_expr)
        }
        _ => false,
    }
}

fn requirement_implies_gt(require: &PureExpr, left_expr: &PureExpr, right_expr: &PureExpr) -> bool {
    match require {
        PureExpr::BinOp(left, BinOp::And, right) => {
            requirement_implies_gt(left, left_expr, right_expr)
                || requirement_implies_gt(right, left_expr, right_expr)
        }
        PureExpr::BinOp(left, BinOp::Gt, right) => {
            expr_equiv_for_arithmetic(left, left_expr)
                && expr_equiv_for_arithmetic(right, right_expr)
        }
        PureExpr::BinOp(left, BinOp::Lt, right) => {
            expr_equiv_for_arithmetic(left, right_expr)
                && expr_equiv_for_arithmetic(right, left_expr)
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "sub_pre" && args.len() == 1 => {
            expr_equiv_for_arithmetic(receiver, left_expr)
                && expr_equiv_for_arithmetic(&args[0], right_expr)
        }
        _ => false,
    }
}

fn expr_equals_positive_literal(candidate: &PureExpr, value: &PureExpr, expr: &PureExpr) -> bool {
    matches!(value, PureExpr::Int(n) if *n > 0) && expr_equiv_for_arithmetic(candidate, expr)
}

/// Structural equivalence used by the arithmetic bound/sign rules below.
///
/// `View`/`Old`/`Deref` are *same-state* projections by the time an expression
/// reaches here — the driver has already substituted `old(e)`'s pre-state term
/// and `Deref(e)`'s `e` is already the referent's value — so folding them
/// through is faithful.
///
/// `Final` is not a projection at all: `^p` names the value the borrow holds
/// when it EXPIRES, and nothing about the expression underneath determines it.
/// Treating `^e` and `e` as the same arithmetic expression lets a premise
/// about the current state discharge a goal about the final state. These
/// helpers feed `postcondition_true_under_context` and
/// `expr_is_strictly_positive_under_requirements`, both of which return
/// `Verified` with no solver call, so that is a false-accept route. Prophecies
/// of the same shape stay comparable (`^a` vs `^b` recurses); only the
/// asymmetric `^e ≡ e` collapse is refused. (tract19, Final-collapse audit)
fn expr_equiv_for_arithmetic(left: &PureExpr, right: &PureExpr) -> bool {
    if same_expr(left, right) {
        return true;
    }
    match (left, right) {
        (PureExpr::View(inner), other) | (other, PureExpr::View(inner)) => {
            expr_equiv_for_arithmetic(inner, other)
        }
        (PureExpr::Final(left_inner), PureExpr::Final(right_inner)) => {
            expr_equiv_for_arithmetic(left_inner, right_inner)
        }
        (PureExpr::Final(_), _) | (_, PureExpr::Final(_)) => false,
        (PureExpr::Old(inner), other)
        | (other, PureExpr::Old(inner))
        | (PureExpr::Deref(inner), other)
        | (other, PureExpr::Deref(inner)) => expr_equiv_for_arithmetic(inner, other),
        _ => false,
    }
}

fn result_type_invariant_method(ensure: &PureExpr) -> Option<&str> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = ensure
    else {
        return None;
    };
    if !args.is_empty() || !matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "result")
    {
        return None;
    }
    method
        .starts_with("__trust_wp_invariant_")
        .then_some(method.as_str())
}

fn requirements_include_expr(requires: &[PureExpr], expr: &PureExpr) -> bool {
    requires
        .iter()
        .any(|require| requirement_includes_expr(require, expr))
}

fn requirement_includes_expr(require: &PureExpr, expr: &PureExpr) -> bool {
    if crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(require, expr) {
        return true;
    }
    match require {
        PureExpr::BinOp(left, BinOp::And, right) => {
            requirement_includes_expr(left, expr) || requirement_includes_expr(right, expr)
        }
        _ => false,
    }
}

fn precheck_ground_disabled_recursive_body(
    logic_ground_mode: LogicGroundInstantiationMode,
    ensures: &[PureExpr],
    return_expr: Option<&PureExpr>,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> Option<VerificationResult> {
    if logic_ground_mode != LogicGroundInstantiationMode::Disabled {
        return None;
    }
    if return_expr_contains_logic_proof_call(return_expr, logic_fns) {
        return None;
    }
    let mentions_recursive_without_specs = return_expr
        .map(|expr| expr_mentions_recursive_logic_fn(expr, logic_fns))
        .unwrap_or(false)
        || ensures
            .iter()
            .any(|ensure| expr_mentions_recursive_logic_fn(ensure, logic_fns));
    mentions_recursive_without_specs
        .then_some(VerificationResult::Unknown(UnknownReason::Unspecified))
}

fn expr_mentions_recursive_logic_fn(
    expr: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> bool {
    let Some(logic_fns) = logic_fns else {
        return false;
    };
    expr.any_recursive(|node| {
        let PureExpr::LogicFnCall { name, .. } = node else {
            return false;
        };
        logic_fns.iter().any(|logic_fn| {
            logic_fn.is_recursive() && logic_fn.ensures().is_empty() && logic_fn.name() == name
        })
    })
}

#[cfg(test)]
mod result_binding_tests;
#[cfg(test)]
mod tests;
