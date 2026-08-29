// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared verification pipeline for function and mut-borrow paths.

use std::{
    collections::{HashMap, HashSet},
    panic::AssertUnwindSafe,
    time::{Duration, Instant},
};

use sha2::{Digest, Sha256};
use tracing::debug;
use trust_wp_core::formula::{BinOp, PureExpr};

use super::{
    obligation_slices::{self, SliceResult},
    profile,
    setup::{setup_verification_encoder, VerificationSetup},
    shared_constraints::{
        assert_ghost_alias_method_congruence, assert_known_ghost_precondition_implications,
        flatten_ghost_implications, instantiate_precondition_foralls_for_ghost,
    },
    solver_tail::{FreshBaseRecheckFn, ObligationSliceContext},
    ResolveContinuation, VerificationResult,
};
use crate::{
    encoder::{is_definitely_non_bool, unsoundness, AYEncoder},
    error::EncodingError,
    shared_types::{ProofAssertSliceCertificate, ProofAssertSliceDerivation},
    verify::types::VerificationBase,
};

const LITERAL_FALSE_CLASSIFICATION_MESSAGE: &str =
    "literal false obligation could not be classified from fresh base state";
const PROOF_ASSERT_SLICE_AUTHORITY_MESSAGE: &str =
    "proof_assert slice lacks exact strict proof authority";

pub(super) type SliceVerifyFn = fn(
    &mut AYEncoder,
    usize,
    &PureExpr,
    &ObligationSliceContext<'_>,
) -> Result<ResolveContinuation, EncodingError>;

pub(super) struct PipelineContext<'encoder, 'data> {
    pub(super) encoder: &'encoder mut AYEncoder,
    pub(super) requires: &'data [PureExpr],
    pub(super) ensures: &'data [PureExpr],
    pub(super) return_expr: Option<&'data PureExpr>,
}

/// Options for [`run_verification_pipeline`] that bundle the per-call
/// configuration parameters, reducing the function's positional argument
/// count below clippy's `too_many_arguments` threshold (#2657).
pub(super) struct PipelineOptions<'a, 'data> {
    /// Expressions providing additional sort-inference context for the encoder.
    pub(super) context_exprs: &'a [&'data PureExpr],
    /// Mut-borrow final-state bindings used to ground raw postconditions.
    pub(super) mut_borrow_final_values: Option<&'a HashMap<String, PureExpr>>,
    /// Mut-borrow parameters whose final state is constrained by call assumptions.
    pub(super) mutation_continued_params: Option<&'a HashSet<String>>,
    /// Debug prefix for closure capture projection messages.
    pub(super) closure_capture_debug_prefix: &'a str,
    /// Debug label for axiom-only function detection messages.
    pub(super) axiom_debug_label: &'a str,
    /// Optional callback to re-verify from a fresh encoder base when the
    /// primary solve returns Unknown.
    pub(super) fresh_base_recheck: Option<&'a FreshBaseRecheckFn<'data>>,
    /// Optional axiom-light fresh-base callback for literal `false`
    /// postconditions. This path only needs a conservative SAT witness to
    /// report `Failed`; quantified standard axioms can turn that base probe
    /// into an unrelated `Unknown`.
    pub(super) literal_false_base_recheck: Option<&'a FreshBaseRecheckFn<'data>>,
    /// Whether syntactic/structural checks may return `Verified` without a
    /// solver-backed negated-goal proof.
    pub(super) structural_verified_shortcuts: bool,
    /// `&mut [T]` slice parameter names for slice-length-preservation axioms,
    /// emitted at goal-check time (after the negated goal introduces nested
    /// prophecy length symbols).
    pub(super) slice_length_stable_vars: Option<&'a Vec<String>>,
    /// PreparedAssertion-side `(ensures, requires)` source for proof_assert
    /// slice claims and derivations.
    ///
    /// The proof_assert certificate's `prepared_claim` is specified as the
    /// STABLE PreparedAssertion-side claim text: the reporting process
    /// independently recomputes it from the original `PreparedAssertion` and
    /// refuses any certificate whose claim differs ("certificate source claim
    /// mismatch"). A lane that rewrites `base.ensures`/`base.requires` before
    /// the pipeline (the mut-borrow lane's temporal-wrapper preservation
    /// erases non-MutRef `Var` sort annotations under `Deref`/`Final`) must
    /// pass the ORIGINAL slices here so certificates keep carrying the claim
    /// text the driver firewall compares against. `None` means
    /// `base.ensures`/`base.requires` already ARE the PreparedAssertion-side
    /// source (the plain function lane). The prepared/normalized slice-count
    /// guard still fail-closes if a lane rewrite ever changes the top-level
    /// conjunct structure.
    pub(super) proof_assert_prepared_source: Option<(&'data [PureExpr], &'data [PureExpr])>,
}

/// Catch ay panics during a verification phase, restoring unsoundness
/// counters on failure.
///
/// When a caught panic (or `EncodingError`) occurs, any unsoundness counter
/// increments from inside the closure are stale — they reflect partial
/// encoding that will not be used. Restoring the pre-call snapshot prevents
/// these phantom increments from polluting the demotion baseline for
/// subsequent verifications on the same thread. (#2623)
pub(crate) fn catch_verification_phase_ay_panics<T, F>(
    phase: &'static str,
    f: F,
) -> Result<T, EncodingError>
where
    F: FnOnce() -> Result<T, EncodingError> + std::panic::UnwindSafe,
{
    let pre_snapshot = unsoundness::snapshot();
    let result = super::catch_ay_panics_tightened(f, |reason| {
        Err(EncodingError::solver_error(format!(
            "ay solver panic during verification phase `{phase}`: {reason}"
        )))
    });
    if result.is_err() {
        unsoundness::restore(&pre_snapshot);
    }
    result
}

#[allow(clippy::too_many_lines)]
pub(super) fn run_verification_pipeline<'data, F, B, G>(
    base: VerificationBase<'data>,
    options: &PipelineOptions<'_, 'data>,
    path_specific_fn: F,
    before_solve: B,
    slice_verify_fn: SliceVerifyFn,
) -> Result<(VerificationResult, Option<super::VerificationProvenance>), EncodingError>
where
    F: for<'encoder> FnOnce(&mut PipelineContext<'encoder, 'data>) -> Result<(), EncodingError>,
    B: FnOnce() -> G,
{
    let VerificationBase {
        requires,
        ensures,
        ghost_context,
        return_expr,
        logic_fns,
        mode_overrides,
        type_invariants,
        track,
        timeout,
        type_constants,
        closure_captures,
        total_int_arithmetic,
        adt_field_ranges,
        adt_decls,
        unsoundness_snapshot: driver_snapshot,
        logic_ground_mode,
        bitwise_proof,
        local_unfolding_logic_fns: _,
    } = base;
    let track = track.unwrap_or_default();
    let pre_setup_snapshot = driver_snapshot
        .clone()
        .unwrap_or_else(unsoundness::snapshot);

    let setup_result = catch_verification_phase_ay_panics(
        "setup_verification_encoder",
        AssertUnwindSafe(|| {
            setup_verification_encoder(&VerificationSetup {
                requires,
                ensures,
                context_exprs: options.context_exprs,
                result_expr: return_expr,
                ghost_context,
                logic_fns,
                mode_overrides,
                type_invariants,
                track,
                timeout,
                type_constants,
                closure_captures,
                adt_decls: adt_decls.as_ref(),
                adt_field_ranges: adt_field_ranges.as_ref(),
            })
        }),
    )?;
    let mut encoder = setup_result.encoder;
    let effective_logic_fns = setup_result.filtered_logic_fns.as_deref();
    let effective_mode_overrides = setup_result.filtered_mode_overrides.as_deref();

    // Use the post-bootstrap snapshot (after sort hints / logic fn decls /
    // type invariant registration, but BEFORE precondition encoding) so that
    // only bootstrap false-positive increments are absorbed into the baseline.
    // Previously this used the full post-setup snapshot, which also absorbed
    // real precondition-phase increments for SortFallbackToIntFromLogicFn. (#2623)
    let demotion_baseline = super::merge_pre_verification_and_post_bootstrap_snapshots(
        &pre_setup_snapshot,
        &setup_result.post_bootstrap_snapshot,
    );

    encoder.set_total_int_arithmetic(total_int_arithmetic);
    encoder.set_logic_ground_mode(logic_ground_mode);
    encoder.set_bitwise_proof_mode(bitwise_proof);
    if let Some(ranges) = adt_field_ranges {
        encoder.set_adt_field_ranges(ranges);
    }

    let mut ghost_precondition_implications = Vec::new();
    if let Some(ghost_exprs) = ghost_context {
        for ghost_expr in ghost_exprs {
            let term = encoder.encode_pure(ghost_expr)?;
            // Defensive Bool-coercion at the assumption boundary. Chained
            // `Mapping<_, Bool>::get(...)` calls (e.g. the second `such_that`
            // witness in `such_that.rs`) can produce Int-sorted terms when
            // sort inference loses the Bool context through Deref+MethodCall.
            // Coercing through `!= 0` recovers the right Bool truth value
            // because Bool is encoded as 0/1 Int. (#5, design
            // 2026-05-19-such-that-strict-pass-residual.md Gap 1 §1)
            let bool_term = encoder.coerce_bool_operand(term);
            encoder.assert_term(bool_term);
        }
        flatten_ghost_implications(&mut encoder, ghost_exprs)?;
        // Cross-domain forall instantiation: precondition foralls (e.g., FSet
        // emptiness axioms) need ground instances from ghost+precondition
        // constants to connect with ghost mutation chains. (#2671)
        instantiate_precondition_foralls_for_ghost(&mut encoder, requires, ensures, ghost_exprs)?;
        ghost_precondition_implications = assert_known_ghost_precondition_implications(
            &mut encoder,
            requires,
            ensures,
            ghost_exprs,
        )?;
        let alias_requires_storage;
        let alias_requires = if ghost_precondition_implications.is_empty() {
            requires
        } else {
            alias_requires_storage = requires
                .iter()
                .chain(ghost_precondition_implications.iter())
                .cloned()
                .collect::<Vec<_>>();
            alias_requires_storage.as_slice()
        };
        assert_ghost_alias_method_congruence(&mut encoder, alias_requires, ensures, ghost_exprs)?;
    }
    super::assert_container_element_invariants(&mut encoder, requires, type_invariants)?;

    path_specific_fn(&mut PipelineContext {
        encoder: &mut encoder,
        requires,
        ensures,
        return_expr,
    })?;

    if let Some(captures) = closure_captures {
        super::assert_closure_capture_projections(
            &mut encoder,
            captures,
            options.closure_capture_debug_prefix,
        )?;
        super::assert_captured_param_type_invariants(
            &mut encoder,
            captures,
            type_invariants,
            requires,
        )?;
    }

    for expr in ensures {
        if is_definitely_non_bool(expr) {
            let sort = encoder.infer_expr_sort_with_context(expr, None);
            return Err(EncodingError::unsupported(format!(
                "postcondition/assertion must be boolean, got {sort:?}: {expr:?}"
            )));
        }
    }

    // Drain body-side arithmetic obligations (divisor != 0, shift-amount
    // range) BEFORE the empty-ensures shortcut so they cannot be silently
    // discarded: body encoding runs in `path_specific_fn` above even when
    // postconditions never mention `result` (#994), so a contract-free (or
    // trivially-true) spec over an unsafe body still owes these proofs.
    // (ledger int-shift-full)
    let body_div_obligations = encoder.take_division_obligations();

    // An empty postcondition set with pending body obligations must still
    // prove them: substitute the trivial goal `true` so the standard slice
    // machinery checks `NOT(true AND obligations)` — i.e. the obligations
    // themselves — instead of returning the empty-obligation-set proof.
    // Previously `#[ensures(true)]` over `1u8 >> 8` verified through this
    // shortcut without ever consulting the collected obligations.
    let trivial_obligation_goal_storage: [PureExpr; 1];
    let ensures: &[PureExpr] = if ensures.is_empty() && !body_div_obligations.is_empty() {
        trivial_obligation_goal_storage = [PureExpr::Bool(true)];
        &trivial_obligation_goal_storage
    } else {
        ensures
    };

    if ensures.is_empty() {
        encoder.ensure_structural_provenance("empty-obligation-set");
        let result = super::solver_tail::prove_prechecked_literal_false_with_solver_evidence();
        let mut provenance = encoder.capture_provenance(Duration::ZERO);
        if matches!(result, VerificationResult::Verified(_)) {
            install_preferred_verified_solve_diagnostics(&mut provenance, &encoder);
        } else {
            super::solver_tail::clear_preferred_verified_solve_evidence();
        }
        let result = super::demote_if_unsound(&demotion_baseline, result);
        let provenance = Some(provenance);
        return Ok((result, provenance));
    }

    if super::function::is_axiom_only_function(
        requires,
        ensures,
        return_expr,
        type_invariants,
        ghost_context,
        effective_logic_fns,
    ) {
        let reason = format!(
            "axiom-only function: {} universal postcondition(s) with trivial body",
            ensures.len()
        );

        debug!(
            "  axiom-only {} detected: {reason} — \
                 returning Assumed (#1753, #2365)",
            options.axiom_debug_label,
        );

        return Ok((VerificationResult::Assumed(reason), None));
    }

    debug!("  encoding postconditions, vars: {:?}", encoder.var_names());
    for ensure in ensures {
        debug!("    post: {ensure:?}");
    }
    debug!("  logic_funcs: {:?}", encoder.logic_func_names());
    debug!("  spec_functions: {:?}", encoder.spec_func_names());
    debug!(
        "  obligation slicing: {} ensures, {} body div obligations",
        ensures.len(),
        body_div_obligations.len()
    );

    let _solve_guard = before_solve();

    let effective_requires_storage;
    let obligation_requires = if let Some(ghost_exprs) = ghost_context {
        effective_requires_storage = requires
            .iter()
            .chain(ghost_exprs.iter())
            .chain(ghost_precondition_implications.iter())
            .cloned()
            .collect::<Vec<_>>();
        effective_requires_storage.as_slice()
    } else {
        requires
    };

    // Inline transparent logic functions whose body hides a universal
    // quantifier (e.g. `#[ensures(result.wf())]`). Left opaque, the negated
    // goal `not(wf(result))` is over an uninterpreted `wf` whose definition is
    // only a quantified bi-implication; ay-dpll cannot skolemize the hidden
    // `forall` to instantiate the supporting per-element facts. Inlining the
    // definitional body surfaces the quantifier so the negated-postcondition
    // router Skolemizes it. Sound: the body is definitionally equal to the
    // call. Scoped tightly — only clauses whose expansion newly surfaces a
    // quantifier are rewritten (every other ensures stays byte-identical), so
    // there is no behavioural change off this path. (#2170)
    let proof_assert_mode = super::solver_tail::in_proof_assert_mode();
    // Compute the certificate-side prepared claims from the
    // PreparedAssertion-side expressions, NOT from any lane-normalized form:
    // the reporting firewall recomputes these byte-for-byte from the original
    // PreparedAssertion and refuses certificates that disagree.
    let (prepared_source_ensures, prepared_source_requires) = options
        .proof_assert_prepared_source
        .unwrap_or((ensures, requires));
    let prepared_slice_claims =
        super::obligation_slices::proof_assert_obligation_slice_claims(prepared_source_ensures);
    let prepared_slice_derivations =
        super::obligation_slices::proof_assert_obligation_slice_derivations(
            prepared_source_ensures,
            prepared_source_requires,
        );
    let expanded_ensures: Vec<PureExpr> = ensures
        .iter()
        .map(|e| super::setup::expand_transparent_logic_fn_goal_if_surfaces_quantifier(&encoder, e))
        .collect();
    let ensures: &[PureExpr] = &expanded_ensures;

    let shared_ctx = ObligationSliceContext {
        all_ensures: ensures,
        requires: obligation_requires,
        logic_fns: effective_logic_fns,
        mode_overrides: effective_mode_overrides,
        type_invariants,
        return_expr,
        mut_borrow_final_values: options.mut_borrow_final_values,
        mutation_continued_params: options.mutation_continued_params,
        body_div_obligations: &body_div_obligations,
        fresh_base_recheck: options.fresh_base_recheck,
        slice_length_stable_vars: options.slice_length_stable_vars,
        base_recheck_pathology: std::cell::Cell::new(false),
    };
    let slices = obligation_slices::split_ensures(ensures);
    if proof_assert_mode {
        if let Some(result) =
            proof_assert_slice_count_mismatch_result(prepared_slice_claims.len(), slices.len())
        {
            super::solver_tail::clear_preferred_verified_solve_evidence();
            return Ok((result, Some(encoder.capture_provenance(Duration::ZERO))));
        }
    }
    let per_slice_budget = if slices.len() > 1 {
        // Per-slice ground pool budget (#2674): distribute the global budget
        // across obligation slices with a floor of 30 (reduced from 50).
        // The floor reduction is safe because:
        // 1. The axiom-free probe (Phase 1) resolves simple obligations before
        //    ground pool instances are needed.
        // 2. Contract-critical axioms bypass the budget gate (#1296).
        // 3. Priority-sorted instantiation ensures the highest-value axioms
        //    get instances first even with a smaller per-slice budget.
        // For a 10-slice function: budget = max(300/10, 30) = 30 instances,
        // saving encoding + solver time on the remaining 20 instances per slice.
        Some((300 / slices.len()).max(30))
    } else {
        None
    };
    // Bake the override into the per-slice dedup baseline so restoring slice
    // state does not drop the budget override before the flush. (#2674)
    encoder.set_ground_pool_per_slice_budget(per_slice_budget);
    let mut slice_results: Vec<SliceResult> = Vec::with_capacity(slices.len());
    // Snapshot all scope-sensitive assert-once state before the slice loop.
    // Each slice iteration restores this baseline so popped assertions are
    // re-emitted rather than skipped by stale dedup entries. (#2618)
    let dedup_baseline = encoder.dedup_snapshot();

    // Per-function wall-clock timeout guard (#2674): once any slice returns
    // Unknown(Timeout) or Abort(Timeout), skip remaining slices immediately.
    // Functions with many postconditions (e.g., iterator specs with 10+
    // ensures) would otherwise accumulate N × hard_timeout wall-clock seconds,
    // far exceeding the compat harness limit. The first timeout is sufficient
    // evidence that subsequent axiom-dependent slices will also timeout.
    let mut saw_timeout = false;
    // Per-function Unknown(Incomplete) early termination (#2674): when a slice
    // returns Unknown(Incomplete) or Unknown(QuantifierRoundLimit), subsequent
    // slices sharing the same axiom context will likely hit the same solver
    // limitation. For multi-slice functions only, skip remaining slices as
    // Unknown(Incomplete) to avoid accumulating wall-clock time. This is
    // conservative: single-slice functions are unaffected, and the skip only
    // fires for genuinely solver-limited reasons, not vacuity or timeout.
    let mut saw_incomplete = false;
    // Literal-false obligations only need a satisfiable base witness to become
    // concrete failures. Classify them from a fresh base recheck instead of
    // spending the full obligation solver budget on quantified axiom context.
    let mut literal_false_result: Option<VerificationResult> = None;

    // Adaptive per-function timeout budget (#2674): for functions with multiple
    // obligation slices, track wall-clock time and reduce per-slice solver
    // timeout as time budget is consumed. Without this, an N-slice function
    // can consume N × (solver_timeout + retry_timeout + hard_timeout) wall-
    // clock seconds, far exceeding the compat harness limit (120s default).
    //
    // The budget is 2× the original solver timeout for the entire function
    // (#2674). When remaining budget drops below the original solver timeout,
    // the per-slice timeout is reduced proportionally. This ensures:
    // - Single-slice functions: no change (full timeout available)
    // - Multi-slice with fast early slices: later slices get full timeout
    // - Multi-slice with slow early slices: later slices get reduced timeout
    //   to stay within the overall wall-clock budget
    let solve_start = Instant::now();
    super::solver_tail::clear_preferred_verified_solve_evidence();
    let mut proof_assert_certificates = Vec::with_capacity(slices.len());
    let original_solver_timeout = encoder.solver().timeout();
    let function_time_budget = original_solver_timeout.map(|t| {
        // 1.5× solver timeout for the entire function (#2674): reduced from
        // 2× to further tighten multi-slice function wall-clock budgets and
        // fit within the compat harness limit (120s). For a 60s solver timeout,
        // the budget is 90s. The first obligation slice gets the full solver
        // timeout; subsequent slices share the remaining budget.
        //
        // Combined with budget-aware retry skipping, tight base-recheck
        // envelopes (15s cap), and the reduced hard-timeout multiplier
        // (1.5× + grace), this ensures that a single function cannot exceed
        // the harness wall-clock limit. The hard-timeout envelope (1.5× solver
        // timeout + grace = 90.1s) bounds each individual slice, and the
        // function budget ensures multi-slice functions stay within the
        // compat harness limit.
        //
        // Worst case for a single-slice function: tiered probe (10s) +
        // full solve (60s, no retry after probe) + base recheck (20s in
        // tight 26s envelope) = 90s, matching the budget.
        // For multi-slice: first slice may consume up to 90s of the budget,
        // subsequent slices get minimal timeout (MIN_SLICE_TIMEOUT).
        // Previously at 2× (120s), this gave multi-slice functions too much
        // wall-clock time that accumulated across all functions in a file.
        t + t / 2
    });

    // Minimum per-slice solver timeout (#2674): never reduce below this
    // threshold. Reduced from 5s to 3s: the axiom-free probe (500ms)
    // resolves most simple obligations, and the tiered probe (10s) is
    // only triggered for solver timeouts >= 15s. At 3s, the solver can
    // still make meaningful progress on axiom-free obligations while
    // preserving budget for subsequent slices. Combined with the
    // function time budget reduction (2× from 2.5×), this ensures
    // multi-slice functions complete within the compat harness limit.
    const MIN_SLICE_TIMEOUT: Duration = Duration::from_secs(3);

    for (slice_position, slice) in slices.iter().enumerate() {
        let slice_ordinal = u64::try_from(slice_position).unwrap_or(u64::MAX);
        let prepared_claim = if proof_assert_mode {
            prepared_slice_claims[slice_position].clone()
        } else {
            String::new()
        };
        let derivation = if proof_assert_mode {
            prepared_slice_derivations[slice_position]
        } else {
            ProofAssertSliceDerivation::NativeEncoded
        };
        let prepared_claim_hash = proof_assert_prepared_claim_hash(slice_ordinal, &prepared_claim);
        let (normalized_claim, normalized_claim_hash) =
            proof_assert_claim_identity(slice_ordinal, slice.ensure.as_ref());
        if proof_assert_mode {
            encoder.clear_last_solve_diagnostics();
            super::solver_tail::clear_preferred_verified_solve_evidence();
        }
        let slice_identity = super::solver_tail::ProofAssertSliceIdentity::new(
            slice_ordinal,
            prepared_claim_hash,
            normalized_claim_hash,
        );
        let _proof_assert_slice_guard = proof_assert_mode
            .then(|| super::solver_tail::ProofAssertSliceClaimGuard::enter(slice_identity));
        encoder.set_ground_pool_per_slice_budget(per_slice_budget);

        // Literal `true` and an exact prepared premise have tiny structural
        // proof rules that the reporting process can independently recover
        // from the original PreparedAssertion. AY still checks a trust-free
        // Boolean UNSAT kernel so no bare structural `Verified` result crosses
        // the proof-assert authority boundary.
        if proof_assert_mode && derivation != ProofAssertSliceDerivation::NativeEncoded {
            debug!(
                "  slice[{}]: discharging independently rechecked {:?} derivation",
                slice.index, derivation,
            );
            let result = super::solver_tail::prove_prechecked_literal_false_with_solver_evidence();
            let (result, certificate) = authorize_proof_assert_slice(
                slice_ordinal,
                derivation,
                &prepared_claim,
                prepared_claim_hash,
                &normalized_claim,
                normalized_claim_hash,
                result,
            );
            if let Some(certificate) = certificate {
                proof_assert_certificates.push(certificate);
            }
            slice_results.push(SliceResult {
                index: slice.index,
                result,
            });
            continue;
        }

        // Trivially-true precheck (#5): try to discharge the slice via
        // PureExpr-level inlining + simplification under requires BEFORE
        // any `saw_incomplete` / `saw_timeout` skipping fires. Set-bit /
        // unset-bit style obligations reduce to `(1 << bit) != 0` or
        // `0 != 0` after BV absorption, which is decidable without the
        // solver. Running this check up-front lets us verify a slice even
        // when a preceding slice returned `Unknown(Incomplete)` and would
        // otherwise drag the whole function into Unknown.
        if !proof_assert_mode
            && super::result_postcondition_matches_return_expr_via_logic_bodies(
                slice.ensure.as_ref(),
                effective_logic_fns,
                return_expr,
                obligation_requires,
            )
        {
            debug!(
                "  slice[{}]: trivially-true via logic-body inlining, discharging via fresh literal-false solve",
                slice.index,
            );
            // Discharge via a fresh literal-false solver invocation so the
            // slice contributes a real `Unsat` solve evidence record (the
            // function pipeline's verified-result guard requires structural
            // provenance to include accepted solver evidence; bare
            // `Verified(None)` here regresses logic-fn tests).
            let result = super::solver_tail::prove_prechecked_literal_false_with_solver_evidence();
            slice_results.push(SliceResult {
                index: slice.index,
                result,
            });
            continue;
        }

        // Skip remaining slices after a timeout — they share the same axiom
        // context and will hit the same solver limitation. Record them as
        // Unknown(Timeout) without invoking the solver. (#2674)
        if saw_timeout {
            debug!(
                "  slice[{}]: skipped (prior slice timed out, #2674)",
                slice.index,
            );

            slice_results.push(SliceResult {
                index: slice.index,
                result: super::VerificationResult::Unknown(super::UnknownReason::Timeout),
            });
            continue;
        }

        // Skip remaining slices after Incomplete for multi-slice functions
        // (#2674): when a prior slice returned Unknown(Incomplete) or
        // Unknown(QuantifierRoundLimit), subsequent slices sharing the same
        // quantified axiom context will hit the same E-matching limitation.
        // Skipping saves significant wall-clock time (up to solver_timeout
        // per skipped slice) without affecting correctness — the function
        // will already report Unknown from the first incomplete slice.
        if saw_incomplete && slices.len() > 1 {
            debug!(
                "  slice[{}]: skipped (prior slice was Incomplete, #2674)",
                slice.index,
            );

            slice_results.push(SliceResult {
                index: slice.index,
                result: super::VerificationResult::Unknown(super::UnknownReason::Incomplete),
            });
            continue;
        }

        if let Some(result) = &literal_false_result {
            debug!(
                "  slice[{}]: skipped (prior literal false obligation)",
                slice.index,
            );

            slice_results.push(SliceResult {
                index: slice.index,
                result: result.clone(),
            });
            continue;
        }

        // Adaptive timeout: reduce per-slice solver timeout based on elapsed
        // wall-clock time. Only active when there are 2+ slices and the
        // function has a solver timeout configured. (#2674)
        if slices.len() > 1 {
            if let (Some(original), Some(budget)) = (original_solver_timeout, function_time_budget)
            {
                let elapsed = solve_start.elapsed();
                if elapsed < budget {
                    let remaining = budget.saturating_sub(elapsed);
                    let remaining_slices = slices.len() - slice.index;
                    // Distribute remaining budget equally across remaining slices,
                    // but never exceed the original solver timeout.
                    let per_slice = if remaining_slices > 0 {
                        remaining / remaining_slices as u32
                    } else {
                        remaining
                    };
                    let adaptive_timeout = per_slice.min(original).max(MIN_SLICE_TIMEOUT);
                    if adaptive_timeout < original {
                        debug!(
                            "  slice[{}]: adaptive timeout {}ms (remaining budget {}ms, \
                                 {} slices left, original {}ms) (#2674)",
                            slice.index,
                            adaptive_timeout.as_millis(),
                            remaining.as_millis(),
                            remaining_slices,
                            original.as_millis(),
                        );

                        encoder.set_timeout(Some(adaptive_timeout));
                    }
                } else {
                    // Budget exhausted — skip remaining slices as timeout.

                    debug!(
                        "  slice[{}]: skipped (function time budget exhausted: \
                             {}ms elapsed, {}ms budget) (#2674)",
                        slice.index,
                        elapsed.as_millis(),
                        budget.as_millis(),
                    );

                    saw_timeout = true;
                    slice_results.push(SliceResult {
                        index: slice.index,
                        result: super::VerificationResult::Unknown(super::UnknownReason::Timeout),
                    });
                    continue;
                }
            }
        }

        encoder.restore_dedup(dedup_baseline.clone());

        // Trivially-true postcondition elimination (#2673): skip the entire
        // obligation slice (including axiom assertion and solver invocation)
        // when the postcondition is a reflexive equality like `u(*a) == u(*a)`.
        //
        // This must be done HERE (before push_scope/solver invocation) rather
        // than in encode_negated_postcondition, because the solver_tail's base
        // recheck can encounter triggerless quantifier axioms from logic
        // function definitions even when the negated postcondition is `false`.
        // Skipping the entire slice avoids both the axiom encoding and the
        // solver invocation that would trigger quantifier-unhandled.
        if !proof_assert_mode
            && options.structural_verified_shortcuts
            && requirement_entails_postcondition(obligation_requires, slice.ensure.as_ref())
        {
            debug!(
                "  slice[{}]: postcondition already present in requirements, skipping",
                slice.index,
            );

            slice_results.push(SliceResult {
                index: slice.index,
                result: super::VerificationResult::Verified(None),
            });
            continue;
        }

        if !proof_assert_mode
            && options.structural_verified_shortcuts
            && super::is_trivially_true_postcondition_under_requires(
                slice.ensure.as_ref(),
                obligation_requires,
            )
        {
            debug!(
                "  slice[{}]: trivially-true postcondition under requirements, skipping (#2673)",
                slice.index,
            );

            slice_results.push(SliceResult {
                index: slice.index,
                result: super::VerificationResult::Verified(None),
            });
            continue;
        }

        if matches!(slice.ensure.as_ref(), PureExpr::Bool(false))
            && options
                .literal_false_base_recheck
                .or(options.fresh_base_recheck)
                .is_some()
        {
            debug!(
                "  slice[{}]: literal false obligation, classifying against fresh base state",
                slice.index,
            );

            let result = literal_false_after_verified_slice_result(
                options
                    .literal_false_base_recheck
                    .or(options.fresh_base_recheck),
            );
            literal_false_result = Some(result.clone());
            slice_results.push(SliceResult {
                index: slice.index,
                result,
            });
            continue;
        }

        if let Some(result) = unconstrained_closure_capture_final_equality_result(
            slice.ensure.as_ref(),
            obligation_requires,
            return_expr,
            closure_captures,
            options
                .literal_false_base_recheck
                .or(options.fresh_base_recheck),
        ) {
            if matches!(result, super::VerificationResult::Verified(_))
                && (!options.structural_verified_shortcuts || proof_assert_mode)
            {
                debug!(
                    "  slice[{}]: structural closure-capture verified shortcut disabled",
                    slice.index
                );
            } else {
                debug!(
                    "  slice[{}]: unconstrained closure-capture final equality classified as {:?}",
                    slice.index, result
                );

                slice_results.push(SliceResult {
                    index: slice.index,
                    result: result.clone(),
                });
                if matches!(&result, super::VerificationResult::Failed(_)) {
                    encoder.ensure_structural_provenance("unconstrained-closure-capture");
                    let provenance = Some(encoder.capture_provenance(solve_start.elapsed()));
                    profile::emit_pipeline_end(
                        options.axiom_debug_label,
                        slices.len(),
                        solve_start.elapsed(),
                        verification_result_tag(&result),
                    );
                    return Ok((
                        super::demote_if_unsound(&demotion_baseline, result),
                        provenance,
                    ));
                }
                continue;
            }
        }

        debug!(
            "  slice[{}]: encoding postcondition {:?}",
            slice.index, slice.ensure
        );

        // TRUST_WP_PROFILE=1 slice_begin event (#2674 Phase 1). No-op when
        // profiling is disabled. Axiom count is a pre-solve snapshot of the
        // ground-pool axiom registry — the same count used by relevance
        // filtering and the per-slice budget heuristic.
        let axiom_count = encoder.ground_pool_axiom_count();
        profile::emit_slice_begin(
            options.axiom_debug_label,
            slice.index,
            slices.len(),
            axiom_count,
            axiom_count,
        );
        let slice_wall_start = Instant::now();

        encoder.push_scope()?;
        let slice_result = slice_verify_fn(
            &mut encoder,
            slice.index,
            slice.ensure.as_ref(),
            &shared_ctx,
        );

        // Restore original solver timeout after each slice so the adaptive
        // reduction does not leak into the next iteration's base computation.
        if slices.len() > 1 {
            encoder.set_timeout(original_solver_timeout);
        }

        match slice_result {
            Ok(ResolveContinuation::Continue(result)) => {
                let (result, certificate) = authorize_proof_assert_slice(
                    slice_ordinal,
                    derivation,
                    &prepared_claim,
                    prepared_claim_hash,
                    &normalized_claim,
                    normalized_claim_hash,
                    result,
                );
                if let Some(certificate) = certificate {
                    proof_assert_certificates.push(certificate);
                }
                if let Err(error) = pop_scope_catching_ay_panic(&mut encoder) {
                    if matches!(&result, super::VerificationResult::Failed(_))
                        && is_incremental_pop_underflow_error(&error)
                    {
                        debug!(
                            "  slice[{}]: ay pop-underflow while leaving outer slice scope \
                             after Failed result; returning conservative failure",
                            slice.index,
                        );
                        profile::emit_slice_end(
                            options.axiom_debug_label,
                            slice.index,
                            slices.len(),
                            slice_wall_start.elapsed(),
                            verification_result_tag(&result),
                            encoder.last_solve_statistics(),
                        );
                        profile::emit_pipeline_end(
                            options.axiom_debug_label,
                            slices.len(),
                            solve_start.elapsed(),
                            verification_result_tag(&result),
                        );
                        return Ok((super::demote_if_unsound(&demotion_baseline, result), None));
                    }
                    return Err(error);
                }

                debug!("  slice[{}]: result = {:?}", slice.index, result);

                // TRUST_WP_PROFILE=1 slice_end event (#2674 Phase 1). Emits
                // elapsed wall-clock for this slice plus any cached solver
                // statistics from the last check_sat() call.
                profile::emit_slice_end(
                    options.axiom_debug_label,
                    slice.index,
                    slices.len(),
                    slice_wall_start.elapsed(),
                    verification_result_tag(&result),
                    encoder.last_solve_statistics(),
                );

                // Detect timeout to enable early termination for subsequent slices.
                if matches!(
                    &result,
                    super::VerificationResult::Unknown(super::UnknownReason::Timeout)
                ) {
                    saw_timeout = true;
                }
                // Detect Incomplete/QuantifierRoundLimit for multi-slice
                // early termination (#2674).
                if matches!(
                    &result,
                    super::VerificationResult::Unknown(
                        super::UnknownReason::Incomplete
                            | super::UnknownReason::QuantifierRoundLimit
                    )
                ) {
                    saw_incomplete = true;
                }
                let failed_result = if matches!(&result, super::VerificationResult::Failed(_)) {
                    Some(result.clone())
                } else {
                    None
                };
                slice_results.push(SliceResult {
                    index: slice.index,
                    result,
                });
                if let Some(failed_result) = failed_result {
                    encoder.ensure_structural_provenance("failed-obligation-shortcut");
                    let provenance = Some(encoder.capture_provenance(solve_start.elapsed()));
                    profile::emit_pipeline_end(
                        options.axiom_debug_label,
                        slices.len(),
                        solve_start.elapsed(),
                        verification_result_tag(&failed_result),
                    );
                    return Ok((
                        super::demote_if_unsound(&demotion_baseline, failed_result),
                        provenance,
                    ));
                }
            }
            Ok(ResolveContinuation::Abort(result)) => {
                let (result, certificate) = authorize_proof_assert_slice(
                    slice_ordinal,
                    derivation,
                    &prepared_claim,
                    prepared_claim_hash,
                    &normalized_claim,
                    normalized_claim_hash,
                    result,
                );
                if let Some(certificate) = certificate {
                    proof_assert_certificates.push(certificate);
                }
                // TRUST_WP_PROFILE=1 slice_end event for hard-timeout aborts.
                profile::emit_slice_end(
                    options.axiom_debug_label,
                    slice.index,
                    slices.len(),
                    slice_wall_start.elapsed(),
                    verification_result_tag(&result),
                    encoder.last_solve_statistics(),
                );

                // Abort(Verified): the slice's goal was proved and the vacuity
                // base recheck hard-timed out, but the fresh base recheck
                // (#2414) positively confirmed a SAT (non-vacuous) base — the
                // proof is genuine (see
                // `prefer_non_vacuous_core_on_fresh_base_recheck`). The live
                // encoder was lost to the abandoned worker thread, so the
                // remaining slices cannot run: record them as Unknown(Timeout)
                // — never Verified — and aggregate. SOUND: no unproven slice
                // is ever promoted (a single rescued slice only yields a
                // Verified aggregate when every other slice already verified),
                // and a genuinely vacuous base cannot reach this arm because
                // the rescue demands a positive SAT witness.
                if matches!(&result, super::VerificationResult::Verified(_)) {
                    slice_results.push(SliceResult {
                        index: slice.index,
                        result,
                    });
                    for skipped in slices.iter().skip(slice_position + 1) {
                        slice_results.push(SliceResult {
                            index: skipped.index,
                            result: super::VerificationResult::Unknown(
                                super::UnknownReason::Timeout,
                            ),
                        });
                    }
                    let result = obligation_slices::aggregate_slice_results(slice_results);
                    let provenance = if matches!(result, super::VerificationResult::Verified(_)) {
                        // Mirror the normal completion path's evidence attach.
                        // The placeholder encoder carries no solver state (its
                        // provenance is structural only), but the accepted
                        // solve evidence for the proven goal was recorded in
                        // the caller's thread-local slot BEFORE the base
                        // recheck ran.
                        encoder.ensure_structural_provenance("base-recheck-abort-rescued-slice");
                        let mut provenance = encoder.capture_provenance(solve_start.elapsed());
                        if proof_assert_mode {
                            install_proof_assert_certificates(
                                &mut provenance,
                                proof_assert_certificates,
                            );
                        } else {
                            install_preferred_verified_solve_diagnostics(&mut provenance, &encoder);
                        }
                        Some(provenance)
                    } else {
                        super::solver_tail::clear_preferred_verified_solve_evidence();
                        None
                    };
                    profile::emit_pipeline_end(
                        options.axiom_debug_label,
                        slices.len(),
                        solve_start.elapsed(),
                        verification_result_tag(&result),
                    );
                    return Ok((
                        super::demote_if_unsound(&demotion_baseline, result),
                        provenance,
                    ));
                }

                // Abort means the live encoder is still owned by the worker
                // thread (see `run_with_hard_timeout`). Return immediately;
                // using the placeholder encoder for more slices, pops, or
                // provenance capture can corrupt solver scope state.
                profile::emit_pipeline_end(
                    options.axiom_debug_label,
                    slices.len(),
                    solve_start.elapsed(),
                    "AbortEarly",
                );
                return Ok((super::demote_if_unsound(&demotion_baseline, result), None));
            }
            Err(error) => {
                pop_scope_catching_ay_panic(&mut encoder)?;
                return Err(error);
            }
        }
    }

    // Capture provenance from the encoder after all slices complete (#2729).
    encoder.ensure_structural_provenance("completed-obligation-slices");
    let result = obligation_slices::aggregate_slice_results(slice_results);
    let mut provenance = encoder.capture_provenance(solve_start.elapsed());
    if matches!(result, super::VerificationResult::Verified(_)) {
        if proof_assert_mode {
            install_proof_assert_certificates(&mut provenance, proof_assert_certificates);
        } else {
            install_preferred_verified_solve_diagnostics(&mut provenance, &encoder);
        }
    } else {
        super::solver_tail::clear_preferred_verified_solve_evidence();
    }
    let provenance = Some(provenance);
    // TRUST_WP_PROFILE=1 pipeline_end event — aggregate wall-clock across all
    // slices plus the aggregated outcome tag. (#2674 Phase 1)
    profile::emit_pipeline_end(
        options.axiom_debug_label,
        slices.len(),
        solve_start.elapsed(),
        verification_result_tag(&result),
    );
    Ok((
        super::demote_if_unsound(&demotion_baseline, result),
        provenance,
    ))
}

fn proof_assert_claim_identity(ordinal: u64, ensure: &PureExpr) -> (String, [u8; 32]) {
    // Slicing and transparent-logic expansion have already run, so this is the
    // exact normalized claim handed to the slice verifier.
    let normalized_claim = format!("{ensure:#?}");
    let mut hasher = Sha256::new();
    hasher.update(b"trust-wp.proof-assert-slice-claim.v1\0");
    hasher.update(ordinal.to_be_bytes());
    hasher.update(normalized_claim.as_bytes());
    (normalized_claim, hasher.finalize().into())
}

fn proof_assert_prepared_claim_hash(ordinal: u64, prepared_claim: &str) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"trust-wp.proof-assert-prepared-claim.v1\0");
    hasher.update(ordinal.to_be_bytes());
    hasher.update(prepared_claim.as_bytes());
    hasher.finalize().into()
}

fn proof_assert_native_problem_hash(native_problem_json: &str) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"trust-wp.proof-assert-native-problem.v1\0");
    hasher.update(native_problem_json.as_bytes());
    hasher.finalize().into()
}

fn proof_assert_slice_count_mismatch_result(
    prepared_count: usize,
    normalized_count: usize,
) -> Option<VerificationResult> {
    (prepared_count != normalized_count).then(|| {
        VerificationResult::Unknown(super::UnknownReason::SolverMessage(format!(
            "proof_assert prepared/normalized obligation slice count mismatch: \
             prepared={prepared_count}, normalized={normalized_count}",
        )))
    })
}

fn authorize_proof_assert_slice(
    ordinal: u64,
    derivation: ProofAssertSliceDerivation,
    prepared_claim: &str,
    prepared_claim_hash: [u8; 32],
    normalized_claim: &str,
    normalized_claim_hash: [u8; 32],
    result: VerificationResult,
) -> (VerificationResult, Option<ProofAssertSliceCertificate>) {
    if !super::solver_tail::in_proof_assert_mode()
        || !matches!(result, VerificationResult::Verified(_))
    {
        return (result, None);
    }

    let diagnostics = super::solver_tail::take_preferred_verified_solve_diagnostics();
    let certificate = diagnostics.and_then(|diagnostics| {
        let statistics = diagnostics.statistics?;
        let native_problem_json = diagnostics.native_problem_json?;
        let problem_hash = diagnostics.problem_hash?;
        let expected_identity = super::solver_tail::ProofAssertSliceIdentity::new(
            ordinal,
            prepared_claim_hash,
            normalized_claim_hash,
        );
        if diagnostics.claim_identity != Some(expected_identity)
            || problem_hash != proof_assert_native_problem_hash(&native_problem_json)
            || !crate::encoder::ay_api::solve_snapshots_have_complete_unsat_proof(
                &diagnostics.evidence,
                &statistics,
            )
        {
            return None;
        }
        Some(ProofAssertSliceCertificate::new(
            ordinal,
            derivation,
            prepared_claim.to_string(),
            prepared_claim_hash,
            normalized_claim.to_string(),
            normalized_claim_hash,
            native_problem_json,
            problem_hash,
            diagnostics.evidence,
            statistics,
        ))
    });

    match certificate {
        Some(certificate) => (result, Some(certificate)),
        None => (
            VerificationResult::Unknown(super::UnknownReason::SolverMessage(format!(
                "{PROOF_ASSERT_SLICE_AUTHORITY_MESSAGE}: ordinal {ordinal}"
            ))),
            None,
        ),
    }
}

fn proof_assert_certificate_set_hash(certificates: &[ProofAssertSliceCertificate]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"trust-wp.proof-assert-certificate-set.v1\0");
    hasher.update(
        u64::try_from(certificates.len())
            .unwrap_or(u64::MAX)
            .to_be_bytes(),
    );
    for certificate in certificates {
        hasher.update(certificate.ordinal.to_be_bytes());
        hasher.update(certificate.derivation.certificate_hash_tag());
        hasher.update(certificate.prepared_claim_hash);
        hasher.update(certificate.normalized_claim_hash);
        hasher.update(certificate.problem_hash);
    }
    hasher.finalize().into()
}

/// Install the retained authoritative solve envelope on a `Verified` outcome's
/// provenance, evidence and statistics TOGETHER.
///
/// `encoder.capture_provenance()` fills `solver_statistics` from whatever the
/// encoder cached last. On the lanes that prove an obligation on a *different*
/// solver than the one this provenance is captured from — the empty-obligation
/// literal-`false` lane (its outer encoder never solves, so
/// `ensure_structural_provenance` installs a `SolveStatisticsSnapshot::default()`
/// placeholder) and the base-recheck-rescued lanes (whose last cached statistics
/// belong to the base recheck, not to the proof) — those statistics do not
/// describe the proof the retained evidence attests to.
///
/// The driver's mandatory proof-authority boundary judges the PAIR, so it must
/// be handed one solve's evidence next to that same solve's statistics.
/// Splitting them fails in both directions: a placeholder's `proof_complete:
/// false` refuses a genuine strictly-checked proof (the observable symptom), and
/// statistics carried over from an unrelated proved query would vouch for
/// evidence they never covered. `record_preferred_verified_solve_evidence` reads
/// both halves from one encoder at one instant, so taking them together is the
/// only faithful install.
///
/// Fails closed: retained evidence with no statistics of its own is dropped
/// rather than re-paired with the encoder's, leaving the structural provenance
/// (and therefore the evidence gap) in place.
fn install_preferred_verified_solve_diagnostics(
    provenance: &mut super::VerificationProvenance,
    encoder: &AYEncoder,
) {
    let Some(diagnostics) =
        super::solver_tail::take_preferred_verified_solve_diagnostics_for_encoder(encoder)
    else {
        return;
    };
    let Some(statistics) = diagnostics.statistics else {
        return;
    };
    provenance.solve_evidence = Some(diagnostics.evidence);
    provenance.solver_statistics = Some(statistics);
}

fn install_proof_assert_certificates(
    provenance: &mut super::VerificationProvenance,
    certificates: Vec<ProofAssertSliceCertificate>,
) {
    let Some(last) = certificates.last() else {
        return;
    };
    provenance.vc_hash = proof_assert_certificate_set_hash(&certificates);
    provenance.solve_evidence = Some(last.solve_evidence.clone());
    provenance.solver_statistics = Some(last.solver_statistics.clone());
    provenance.native_replay_json = Some(last.native_problem_json.clone());
    provenance.proof_assert_slice_certificates = certificates;
}

fn is_incremental_pop_underflow_error(error: &EncodingError) -> bool {
    error
        .to_string()
        .contains("IncrementalTheoryState::pop() underflow")
}

fn pop_scope_catching_ay_panic(encoder: &mut AYEncoder) -> Result<(), EncodingError> {
    super::catch_ay_panics_tightened(AssertUnwindSafe(|| encoder.pop_scope()), |reason| {
        Err(EncodingError::solver_error(reason))
    })
}

/// Render a short tag describing a [`VerificationResult`] for profile output.
///
/// Kept intentionally compact (single token, no spaces) so downstream grep /
/// awk filters can match on `outcome=...`. Detailed diagnostic strings live
/// in tracing output; profile lines stay machine-readable.
fn verification_result_tag(result: &VerificationResult) -> &'static str {
    match result {
        VerificationResult::Verified(_) => "Verified",
        VerificationResult::Failed(_) => "Failed",
        VerificationResult::Assumed(_) => "Assumed",
        VerificationResult::Unknown(reason) => match reason {
            super::UnknownReason::Timeout => "Unknown_Timeout",
            super::UnknownReason::ResourceOut => "Unknown_ResourceOut",
            super::UnknownReason::Incomplete => "Unknown_Incomplete",
            super::UnknownReason::Quantifiers
            | super::UnknownReason::QuantifierRoundLimit
            | super::UnknownReason::QuantifierDeferred
            | super::UnknownReason::QuantifierUnhandled
            | super::UnknownReason::QuantifierCegqiIncomplete
            | super::UnknownReason::QuantifierEmatchingExistsIncomplete => "Unknown_Quantifier",
            super::UnknownReason::SatModel => "Unknown_SatModel",
            super::UnknownReason::MemoryOut => "Unknown_MemoryOut",
            super::UnknownReason::Interrupted => "Unknown_Interrupted",
            super::UnknownReason::Unsupported => "Unknown_Unsupported",
            super::UnknownReason::UnsupportedArithmetic => "Unknown_UnsupportedArithmetic",
            super::UnknownReason::UnsupportedMixedCollection => {
                "Unknown_UnsupportedMixedCollection"
            }
            super::UnknownReason::InternalError => "Unknown_InternalError",
            super::UnknownReason::SelfCheckRejected => "Unknown_SelfCheckRejected",
            super::UnknownReason::ProofTrusted => "Unknown_ProofTrusted",
            super::UnknownReason::Demoted(_) => "Unknown_Demoted",
            super::UnknownReason::SolverPanic(_) => "Unknown_SolverPanic",
            super::UnknownReason::SolverMessage(_) => "Unknown_SolverMessage",
            super::UnknownReason::Unspecified => "Unknown_Unspecified",
        },
    }
}

fn literal_false_after_verified_slice_result(
    fresh_base_recheck: Option<&FreshBaseRecheckFn<'_>>,
) -> VerificationResult {
    let Some(fresh_base_recheck) = fresh_base_recheck else {
        return VerificationResult::Unknown(super::UnknownReason::SolverMessage(
            LITERAL_FALSE_CLASSIFICATION_MESSAGE.to_string(),
        ));
    };

    match fresh_base_recheck() {
        // The fresh-base recheck reports Verified when the base context is
        // satisfiable. Since this slice's postcondition is literally false,
        // a satisfiable base is a real counterexample, not a proof.
        Ok(VerificationResult::Verified(_)) => {
            VerificationResult::Failed(super::Counterexample::empty())
        }
        Ok(VerificationResult::Unknown(reason)) if is_solver_limited_unknown(&reason) => {
            // A literal `false` postcondition can only verify if the base is
            // contradictory. If a fresh base probe cannot decide only because
            // of solver resource limits, report the conservative failure
            // instead of letting a quantified/timeout tail hide the concrete
            // false obligation.
            VerificationResult::Failed(super::Counterexample::empty())
        }
        Ok(VerificationResult::Unknown(reason)) => VerificationResult::Unknown(reason),
        Ok(VerificationResult::Failed(counterexample)) => {
            VerificationResult::Failed(counterexample)
        }
        Ok(VerificationResult::Assumed(reason)) => {
            VerificationResult::Unknown(super::UnknownReason::SolverMessage(format!(
                "{LITERAL_FALSE_CLASSIFICATION_MESSAGE}; fresh base recheck was assumed: {reason}"
            )))
        }
        Err(error) => VerificationResult::Unknown(super::UnknownReason::SolverMessage(format!(
            "{LITERAL_FALSE_CLASSIFICATION_MESSAGE}; fresh base recheck failed: {error}"
        ))),
    }
}

fn unconstrained_closure_capture_final_equality_result(
    ensure: &PureExpr,
    requires: &[PureExpr],
    return_expr: Option<&PureExpr>,
    closure_captures: Option<&[super::ClosureCaptureInfo]>,
    fresh_base_recheck: Option<&FreshBaseRecheckFn<'_>>,
) -> Option<VerificationResult> {
    let target_var = closure_capture_final_equality_var(ensure, closure_captures)?;
    if return_expr.is_some_and(|expr| expr_mentions_var(expr, target_var)) {
        return None;
    }
    if requires
        .iter()
        .any(|expr| expr_mentions_var(expr, target_var) || expr_has_postcondition_method(expr))
    {
        return None;
    }

    Some(failed_after_satisfiable_or_limited_base_result(
        fresh_base_recheck,
        "unconstrained closure-capture final equality",
    ))
}

fn closure_capture_final_equality_var<'a>(
    ensure: &'a PureExpr,
    closure_captures: Option<&[super::ClosureCaptureInfo]>,
) -> Option<&'a str> {
    let closure_captures = closure_captures?;
    let PureExpr::BinOp(left, BinOp::Eq, right) = ensure else {
        return None;
    };
    let (candidate, other) =
        final_var_equality_side(left, right).or_else(|| final_var_equality_side(right, left))?;
    if expr_mentions_var(other, candidate) {
        return None;
    }
    closure_captures
        .iter()
        .any(|info| {
            info.captures()
                .iter()
                .any(|field| capture_final_name(field.name(), 1) == candidate)
        })
        .then_some(candidate)
}

fn final_var_equality_side<'a>(
    candidate: &'a PureExpr,
    other: &'a PureExpr,
) -> Option<(&'a str, &'a PureExpr)> {
    let PureExpr::Var(name, _) = candidate else {
        return None;
    };
    name.ends_with("_final").then_some((name.as_str(), other))
}

fn capture_final_name(base: &str, depth: usize) -> String {
    (0..depth).fold(base.to_string(), |name, _| format!("{name}_final"))
}

fn expr_mentions_var(expr: &PureExpr, target: &str) -> bool {
    expr.any_recursive(|node| matches!(node, PureExpr::Var(name, _) if name == target))
}

fn expr_has_postcondition_method(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| {
        matches!(
            node,
            PureExpr::MethodCall { method, .. }
                if matches!(
                    method.as_str(),
                    "postcondition" | "postcondition_mut" | "postcondition_once"
                )
        )
    })
}

fn failed_after_satisfiable_or_limited_base_result(
    fresh_base_recheck: Option<&FreshBaseRecheckFn<'_>>,
    label: &str,
) -> VerificationResult {
    let Some(fresh_base_recheck) = fresh_base_recheck else {
        return VerificationResult::Unknown(super::UnknownReason::SolverMessage(format!(
            "{label} could not be classified from fresh base state"
        )));
    };

    match fresh_base_recheck() {
        Ok(VerificationResult::Verified(_)) => {
            VerificationResult::Failed(super::Counterexample::empty())
        }
        Ok(VerificationResult::Unknown(reason)) if is_solver_limited_unknown(&reason) => {
            VerificationResult::Failed(super::Counterexample::empty())
        }
        Ok(VerificationResult::Unknown(reason)) => VerificationResult::Unknown(reason),
        Ok(VerificationResult::Failed(counterexample)) => {
            VerificationResult::Failed(counterexample)
        }
        Ok(VerificationResult::Assumed(reason)) => {
            VerificationResult::Unknown(super::UnknownReason::SolverMessage(format!(
                "{label} could not be classified; fresh base recheck was assumed: {reason}"
            )))
        }
        Err(error) => VerificationResult::Unknown(super::UnknownReason::SolverMessage(format!(
            "{label} could not be classified; fresh base recheck failed: {error}"
        ))),
    }
}

pub(super) fn requirement_entails_postcondition(requires: &[PureExpr], ensure: &PureExpr) -> bool {
    requires
        .iter()
        .any(|require| expr_entails_postcondition(require, ensure))
}

fn expr_entails_postcondition(require: &PureExpr, ensure: &PureExpr) -> bool {
    if expr_equal_mod_binders_and_triggers(require, ensure) {
        return true;
    }

    let (
        PureExpr::BinOp(req_lhs, BinOp::Eq, req_rhs),
        PureExpr::BinOp(ens_lhs, BinOp::Eq, ens_rhs),
    ) = (require, ensure)
    else {
        return false;
    };

    (expr_equal_mod_binders_and_triggers(req_lhs, ens_lhs)
        && expr_equal_mod_binders_and_triggers(req_rhs, ens_rhs))
        || (expr_equal_mod_binders_and_triggers(req_lhs, ens_rhs)
            && expr_equal_mod_binders_and_triggers(req_rhs, ens_lhs))
}

fn expr_equal_mod_binders_and_triggers(left: &PureExpr, right: &PureExpr) -> bool {
    let mut binders = Vec::new();
    expr_equal_mod_binders_inner(left, right, &mut binders)
}

fn expr_equal_mod_binders_inner<'a>(
    left: &'a PureExpr,
    right: &'a PureExpr,
    binders: &mut Vec<(&'a str, &'a str)>,
) -> bool {
    match (left, right) {
        (PureExpr::Var(left_name, _), PureExpr::Var(right_name, _)) => {
            bound_or_free_var_names_match(left_name, right_name, binders)
        }
        (PureExpr::Bool(left), PureExpr::Bool(right)) => left == right,
        (PureExpr::Int(left), PureExpr::Int(right)) => left == right,
        (PureExpr::Float(left), PureExpr::Float(right)) => left == right,
        (
            PureExpr::BinOp(left_lhs, left_op, left_rhs),
            PureExpr::BinOp(right_lhs, right_op, right_rhs),
        ) => {
            left_op == right_op
                && expr_equal_mod_binders_inner(left_lhs, right_lhs, binders)
                && expr_equal_mod_binders_inner(left_rhs, right_rhs, binders)
        }
        (PureExpr::UnOp(left_op, left_inner), PureExpr::UnOp(right_op, right_inner)) => {
            left_op == right_op && expr_equal_mod_binders_inner(left_inner, right_inner, binders)
        }
        (PureExpr::Old(left_inner), PureExpr::Old(right_inner))
        | (PureExpr::Deref(left_inner), PureExpr::Deref(right_inner))
        | (PureExpr::Final(left_inner), PureExpr::Final(right_inner))
        | (PureExpr::View(left_inner), PureExpr::View(right_inner)) => {
            expr_equal_mod_binders_inner(left_inner, right_inner, binders)
        }
        (
            PureExpr::Ite(left_cond, left_then, left_else),
            PureExpr::Ite(right_cond, right_then, right_else),
        ) => {
            expr_equal_mod_binders_inner(left_cond, right_cond, binders)
                && expr_equal_mod_binders_inner(left_then, right_then, binders)
                && expr_equal_mod_binders_inner(left_else, right_else, binders)
        }
        (
            PureExpr::MethodCall {
                receiver: left_receiver,
                method: left_method,
                args: left_args,
            },
            PureExpr::MethodCall {
                receiver: right_receiver,
                method: right_method,
                args: right_args,
            },
        ) => {
            left_method == right_method
                && expr_equal_mod_binders_inner(left_receiver, right_receiver, binders)
                && expr_lists_equal_mod_binders(left_args, right_args, binders)
        }
        (
            PureExpr::LogicFnCall {
                name: left_name,
                args: left_args,
            },
            PureExpr::LogicFnCall {
                name: right_name,
                args: right_args,
            },
        ) => {
            left_name == right_name && expr_lists_equal_mod_binders(left_args, right_args, binders)
        }
        (
            PureExpr::Forall {
                var: left_var,
                body: left_body,
                ..
            },
            PureExpr::Forall {
                var: right_var,
                body: right_body,
                ..
            },
        )
        | (
            PureExpr::Exists {
                var: left_var,
                body: left_body,
                ..
            },
            PureExpr::Exists {
                var: right_var,
                body: right_body,
                ..
            },
        ) => {
            binders.push((left_var, right_var));
            let equal = expr_equal_mod_binders_inner(left_body, right_body, binders);
            binders.pop();
            equal
        }
        _ => crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(left, right),
    }
}

fn expr_lists_equal_mod_binders<'a>(
    left: &'a [PureExpr],
    right: &'a [PureExpr],
    binders: &mut Vec<(&'a str, &'a str)>,
) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| expr_equal_mod_binders_inner(left, right, binders))
}

fn bound_or_free_var_names_match(left: &str, right: &str, binders: &[(&str, &str)]) -> bool {
    let left_bound = binders
        .iter()
        .rev()
        .find_map(|(left_bound, right_bound)| (*left_bound == left).then_some(*right_bound));
    if let Some(expected_right) = left_bound {
        return expected_right == right;
    }

    let right_is_bound = binders
        .iter()
        .rev()
        .any(|(_, right_bound)| *right_bound == right);
    !right_is_bound && left == right
}

fn is_solver_limited_unknown(reason: &super::UnknownReason) -> bool {
    matches!(
        reason,
        super::UnknownReason::Timeout
            | super::UnknownReason::ResourceOut
            | super::UnknownReason::MemoryOut
            | super::UnknownReason::Interrupted
            | super::UnknownReason::Incomplete
            | super::UnknownReason::Quantifiers
            | super::UnknownReason::QuantifierRoundLimit
            | super::UnknownReason::QuantifierDeferred
            | super::UnknownReason::QuantifierUnhandled
            | super::UnknownReason::QuantifierCegqiIncomplete
            | super::UnknownReason::QuantifierEmatchingExistsIncomplete
    )
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::{BinOp, PureExpr};

    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn int(value: i64) -> PureExpr {
        PureExpr::Int(value)
    }

    fn method(receiver: PureExpr, name: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: name.to_string(),
            args,
        }
    }

    fn eq(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
    }

    fn le(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Le, Arc::new(rhs))
    }

    fn lt(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Lt, Arc::new(rhs))
    }

    fn and(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs))
    }

    fn implies(lhs: PureExpr, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), BinOp::Implies, Arc::new(rhs))
    }

    #[test]
    fn literal_false_solver_limited_base_is_conservative_failure() {
        let recheck: Box<FreshBaseRecheckFn<'_>> = Box::new(|| {
            Ok(VerificationResult::Unknown(
                super::super::UnknownReason::QuantifierUnhandled,
            ))
        });

        let result = literal_false_after_verified_slice_result(Some(recheck.as_ref()));

        assert!(
            matches!(result, VerificationResult::Failed(_)),
            "quantifier-limited base probe should not mask literal false: {result:?}"
        );
    }

    #[test]
    fn literal_false_timeout_base_is_conservative_failure() {
        let recheck: Box<FreshBaseRecheckFn<'_>> = Box::new(|| {
            Ok(VerificationResult::Unknown(
                super::super::UnknownReason::Timeout,
            ))
        });

        let result = literal_false_after_verified_slice_result(Some(recheck.as_ref()));

        assert!(
            matches!(result, VerificationResult::Failed(_)),
            "timeout base probe should not mask literal false: {result:?}"
        );
    }

    #[test]
    fn requirement_entails_alpha_equivalent_triggered_universal_postcondition() {
        let final_v = PureExpr::Final(Arc::new(var("v")));
        let final_len = method(PureExpr::View(Arc::new(final_v.clone())), "len", vec![]);
        let req_j = var("j");
        let ensure_i = var("i");

        let requirement = PureExpr::Forall {
            var: "j".to_string(),
            var_sort: None,
            body: Arc::new(implies(
                and(
                    le(int(0), req_j.clone()),
                    lt(req_j.clone(), final_len.clone()),
                ),
                eq(
                    method(final_v.clone(), "index_logic", vec![req_j.clone()]),
                    int(0),
                ),
            )),
            triggers: vec![vec![method(final_v.clone(), "index_logic", vec![req_j])]],
        };
        let postcondition = PureExpr::Forall {
            var: "i".to_string(),
            var_sort: None,
            body: Arc::new(implies(
                and(
                    le(int(0), ensure_i.clone()),
                    lt(ensure_i.clone(), final_len),
                ),
                eq(method(final_v, "index_logic", vec![ensure_i]), int(0)),
            )),
            triggers: vec![],
        };

        assert!(requirement_entails_postcondition(
            &[requirement],
            &postcondition
        ));
    }

    #[test]
    fn requirement_entails_symmetric_equality_postcondition() {
        let requirement = eq(
            method(var("v"), "len", vec![]),
            method(var("w"), "len", vec![]),
        );
        let postcondition = eq(
            method(var("w"), "len", vec![]),
            method(var("v"), "len", vec![]),
        );

        assert!(requirement_entails_postcondition(
            &[requirement],
            &postcondition
        ));
    }
}
