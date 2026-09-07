// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Verification - Functions for verifying separation logic contracts.
//!
//! This module provides the main verification entry points for checking
//! function contracts and loop invariants.
//!
//! # Key Types
//!
//! - [`VerificationResult`]: Result of a verification attempt (Verified, Failed, Unknown)
//! - [`Counterexample`]: Witness values when verification fails
//! - [`CounterexampleValue`]: Individual value in a counterexample
//! - [`CounterexampleType`]: Type of counterexample (integer, boolean, etc.)
//! - [`VarOrigin`]: Tracks where counterexample variables originated
//! - [`PostconditionInfo`]: Information about violated postconditions
//! - [`LoopVerificationResult`]: Detailed result for loop invariant verification
//!
//! # Key Functions
//!
//! - [`verify_function_with_modes`]: Verifies a function's postcondition holds given preconditions
//! - [`verify_mut_borrow_function_with_modes`]: Verifies functions with mutable borrow patterns
//! - [`verify_loop_invariant`]: Verifies loop invariant preservation and termination
//! - [`verify_preservation`]: Verifies loop preservation without initialization
//!
//! # See Also
//!
//! - [`crate::encoder`]: SMT term encoding

mod eager_instantiation;
mod expr_subst;
pub(crate) mod function;
mod hard_timeout;
mod loops;
pub(crate) mod mut_borrow;
pub(crate) mod obligation_slices;
mod panic_boundary;
pub(crate) mod pipeline;
mod postcondition;
mod process_isolation;
// The wire frames only cross the fork(2) pipe, and fork does not exist on
// Windows — see process_isolation for the non-unix inline path.
#[cfg(unix)]
mod process_wire;
pub(crate) mod profile;
mod result_inference;
#[cfg(test)]
mod result_inference_name_tests;
mod setup;
pub(crate) mod shared_constraints;
mod solver_tail;
#[cfg(test)]
mod solver_tail_tests;
mod types;

use ay_dpll::api::Sort;
pub(crate) use eager_instantiation::assert_eager_negated_existential_instantiations;
#[cfg(test)]
pub(crate) use eager_instantiation::{
    collect_ground_postcondition_mut_calls, collect_ground_resolve_calls, expr_mentions_bound_var,
    exprs_structurally_equal, flatten_nested_existentials, normalize_deref_final, try_match_expr,
    try_match_method_call, try_match_resolve_call, MethodCallPattern,
};
pub(crate) use expr_subst::substitute_vars_in_expr;
// Re-export public verification functions
pub use function::{verify_function_with_modes, verify_function_with_modes_outcome};
#[cfg(test)]
pub(crate) use hard_timeout::force_hard_timeout_for_test;
#[cfg(test)]
pub(crate) use hard_timeout::run_with_hard_timeout;
pub(crate) use hard_timeout::ResolveContinuation;
#[cfg(test)]
pub(crate) use loops::verify_loop_invariant_positional;
// Test-only re-exports: internal API, not part of public surface.
#[cfg(test)]
pub(crate) use loops::verify_preservation;
pub use loops::{
    verify_loop_invariant, verify_loop_invariant_outcome, BodyEffects, LoopEncoderConfig,
    LoopVerificationContext,
};
pub use mut_borrow::{
    verify_mut_borrow_function_with_modes, verify_mut_borrow_function_with_modes_outcome,
};
pub use obligation_slices::{
    proof_assert_obligation_slice_claims, proof_assert_obligation_slice_count,
    proof_assert_obligation_slice_derivations,
};
pub(crate) use panic_boundary::{catch_ay_panics_tightened, catch_ay_sort_panics_outcome};
#[cfg(test)]
pub(crate) use panic_boundary::{catch_ay_sort_panics, catch_ay_sort_panics_loop, is_ay_panic};
#[cfg(test)]
pub(crate) use postcondition::negate_existential_postcondition;
#[cfg(test)]
pub(crate) use postcondition::{classify_negated_postcondition_route, NegatedPostconditionRoute};
pub(crate) use postcondition::{
    encode_and_assert_negated_postconditions, encode_negated_postcondition,
    is_trivially_true_postcondition, is_trivially_true_postcondition_under_requires,
    logic_fn_equality_has_visible_body_candidate, logic_fn_equality_is_finite_enumerable_candidate,
    logic_fn_equality_is_projected_index_candidate, logic_fn_equality_matches_body,
    postcondition_contains_visible_recursive_logic_call, postcondition_contradicts_requirements,
    postcondition_false_via_logic_bodies, postcondition_true_via_logic_bodies,
    recursive_logic_fn_equality_matches_evaluation,
    recursive_postcondition_matches_evaluation_under_requires,
    requirements_imply_postcondition_via_logic_bodies,
    result_equals_return_expr_via_logic_body_with_requires,
    result_match_over_option_ite_is_directly_invalid, result_postcondition_contradicts_return_expr,
    result_postcondition_contradicts_return_expr_via_logic_bodies,
    result_postcondition_matches_return_expr,
    result_postcondition_matches_return_expr_via_logic_bodies,
};
pub(crate) use result_inference::{
    detect_body_constructor_name, expr_contains_result_var, option_datatype_from_constructor_expr,
    result_collection_sort_from_postcondition_with_context,
    result_is_bool_by_postcondition_with_context, result_match_datatype_from_postcondition,
};
#[cfg(test)]
pub(crate) use result_inference::{
    expr_match_datatype_for_result, expr_requires_result_bool,
    result_collection_sort_from_postcondition, result_is_bool_by_postcondition,
};
#[cfg(test)]
pub(crate) use shared_constraints::flatten_ghost_implications;
#[cfg(test)]
use solver_tail::resolve_sat_result;
#[cfg(test)]
pub(crate) use solver_tail::retry_check_sat_on_timeout;
#[cfg(test)]
use solver_tail::retry_disabled;
// Compatibility re-exports: solver helpers moved to solver_tail.rs (#1576 Slice B).
// These preserve existing import paths for loop modules and tests.
pub(crate) use solver_tail::unknown_result_from_encoder;
/// Re-export the proof_assert-mode guard for the driver. (#transpose)
pub use solver_tail::ProofAssertModeGuard;
pub(crate) use solver_tail::{active_proof_assert_slice_identity, in_proof_assert_mode};
use solver_tail::{
    assert_standard_axioms, axiom_free_solve_with_sat, try_axiom_free_solve, AxiomFreeOutcome,
};
use tracing::debug;
use trust_wp_core::{formula::PureExpr, TrackLevel};
pub(crate) use types::ClosureCaptureInfo;
// Re-export public types
pub use types::{
    Counterexample, CounterexampleType, CounterexampleValue, LoopVerificationOutcome,
    LoopVerificationResult, MutBorrowRequest, PostconditionInfo, ProofCertificateSummary,
    SolveEvidenceSnapshot, SolveLimitKindSnapshot, SolveResourceSnapshot, SolveStatisticsSnapshot,
    SolveVerificationLevelSnapshot, SolveVerificationSnapshot, StrictProofReplayObservation,
    UnknownReason, VarOrigin, VerificationOutcome, VerificationProvenance, VerificationRequest,
    VerificationResult,
};

/// Extract the strict proof authority produced by an AY solver's most recent
/// UNSAT result.
///
/// Keeping this conversion in one place prevents isolated proof lanes (native
/// BV, fresh literal contradictions, and exact native replays) from replacing
/// the checked artifact with synthetic `Verified(None)` metadata.
pub(crate) fn extract_proof_summary(
    solver: &ay_dpll::api::Solver,
) -> Option<ProofCertificateSummary> {
    solver
        .export_last_unsat_artifact()
        .map(proof_summary_from_artifact)
}

pub(crate) fn proof_summary_from_artifact(
    artifact: ay_dpll::api::UnsatProofArtifact,
) -> ProofCertificateSummary {
    ProofCertificateSummary {
        strict_verified: matches!(
            artifact.strict_verdict,
            ay_dpll::api::StrictProofVerdict::Verified(_)
        ),
        restricted_rule_subset: artifact.restricted_rule_subset,
        trust_count: artifact.quality.trust_count,
        trust_fallback_count: artifact.quality.trust_fallback_count,
        hole_count: artifact.quality.hole_count,
        theory_lemma_count: artifact.quality.theory_lemma_count,
        resolution_count: artifact.quality.resolution_count,
        farkas_certificate_count: u32::try_from(artifact.farkas_certificates.len())
            .unwrap_or(u32::MAX),
        lrat_present: artifact.lrat_certificate.is_some(),
        alethe_text: Some(artifact.alethe),
    }
}

use crate::{
    encoder::{
        sort_context::{
            var_collection::{collect_variable_usage_as_formula, determine_sort},
            DerivedKind,
        },
        unsoundness, AYEncoder,
    },
    error::EncodingError,
    shared_types::CaptureKind,
};

/// Build a verified outcome for trust-wp-side structural checks that do not need
/// a ay SAT/UNSAT query.
pub fn structural_verified_outcome() -> VerificationOutcome {
    VerificationOutcome::new(
        VerificationResult::Verified(None),
        Some(
            VerificationProvenance::default()
                .with_solve_evidence(Some(structural_solve_evidence())),
        ),
    )
}

fn structural_solve_evidence() -> SolveEvidenceSnapshot {
    SolveEvidenceSnapshot {
        result: "trust-wp-structural-provenance".to_string(),
        model_validated: false,
        accepted_for_consumer: false,
        consumer_rejection: Some(
            "structural provenance does not include verified solver evidence".to_string(),
        ),
        verification: SolveVerificationSnapshot::default(),
        verification_level: SolveVerificationLevelSnapshot::Unknown,
        resource_usage: SolveResourceSnapshot::default(),
    }
}

/// Build a provisional outcome for a closed structural-induction precheck.
///
/// The recognizer may establish the mathematical argument, but it does not yet
/// emit an AY-checkable certificate. Keep the result explicitly outside proof
/// authority; the mandatory public boundary will downgrade it until the
/// structural derivation has a replayable artifact.
pub(crate) fn structural_induction_verified_outcome() -> VerificationOutcome {
    structural_verified_outcome()
}

// --- Unsoundness demotion (#2106) ---

/// Demote a `Verified` result to `Unknown` if any demoting unsoundness
/// categories fired during this verification.
///
/// Takes a snapshot before verification; after verification completes, computes
/// the delta. If any HIGH or MEDIUM risk categories incremented, the `Verified`
/// result is demoted to `Unknown` with a diagnostic message listing the
/// categories that fired. Non-`Verified` results pass through unchanged.
///
/// This is the safety net that prevents encoding approximations (sort fallback,
/// panic recovery, dropped assumptions, etc.) from producing false proofs.
///
/// Fail-closed counterexample hygiene (arc_and_rc sort-plan fix, part c):
/// a `Failed(Counterexample)` verdict is demoted to `Unknown(Demoted)` when
/// `PremiseNeutralizedEq` fired during this verification — i.e. an equality
/// premise was fabricated away (`__trust_wp_unencodable_eq_*`) while encoding
/// in assumption position. The counterexample may only exist because a real
/// premise vanished, so it must not surface as a definitive rejection. Other
/// demoting categories deliberately do NOT touch `Failed` (they guard false
/// proofs, and genuine goal-side failures must keep their verdicts).
pub(crate) fn demote_if_unsound(
    before: &unsoundness::Snapshot,
    result: VerificationResult,
) -> VerificationResult {
    match result {
        VerificationResult::Verified(_) => {
            let after = unsoundness::snapshot();
            let d = unsoundness::delta(before, &after);
            if unsoundness::has_demoting(&d) {
                let categories = unsoundness::format_demoting(&d);
                VerificationResult::Unknown(UnknownReason::Demoted(format!(
                    "demoted: encoding approximations may affect soundness: {categories}"
                )))
            } else {
                result
            }
        }
        VerificationResult::Failed(_) => {
            let after = unsoundness::snapshot();
            let d = unsoundness::delta(before, &after);
            let neutralized = d
                .get(&unsoundness::UnsoundnessCategory::PremiseNeutralizedEq)
                .copied()
                .unwrap_or(0);
            if neutralized > 0 {
                VerificationResult::Unknown(UnknownReason::Demoted(format!(
                    "demoted: counterexample verdict withheld — encoding neutralized \
                     assumption-position equalities: premise_neutralized_eq({neutralized})"
                )))
            } else {
                result
            }
        }
        other => other,
    }
}

/// Merge pre-verification and post-bootstrap snapshots for the demotion baseline.
///
/// Uses the pre-verification snapshot as the base for all categories so that
/// driver-side and precondition-phase increments remain visible to
/// `demote_if_unsound`. For categories with bootstrap false positives
/// (identified by [`UnsoundnessCategory::has_bootstrap_false_positives`]),
/// overrides with the post-bootstrap value to absorb false-positive increments
/// from sort hint collection during bootstrap (infer_expr_sort encounters
/// LogicFnCall nodes before declarations exist). (#994, #2106)
///
/// **Important:** `post_bootstrap` must be taken AFTER bootstrap but BEFORE
/// precondition encoding (`encode_and_assert_requires`). Using a post-setup
/// snapshot (after preconditions) would also absorb real precondition-phase
/// increments, masking genuine unsoundness. (#2623)
///
/// Shared between `function` and `mut_borrow` paths to prevent drift (#2365).
pub(crate) fn merge_pre_verification_and_post_bootstrap_snapshots(
    pre_verification: &unsoundness::Snapshot,
    post_bootstrap: &unsoundness::Snapshot,
) -> unsoundness::Snapshot {
    let mut merged = pre_verification.clone();
    // Override bootstrap-false-positive categories with their post-bootstrap
    // values. This absorbs sort-hint-phase noise while preserving real
    // precondition-phase increments. The set of affected categories is
    // maintained centrally on UnsoundnessCategory::has_bootstrap_false_positives.
    for (&cat, &post_val) in post_bootstrap {
        if cat.has_bootstrap_false_positives() {
            merged.insert(cat, post_val);
        }
    }
    merged
}

const MAX_CLOSURE_CAPTURE_PROJECTION_DEPTH: usize = 8;

fn final_name_at_depth(base: &str, depth: usize) -> String {
    (0..depth).fold(base.to_string(), |name, _| {
        DerivedKind::Final.format_name(&name)
    })
}

/// Assert capture projection bindings for registered closure sorts (#1489).
///
/// For each [`ClosureCaptureInfo`] with a known `param_name`, asserts that the
/// observed closure state chain projects back to the matching caller capture
/// state chain:
///
/// ```text
/// capture_i(c) == x
/// capture_i(c_final) == x_final
/// capture_i(c_final_final) == x_final_final
/// ```
///
/// where `c` is the closure parameter and `x` is capture field `i`.
///
/// This connects the structural closure sort (from Layer 1) to the caller's
/// variable bindings, enabling the solver to reason about how closure calls
/// affect captured mutable state across sequential FnOnce/FnMut calls.
///
/// When the MIR analysis does not produce a `{param}_final` variable, this
/// function auto-creates it (with the closure's registered sort) provided at
/// least one captured variable has a `_final` form in scope (#1543).
///
/// Shared between `function.rs` and `mut_borrow.rs` to prevent drift.
pub(crate) fn assert_closure_capture_projections(
    encoder: &mut AYEncoder,
    captures: &[ClosureCaptureInfo],
    debug_prefix: &str,
) -> Result<(), EncodingError> {
    let mut var_names: std::collections::HashSet<String> =
        encoder.var_names().into_iter().collect();
    if !captures.is_empty() {
        debug!(
            "  {debug_prefix}closure capture projection: {} capture info(s), {} encoder vars",
            captures.len(),
            var_names.len()
        );
    }
    for info in captures {
        let Some(param_name) = info.param_name() else {
            continue;
        };

        for depth in 0..=MAX_CLOSURE_CAPTURE_PROJECTION_DEPTH {
            let closure_state_var = final_name_at_depth(param_name, depth);
            if !var_names.contains(&closure_state_var) {
                // Auto-create `{param}_final` when a matching capture `_final`
                // exists even if the closure pre-state was not materialized; this
                // preserves the original #1543 behavior. Deeper states still need
                // the prior closure state to avoid inventing disconnected chains.
                let has_matching_capture_state = info
                    .captures()
                    .iter()
                    .any(|field| var_names.contains(&final_name_at_depth(field.name(), depth)));
                let has_previous_closure_state = depth == 1
                    || (depth > 1
                        && var_names.contains(&final_name_at_depth(param_name, depth - 1)));

                if depth == 0 || !has_matching_capture_state || !has_previous_closure_state {
                    continue;
                }

                let sort = encoder.register_closure_struct_sort(info.def_id(), info.captures())?;
                debug!(
                    "  {debug_prefix}closure '{}': auto-creating '{}' with sort {:?}",
                    info.def_id(),
                    closure_state_var,
                    sort
                );

                encoder.get_or_declare_var(&closure_state_var, sort)?;
                var_names.insert(closure_state_var.clone());
            }

            let capture_bindings: Vec<(usize, String)> = info
                .captures()
                .iter()
                .enumerate()
                .filter_map(|(idx, field)| {
                    let caller_var = final_name_at_depth(field.name(), depth);
                    if var_names.contains(&caller_var) {
                        return Some((idx, caller_var));
                    }

                    if depth > 0
                        && matches!(field.kind(), CaptureKind::ByMutRef)
                        && var_names.contains(param_name)
                        && var_names.contains(field.name())
                    {
                        // Sequential mutable captures need intermediate prophecy
                        // variables even when the VC only mentions the last one:
                        // c -> x, c_final -> x_final, c_final_final ->
                        // x_final_final. assert_capture_projection declares the
                        // capture-side variable with the registered capture sort.
                        return Some((idx, caller_var));
                    }

                    if depth == 1
                        && matches!(field.kind(), CaptureKind::ByMutRef)
                        && !var_names.contains(param_name)
                        && var_names.contains(field.name())
                    {
                        // Legacy fallback: some older ByMutRef VCs name the
                        // caller post-state with the bare capture name and do
                        // not expose the closure pre-state. Do not use this
                        // fallback when `c -> x` can be projected, because then
                        // `c_final -> x` would collapse a real mutation.
                        return Some((idx, field.name().to_string()));
                    }

                    None
                })
                .collect();
            if !capture_bindings.is_empty() {
                encoder.assert_capture_projection(
                    info.def_id(),
                    &closure_state_var,
                    &capture_bindings,
                )?;
                for (_, caller_var) in capture_bindings {
                    var_names.insert(caller_var);
                }
            }
        }
    }
    Ok(())
}

/// Resolve the ADT type name from a capture field's `ExprSort`, peeling
/// `Ref`/`MutRef` wrappers.
///
/// Mirrors the driver's `capture_field_type_name`
/// (type_invariants/clauses.rs:686) so the receiver/type matching here is
/// term-identical to the `inv_T(receiver)` precondition the driver already
/// injects for the same captures.
fn capture_field_type_name(sort: &trust_wp_core::formula::ExprSort) -> Option<String> {
    use trust_wp_core::formula::{resolve_sort_name, ExprSort};
    match sort {
        ExprSort::Datatype(id) => Some(resolve_sort_name(*id)),
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => capture_field_type_name(inner),
        _ => None,
    }
}

/// True iff `requires` contains the driver-injected opaque invariant
/// precondition `inv_<method>(receiver_name)` — i.e. a top-level
/// `MethodCall { receiver: Var(receiver_name, _), method, args: [] }`.
///
/// This mirrors the exact shape produced by the driver's
/// `build_closure_capture_invariant_requires_with_receiver_names`
/// (type_invariants/clauses.rs:664): a zero-arg method call whose receiver is a
/// plain variable. The receiver match is sort-agnostic (name only) because the
/// driver and the consumer may annotate the receiver `Var` with different sort
/// metadata while referring to the same logical term. Used as the soundness
/// gate for `assert_captured_param_type_invariants`: the substituted body may
/// only be materialized when its defining hypothesis was actually assumed.
fn requires_inject_invariant_call(
    requires: &[PureExpr],
    receiver_name: &str,
    method_name: &str,
) -> bool {
    requires.iter().any(|req| match req {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if args.is_empty() && method == method_name => {
            matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == receiver_name)
        }
        _ => false,
    })
}

/// Assert the SUBSTITUTED type-invariant body for each invariant-bearing
/// closure capture that is already in scope, as a ground hypothesis.
///
/// At closure entry Creusot assumes `inv(closure_env)`, which decomposes to
/// `inv(capture_i)` for each captured field at its entry (pre-state) value.
/// The driver already injects this as the opaque `inv_T(receiver)` requires
/// (type_invariants/clauses.rs:559/576), and the encoder registers the
/// invariant as a DEFINING axiom `inv_T(z) <=> body[z/self]`
/// (encoder/logic_fn/type_invariant.rs:37). For closure VCs the ground-pool
/// flush that would connect `inv_T(receiver)` to its body never fires, so the
/// captured field's logical content (e.g. `x.0@ == 0` for `Zero`) stays
/// unconstrained and the negated VC is spuriously SAT (closures/10_tyinv).
///
/// This helper bypasses that ground-pool / E-matching dependency by asserting
/// the substituted body directly, mirroring the proven
/// `assert_type_invariant_precheck_facts` substitute -> encode -> coerce-Bool
/// -> assert pattern (verify/function/mod.rs:589). It asserts ONLY the exact
/// matched `TypeInvariantDef` body (never a strengthened predicate), ONLY for
/// genuine closure captures already in scope (`var_names` guard), and ONLY at
/// the entry receiver var (never a `_final`/prophecy state).
///
/// SOUNDNESS GATE (`requires`): the substituted body is asserted ONLY when the
/// driver actually injected the opaque `inv_T(receiver)` precondition for that
/// exact `(receiver, type)` pair (`build_closure_capture_invariant_requires` /
/// `build_current_closure_self_invariant_requires`). The asserted body is a
/// logical consequence of that very hypothesis (the encoder registers
/// `inv_T(z) <=> body[z/self]`), so when the requires is present this helper
/// only *materializes* an already-assumed fact and cannot manufacture a
/// false-accept. WITHOUT the matching requires, asserting the body would
/// fabricate a hypothesis the driver never assumed (e.g. a capture whose
/// invariant injection is absent or only partial), spuriously certifying
/// programs that are NOT safe. We therefore fail closed: no matching requires
/// => no body asserted (the capture stays unconstrained and the VC is
/// correctly unable to certify safety). (fix3-closure-typeinv; soundness fix
/// 2026-06-02)
pub(crate) fn assert_captured_param_type_invariants(
    encoder: &mut AYEncoder,
    captures: &[ClosureCaptureInfo],
    type_invariants: Option<&[trust_wp_core::logic::TypeInvariantDef]>,
    requires: &[PureExpr],
) -> Result<(), EncodingError> {
    let Some(invariants) = type_invariants else {
        return Ok(());
    };
    if invariants.is_empty() || captures.is_empty() {
        return Ok(());
    }

    // Snapshot the variables already participating in this VC. Asserting the
    // body only for in-scope receivers guarantees the fact connects to the
    // obligation (no disconnected/invented constraints).
    let var_names: std::collections::HashSet<String> = encoder.var_names().into_iter().collect();

    // Dedup the same (receiver, type) pair across captures/closures.
    let mut seen: std::collections::HashSet<(String, String)> = std::collections::HashSet::new();

    for info in captures {
        for (idx, field) in info.captures().iter().enumerate() {
            // Resolve the capture's ADT type name, peeling Ref/MutRef wrappers.
            let Some(type_name) = capture_field_type_name(field.sort()) else {
                continue;
            };

            // Find the matching invariant definition: exact type-name match,
            // then crate-qualified-suffix fallback (mirrors the driver).
            let matching_inv = invariants
                .iter()
                .find(|inv| inv.type_name() == type_name)
                .or_else(|| {
                    if type_name.contains("::") {
                        return None;
                    }
                    let suffix = format!("::{type_name}");
                    invariants
                        .iter()
                        .find(|inv| inv.type_name().ends_with(&suffix))
                });
            let Some(inv) = matching_inv else {
                continue;
            };

            // Trivial container-invariant stubs add no information; skip them
            // (the encoder already fast-paths `Bool(true)` bodies).
            if matches!(inv.body(), PureExpr::Bool(true)) {
                continue;
            }

            // Candidate receiver names that carry the ENTRY (pre-state) value:
            //  - capture-name form (`x`), what build_closure_capture_invariant_requires uses;
            //  - `self.N` form, only when the closure self is the receiver,
            //    what build_current_closure_self_invariant_requires uses.
            let mut receiver_names = vec![field.name().to_string()];
            if info.param_name() == Some("self") {
                receiver_names.push(format!("self.{idx}"));
            }

            let method_name = trust_wp_core::logic::type_invariant_method_name(inv.type_name());

            for receiver_name in receiver_names {
                // Only assert for a receiver that is (a) actually in scope so
                // the fact unifies with the obligation, and (b) the entry
                // value, never a `_final`/prophecy state where re-establishing
                // the invariant is an obligation, not an assumption.
                if !var_names.contains(&receiver_name) || receiver_name.contains("_final") {
                    continue;
                }

                // SOUNDNESS GATE: only materialize the invariant body when the
                // driver actually injected the matching opaque
                // `inv_T(receiver)` precondition for this `(receiver, type)`
                // pair. Asserting the body is sound ONLY as the realization of
                // that already-assumed hypothesis; without it we would fabricate
                // a fact the program never establishes (missing or partial
                // invariant injection), which would spuriously certify unsafe
                // code. Fail closed: skip when the requires is absent.
                if !requires_inject_invariant_call(requires, &receiver_name, &method_name) {
                    continue;
                }

                let key = (receiver_name.clone(), type_name.clone());
                if seen.contains(&key) {
                    continue;
                }
                seen.insert(key);

                // Preserve the capture's exact sort so the substituted receiver
                // unifies with the obligation's use of the same variable.
                let receiver_expr =
                    PureExpr::Var(receiver_name.clone(), Some(field.sort().clone()));
                let mut substitutions = std::collections::HashMap::new();
                substitutions.insert(inv.self_param().to_string(), receiver_expr);
                let body = inv.body().substitute(&substitutions);

                let term = encoder.encode_pure(&body)?;
                let term = encoder.coerce_bool_operand(term);
                encoder.assert_term(term);
            }
        }
    }

    Ok(())
}

/// Assert container element invariants for precondition-referenced receivers.
///
/// For container types (for example `Vec<T>`) with element invariants, this
/// asserts that every element of the container's Seq view satisfies the
/// element invariant. The body form is inlined when available to compensate
/// for ay-dpll's single-round E-matching limit. Shared helper for verification
/// paths that need the function-path workaround without duplicating it. (#869, #2365)
pub(crate) fn assert_container_element_invariants(
    encoder: &mut AYEncoder,
    requires: &[PureExpr],
    type_invariants: Option<&[trust_wp_core::logic::TypeInvariantDef]>,
) -> Result<(), EncodingError> {
    let Some(invariants) = type_invariants else {
        return Ok(());
    };

    for inv in invariants {
        let Some(element_method) = inv.element_invariant_method() else {
            continue;
        };

        let element_inv = invariants.iter().find(|other| {
            trust_wp_core::logic::type_invariant_method_name(other.type_name()) == element_method
        });
        let container_method = trust_wp_core::logic::type_invariant_method_name(inv.type_name());

        for req in requires {
            let Some(param_name) = function::extract_invariant_receiver_var(req, &container_method)
            else {
                continue;
            };
            let view_name = DerivedKind::View.format_name(&param_name);
            if let Some(elem_inv) = element_inv {
                encoder.register_container_element_invariant_body_spec(
                    &view_name,
                    elem_inv.self_param(),
                    elem_inv.body(),
                )?;
            } else {
                encoder
                    .register_container_element_invariant_method_spec(&view_name, element_method)?;
            }
        }
    }

    Ok(())
}

// Generic solve helpers moved to solver_tail.rs (#1576 Slice B).
// See re-exports at top of this file for backward compatibility.

/// Register type invariant definitions as axioms on the encoder.
///
/// For each `TypeInvariantDef`, registers sort hints for the body expression,
/// resolves the parameter sort, and calls `register_type_invariant` to add
/// the `∀ self. invariant(self) = body` axiom. (#785: lifted from loops.rs
/// for shared use by function.rs and mut_borrow.rs.)
fn register_type_invariants_on_encoder(
    encoder: &mut AYEncoder,
    type_invariants: Option<&[trust_wp_core::logic::TypeInvariantDef]>,
) -> Result<(), EncodingError> {
    if let Some(inv_defs) = type_invariants {
        for inv in inv_defs {
            encoder.register_sort_hints(std::slice::from_ref(inv.body()));
            // Type invariant bodies ARE formulas (boolean predicates over self),
            // so bare Var/LogicFnCall leaves in formula position need Bool sort. (#1965)
            encoder.register_formula_sort_hints(std::slice::from_ref(inv.body()));
            let sort = if let Some(param_sort) = inv.param_sort() {
                encoder.sort_from_param_sort(param_sort.clone())
            } else if let Some(inferred) = infer_type_invariant_self_sort(inv) {
                inferred
            } else {
                unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromVar);
                Sort::Int
            };
            encoder.register_type_invariant(inv.type_name(), inv.self_param(), sort, inv.body())?;
        }
    }
    Ok(())
}

fn infer_type_invariant_self_sort(inv: &trust_wp_core::logic::TypeInvariantDef) -> Option<Sort> {
    let usage = collect_variable_usage_as_formula(std::slice::from_ref(inv.body()));
    let self_usage = usage.get(inv.self_param())?;
    let sort = determine_sort(self_usage);
    (sort != Sort::Int).then_some(sort)
}

fn new_encoder_for_track_with_arrays(
    track: TrackLevel,
    use_quantifiers: bool,
    needs_array_theory: bool,
) -> Result<AYEncoder, EncodingError> {
    match track {
        TrackLevel::Auto | TrackLevel::Reg => {
            // Pure functions - no heap operations by default.
            // When needs_array_theory is set (e.g., IndexMut Seq encoding
            // using store/select), escalate to array-capable logic. (#1317)
            if needs_array_theory {
                if use_quantifiers {
                    AYEncoder::try_new_with_quantifiers()
                } else {
                    AYEncoder::try_new()
                }
            } else if use_quantifiers {
                // The default quantified track takes the CERTIFIABLE Seq
                // carrier. ay withholds strict proof authority from any
                // refutation whose proof mentions a native `Sort::Seq(_)`,
                // because the pinned Alethe calculus has no sequence sort and
                // carcara rejects such a problem at parse time. On this track
                // that cost is unnecessary: sequences here are modelled
                // entirely by trust-wp's own UF/array projectors, so an
                // uninterpreted carrier loses nothing and keeps the proof
                // externally replayable.
                //
                // The reason this could not simply be switched on before is
                // that the stateless sort converter hard-coded the native
                // spelling, so choosing the uninterpreted carrier split the
                // encoder's Seq sort in two — variables declared `(Seq Int)`,
                // projectors declared over `Seq`, and `Solver::apply` failing
                // its domain check. The carrier is now threaded through to the
                // converter, so both agree.
                AYEncoder::try_new_pure_with_quantifiers().map(|mut encoder| {
                    encoder.use_certifiable_seq_carrier();
                    encoder
                })
            } else {
                AYEncoder::try_new_pure()
            }
        }
        TrackLevel::Ptr | TrackLevel::Mem => {
            // Heap-using functions - need array theory
            if use_quantifiers {
                AYEncoder::try_new_with_quantifiers()
            } else {
                AYEncoder::try_new()
            }
        }
        // TrackLevel is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => AYEncoder::try_new(),
    }
}

#[cfg(test)]
mod counterexample_tests;
#[cfg(test)]
mod shared_constraints_tests;
#[cfg(test)]
mod tests;
