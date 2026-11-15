// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-slice obligation verification for standard function contracts.

use std::{
    collections::{HashMap, HashSet},
    panic::AssertUnwindSafe,
    sync::Arc,
    time::Duration,
};

use trust_wp_core::{
    formula::{
        internal::tuple_lowering::{
            tuple_field_logic_fn_index, tuple_field_logic_fn_name, tuple_logic_fn_arity,
        },
        BinOp, MatchArm, Pattern, PureExpr,
    },
    logic::LogicMode,
};

use super::super::{
    encode_negated_postcondition, is_trivially_true_postcondition,
    logic_fn_equality_has_visible_body_candidate, logic_fn_equality_is_finite_enumerable_candidate,
    logic_fn_equality_is_projected_index_candidate, logic_fn_equality_matches_body,
    pipeline::catch_verification_phase_ay_panics,
    postcondition_contains_visible_recursive_logic_call, postcondition_contradicts_requirements,
    postcondition_true_via_logic_bodies, recursive_logic_fn_equality_matches_evaluation,
    recursive_postcondition_matches_evaluation_under_requires,
    requirements_imply_postcondition_via_logic_bodies,
    result_equals_return_expr_via_logic_body_with_requires,
    result_match_over_option_ite_is_directly_invalid, result_postcondition_contradicts_return_expr,
    result_postcondition_contradicts_return_expr_via_logic_bodies,
    result_postcondition_matches_return_expr,
    result_postcondition_matches_return_expr_via_logic_bodies,
    solver_tail::{AliasConstraintMode, ObligationSliceContext},
    PostconditionInfo, ResolveContinuation, UnknownReason, VerificationResult,
};
use crate::{
    encoder::{
        closure_sorts::closure_env_sort_name, match_enc::short_constructor_name, unsoundness,
        AYEncoder,
    },
    error::EncodingError,
};

/// Verify a single obligation (one postcondition) within a push/pop scope.
///
/// The caller must have already called `encoder.push_scope()` before this
/// function. On [`ResolveContinuation::Continue`] the caller must call
/// `encoder.pop_scope()`. On [`ResolveContinuation::Abort`] the live encoder
/// was not restored (hard timeout), so the caller must skip `pop_scope()` and
/// return immediately. (#1342)
///
/// Encodes and negates the postcondition locally, then delegates to
/// [`super::super::solver_tail::verify_negated_obligation_slice`] for the
/// shared post-negation tail (disjunction, alias, axioms, SAT). (#1576)
///
/// On `Failed` results, tags the counterexample with violated-postcondition
/// metadata (clause index + clause text) so the driver can render a precise
/// "violated ensures #N: <clause>" diagnostic without re-deriving which
/// clause failed.
pub(super) fn verify_single_obligation_slice(
    encoder: &mut AYEncoder,
    obligation_index: usize,
    ensure: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> Result<ResolveContinuation, EncodingError> {
    let _shape_scope = SliceRefutationShapeScope::enter();
    let cont = verify_single_obligation_slice_inner(encoder, obligation_index, ensure, ctx)?;
    // Publish the shape BEFORE the scope drops. A `Failed` that a structural
    // shape also refuted was decided from the program text, not from a model
    // over values trust-wp manufactured, and that is the only refutation the
    // injected-goal gate (D-27) may let through in a function whose goal set
    // carries a fail-closed marker.
    super::super::solver_tail::publish_last_slice_refutation_shape(
        continuation_is_failed(&cont)
            .then(slice_refutation_shape)
            .flatten(),
    );
    Ok(tag_continuation_with_violated_postcondition(
        cont,
        obligation_index,
        ensure,
    ))
}

/// Does this continuation carry a refutation?
fn continuation_is_failed(cont: &ResolveContinuation) -> bool {
    matches!(
        cont,
        ResolveContinuation::Continue(VerificationResult::Failed(_))
            | ResolveContinuation::Abort(VerificationResult::Failed(_))
    )
}

/// Inner implementation of [`verify_single_obligation_slice`]; the public
/// wrapper attaches violated-postcondition metadata on `Failed` results
/// regardless of which precheck path produced them.
fn verify_single_obligation_slice_inner(
    encoder: &mut AYEncoder,
    obligation_index: usize,
    ensure: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> Result<ResolveContinuation, EncodingError> {
    if requirement_includes_ensure(ctx.requires, ensure) {
        return prove_prechecked_literal_false_obligation_with_solver(
            encoder,
            obligation_index,
            ctx,
        );
    }
    if seq_ext_eq_concat_length_conservation_follows_requires(ensure, ctx.requires)
        || seq_ext_eq_concat_left_length_bound_follows_requires(ensure, ctx.requires)
    {
        return prove_prechecked_literal_false_obligation_with_solver(
            encoder,
            obligation_index,
            ctx,
        );
    }
    if let Some(result) =
        prove_implication_false_guard_with_solver(encoder, obligation_index, ensure, ctx.requires)?
    {
        return Ok(result);
    }
    if type_invariant_postcondition_prechecked(ensure, ctx) {
        return prove_prechecked_literal_false_obligation_with_solver(
            encoder,
            obligation_index,
            ctx,
        );
    }
    if take_first_mut_result_match_follows_split_first_source(ensure, ctx.return_expr, ctx.requires)
    {
        return prove_verified_obligation_with_solver(encoder, obligation_index, ensure, ctx);
    }
    if final_borrow_option_field_selector_matches(ensure, ctx.return_expr) {
        return prove_prechecked_literal_false_obligation_with_solver(
            encoder,
            obligation_index,
            ctx,
        );
    }
    if final_borrow_result_field_selector_matches(ensure, ctx.return_expr) {
        return prove_prechecked_literal_false_obligation_with_solver(
            encoder,
            obligation_index,
            ctx,
        );
    }
    // A constructor-preserving enum match is a complete finite proof: every
    // input constructor is covered, the returned constructor is the same, and
    // each payload postcondition is authenticated by the matching requirement.
    // Discharge this certified shape directly so the subsequent datatype base
    // model check cannot turn a proved obligation into a timeout.
    if result_constructor_match_postcondition_follows_return_branches(
        ensure,
        ctx.return_expr,
        ctx.requires,
    ) {
        return prove_prechecked_literal_false_obligation_with_solver(
            encoder,
            obligation_index,
            ctx,
        );
    }
    if result_match_postcondition_follows_return_branches(ensure, ctx.return_expr, ctx.requires) {
        return prove_verified_obligation_with_solver(encoder, obligation_index, ensure, ctx);
    }
    if let Some(proof_expr) =
        super::result_match_constructor_prechecked_body(ctx.requires, ensure, ctx.return_expr)
    {
        return prove_verified_obligation_with_solver(encoder, obligation_index, &proof_expr, ctx);
    }
    if result_match_over_option_ite_follows_selected_branch(ensure, ctx.return_expr, ctx.requires) {
        return prove_verified_obligation_with_solver(encoder, obligation_index, ensure, ctx);
    }
    if sequence_tail_reverse_push_front_index_proof_assert_matches(ensure)
        || sequence_tail_reverse_push_front_index_proof_assert_follows_requires(
            ensure,
            ctx.requires,
        )
    {
        return prove_prechecked_literal_false_obligation_with_solver(
            encoder,
            obligation_index,
            ctx,
        );
    }
    if increment_by_one_postcondition_follows_from_facts(ensure, ctx.requires) {
        return prove_prechecked_literal_false_obligation_with_solver(
            encoder,
            obligation_index,
            ctx,
        );
    }
    if result_postcondition_matches_direct_logic_call_contract(
        ensure,
        ctx.return_expr,
        ctx.requires,
        ctx.logic_fns,
    ) {
        return prove_prechecked_literal_false_obligation_with_solver(
            encoder,
            obligation_index,
            ctx,
        );
    }
    if result_postcondition_matches_logic_call_ite_condition_contract(
        ensure,
        ctx.return_expr,
        ctx.requires,
        ctx.logic_fns,
    ) {
        return prove_prechecked_literal_false_obligation_with_solver(
            encoder,
            obligation_index,
            ctx,
        );
    }
    // Structural refutations (the shapes below) are trace-only hints, never
    // the verdict. A `Failed` may only be published with a VALIDATED model
    // (D-28), and a model-free `Failed` would only ever surface as
    // `unknown (refutation withheld)`. Each such shape is a query the solver
    // answers SAT trivially — `requires ∧ body ∧ ¬ensure` with the
    // contradiction already syntactic — so fall through to
    // `prove_verified_obligation_with_solver`, which produces the validated
    // counterexample.
    let mut structural_refuted = false;
    // ONCE A SHAPE HAS FIRED, NO STRUCTURAL LANE MAY SAY `Verified`.
    //
    // A shape only records a hint and falls through for the model, so the
    // structural accepts below stay reachable after one fires and the rule
    // has to be enforced explicitly: `break 'structural_lanes` jumps straight
    // to the real negated-goal solve at the end of this function, the only
    // thing allowed to decide a slice a shape refuted (and whose `Verified` is
    // then withheld by `structural_refutation_disagrees_with_proof`). The
    // permitted outcomes are exactly: `Failed` with a validated model, or a
    // withheld `Unknown`.
    //
    // `SliceRefutationShapeScope` is the second, non-bypassable half of the
    // same rule: every structural accept re-checks it, so a lane reached by a
    // future edit to this ordering still cannot return an accept.
    'structural_lanes: {
        if result_match_over_option_ite_is_directly_invalid(ensure, ctx.return_expr) {
            structural_refuted |=
                structural_refutation_hint("result-match-over-option-ite-directly-invalid");
        }
        if structural_refuted {
            break 'structural_lanes;
        }
        if postcondition_is_logic_fn_spec_instance(ensure, ctx.logic_fns, ctx.requires) {
            return prove_prechecked_literal_false_obligation_with_solver(
                encoder,
                obligation_index,
                ctx,
            );
        }
        if result_postcondition_matches_return_expr(ensure, ctx.return_expr, ctx.requires) {
            if postcondition_or_return_contains_div_or_mod(ensure, ctx.return_expr) {
                if div_mod_denominators_guarded_by_requires(ensure, ctx.return_expr, ctx.requires) {
                    return prove_prechecked_literal_false_obligation_with_solver(
                        encoder,
                        obligation_index,
                        ctx,
                    );
                }
                if let Some(result) = structurally_verified_precheck_with_base_recheck(ctx) {
                    return Ok(ResolveContinuation::Continue(result));
                }
            }
            return prove_verified_obligation_with_solver(encoder, obligation_index, ensure, ctx);
        }
        if result_postcondition_matches_return_expr_with_encoder_type_constants(
            encoder,
            ensure,
            ctx.return_expr,
            ctx.requires,
        ) {
            if postcondition_or_return_contains_div_or_mod(ensure, ctx.return_expr) {
                if div_mod_denominators_guarded_by_requires(ensure, ctx.return_expr, ctx.requires) {
                    return prove_prechecked_literal_false_obligation_with_solver(
                        encoder,
                        obligation_index,
                        ctx,
                    );
                }
                if let Some(result) = structurally_verified_precheck_with_base_recheck(ctx) {
                    return Ok(ResolveContinuation::Continue(result));
                }
            }
            return prove_verified_obligation_with_solver(encoder, obligation_index, ensure, ctx);
        }
        if result_postcondition_matches_return_expr_via_logic_bodies(
            ensure,
            ctx.logic_fns,
            ctx.return_expr,
            ctx.requires,
        ) {
            return prove_prechecked_literal_false_obligation_with_solver(
                encoder,
                obligation_index,
                ctx,
            );
        }
        if super::result_postcondition_matches_return_expr_via_context_fact(
            ensure,
            ctx.return_expr,
            Some(ctx.requires),
            ctx.logic_fns,
        ) || result_equality_follows_from_context_fact(ensure, ctx.return_expr, ctx.requires)
        {
            return prove_verified_obligation_with_solver(encoder, obligation_index, ensure, ctx);
        }
        if result_postcondition_contradicts_return_expr_via_logic_bodies(
            ensure,
            ctx.logic_fns,
            ctx.return_expr,
            ctx.requires,
        ) {
            structural_refuted |=
                structural_refutation_hint("result-contradicts-return-expr-via-logic-bodies");
        }
        if result_postcondition_contradicts_return_expr(ensure, ctx.return_expr, ctx.requires) {
            structural_refuted |= structural_refutation_hint("result-contradicts-return-expr");
        }
        if postcondition_contradicts_requirements(ensure, ctx.requires) {
            structural_refuted |=
                structural_refutation_hint("postcondition-contradicts-requirements");
        }
        if structural_refuted {
            break 'structural_lanes;
        }
        if logic_fn_equality_matches_body(ensure, ctx.logic_fns) {
            return prove_verified_obligation_with_solver(encoder, obligation_index, ensure, ctx);
        }
        if recursive_logic_fn_equality_matches_evaluation(ensure, ctx.logic_fns, ctx.mode_overrides)
        {
            return prove_prechecked_literal_false_obligation_with_solver(
                encoder,
                obligation_index,
                ctx,
            );
        }
        if recursive_postcondition_matches_evaluation_under_requires(
            ensure,
            ctx.requires,
            ctx.logic_fns,
            ctx.mode_overrides,
        ) {
            return prove_prechecked_literal_false_obligation_with_solver(
                encoder,
                obligation_index,
                ctx,
            );
        }
        // A postcondition over a visible recursive logic fn is normally hopeless
        // for the solver (the defining forall would need unbounded E-matching), so
        // it short-circuits to Unknown — UNLESS the setup phase has already
        // asserted ground one-step unfolding instances of that recursive fn at
        // exactly this ensure's argument points
        // (`assert_recursive_logic_fn_symbolic_unfoldings_for_goal_and_assumptions`
        // runs over ctx.ensures before any obligation slice). In that case the
        // solver has real ground material — e.g. filter_positive's lemma
        // postconditions over `num_of_pos` — and must be allowed to RUN. This is a
        // routing decision only, never a soundness one: Verified still requires a
        // genuine debug-checked UNSAT from the solver.
        if postcondition_contains_visible_recursive_logic_call(
            ensure,
            ctx.logic_fns,
            ctx.mode_overrides,
        ) && !super::return_expr_contains_logic_proof_call(ctx.return_expr, ctx.logic_fns)
            && !ensure_covered_by_ground_recursive_unfoldings(ensure, ctx)
        {
            return Ok(ResolveContinuation::Continue(VerificationResult::Unknown(
                UnknownReason::Unspecified,
            )));
        }
        // Native QF_BV fast path for `#[bitwise_proof]` popcount-style obligations
        // (`result@ == count8_log(n)`). The general encoder lowers this through the
        // `int2bv`/`bv2int` bridge, producing a mixed LIA+BV query that churns and
        // times out on the current ay; this discharges it as a pure-BV bitblast
        // instead. SOUND by construction (see `bitwise_bv_proof`): it only returns a
        // definitive Verified/Failed when the spec side provably stays in range, and
        // otherwise BAILS to the general path below. (#popcount)
        if let Some(result) = super::bitwise_bv_proof::try_prove_bitwise_bv_obligation(ensure, ctx)
        {
            return Ok(ResolveContinuation::Continue(
                withhold_structural_accept_after_shape(result),
            ));
        }
        // Tier 2 of the native QF_BV fast path (#route-100 rightmostbit):
        // SIGNED widths, boolean obligation structure (==>/&&/iff/!/positive
        // bounded forall), and wrapping-spec call results. Same soundness
        // contract as tier 1: UNSAT-only acceptance on an isolated exact-width
        // encoding, fail-closed bail on anything unsupported (see
        // `bitwise_bv_proof_general` module docs).
        if let Some(result) =
            super::bitwise_bv_proof_general::try_prove_general_bitwise_obligation(ensure, ctx)
        {
            return Ok(ResolveContinuation::Continue(
                withhold_structural_accept_after_shape(result),
            ));
        }
        if postcondition_true_via_logic_bodies(ensure, ctx.logic_fns) {
            return prove_verified_obligation_with_solver(encoder, obligation_index, ensure, ctx);
        }
        if requirements_imply_postcondition_via_logic_bodies(
            ensure,
            ctx.logic_fns,
            ctx.return_expr,
            ctx.requires,
        ) {
            return prove_verified_obligation_with_solver(encoder, obligation_index, ensure, ctx);
        }
        if result_equals_return_expr_via_logic_body_with_requires(
            ensure,
            ctx.logic_fns,
            ctx.return_expr,
            ctx.requires,
        ) {
            return prove_verified_obligation_with_solver(encoder, obligation_index, ensure, ctx);
        }
        if logic_fn_equality_has_visible_body_candidate(ensure, ctx.logic_fns) {
            // `result@ == f(args)` over a non-recursive logic fn whose body is a
            // finite-domain integer/bitwise expression (e.g. popcount's
            // `result@ == count8_log(n)`) is decided by the solver's BV↔LIA
            // bit-blast/enumeration bridge even when no syntactic body match exists.
            // Route it to the solver instead of short-circuiting to Unknown. This is
            // a routing decision only — the solver still requires a full-domain UNSAT
            // to verify and reports a counterexample for any mismatching value, so a
            // wrong target (e.g. `result@ == f(n) + 1`) stays unprovable. (#popcount)
            //
            // Likewise route `result == f(args)` where f's body is a builtin
            // collection index over a field projection of a parameter (a user
            // `IndexLogic` impl accessor like `Memory::index_logic`, whose global
            // defining axiom is asserted): the obligation reduces to ground select
            // facts and is cheap for the solver. (list_reversal_lasso)
            if !logic_fn_equality_is_finite_enumerable_candidate(
                ensure,
                ctx.logic_fns,
                ctx.return_expr,
            ) && !logic_fn_equality_is_projected_index_candidate(ensure, ctx.logic_fns)
            {
                return Ok(ResolveContinuation::Continue(VerificationResult::Unknown(
                    UnknownReason::Unspecified,
                )));
            }
        }
        if closure_weakening_follows_from_requires(encoder, ensure, ctx) {
            return prove_prechecked_literal_false_obligation_with_solver(
                encoder,
                obligation_index,
                ctx,
            );
        }
        if closure_existential_postcondition_follows_from_requires(ensure, ctx.requires) {
            return prove_prechecked_literal_false_obligation_with_solver(
                encoder,
                obligation_index,
                ctx,
            );
        }
    } // 'structural_lanes
    if postcondition_depends_on_unconstrained_logic_fn(ensure, ctx.logic_fns, ctx.requires) {
        // The opaque / body-less logic fn is an uninterpreted symbol to the
        // solver, so `¬ensure` is satisfiable with a validated model naming
        // the value the hidden definition would have to rule out.
        structural_refuted |=
            structural_refutation_hint("postcondition-depends-on-unconstrained-logic-fn");
    }

    if super::result_binding::should_use_slice_local_match_result_binding(
        ctx.return_expr,
        ctx.all_ensures,
    ) {
        super::result_binding::assert_slice_local_match_result_body_binding(
            encoder,
            ensure,
            ctx.return_expr,
            ctx.all_ensures,
            ctx.requires,
        )?;
    }

    let tuple_rewritten_ensure = rewrite_tuple_getters_from_requirements(ensure, ctx.requires);
    if !crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
        ensure,
        &tuple_rewritten_ensure,
    ) && postcondition_contradicts_requirements(&tuple_rewritten_ensure, ctx.requires)
    {
        structural_refuted |=
            structural_refutation_hint("tuple-rewritten-postcondition-contradicts-requirements");
    }
    let ensure_for_encoding = &tuple_rewritten_ensure;

    let continuation =
        prove_verified_obligation_with_solver(encoder, obligation_index, ensure_for_encoding, ctx)?;
    if structural_refuted {
        let base_is_vacuous = matches!(
            &continuation,
            ResolveContinuation::Continue(VerificationResult::Unknown(reason))
                if unknown_reason_is_vacuous(reason)
        );
        if base_is_vacuous {
            // The fall-through solve reports the BASE itself UNSAT: the
            // requirements this slice runs under are contradictory, so
            // nothing about the obligation was proved and the shape's own
            // `requires ⟹ ¬ensure` reading is moot. Vacuity is its own
            // soundness gap in this tool (`vacuous > 0` → exit 2, same as
            // `requirements_are_obviously_contradictory`), and it is the
            // STRONGER statement, so report it rather than re-dressing it
            // as a bare structural `Failed` whose public boundary would
            // spend it as an uncounted `refutation withheld`.
            crate::verify::authority_trace(|| {
                "structural slice refutation over a vacuous base; reporting the vacuity".to_string()
            });
            return Ok(continuation);
        }
        match &continuation {
            ResolveContinuation::Continue(VerificationResult::Unknown(reason)) => {
                // The solver could not decide a slice a structural shape
                // already refuted (quantified context, typically). The shape
                // proves `requires ⟹ ¬ensure`, so a VALIDATED model of the
                // base alone is a validated counterexample: ask the AxiomLight
                // fresh base recheck for one (it records the refutation
                // witness the pipeline installs). Without one, keep the
                // structural `Failed` — the public boundary withholds it as
                // before.
                crate::verify::authority_trace(|| {
                    format!(
                        "solver inconclusive ({}) after a structural slice refutation; seeking \
                         a base witness",
                        reason.as_str()
                    )
                });
                return Ok(ResolveContinuation::Continue(
                    structural_refutation_with_base_witness(ctx),
                ));
            }
            ResolveContinuation::Continue(VerificationResult::Verified(_)) => {
                // The two disagree. Before the shapes fell through to the
                // solver this slice was a (withheld) `Failed`, never an
                // accept; a checked proof outranks a syntactic shape, but a
                // disagreement is a bug in one of them, so the accept is
                // withheld — fail closed, strictly narrowing, and the same
                // rule the function lane applies in
                // `reconcile_precheck_refutation`.
                return Ok(ResolveContinuation::Continue(
                    structural_refutation_disagrees_with_proof(),
                ));
            }
            _ => {}
        }
    }
    Ok(continuation)
}

/// Whether an `Unknown` reason is one of the two vacuity demotions
/// (`VACUOUS_PROOF_MESSAGE` / `VACUOUS_WITH_ENCODER_AXIOMS_MESSAGE`). The
/// driver's counter keys off the same `"vacuous proof"` prefix
/// (`callbacks/reporting.rs`), so this predicate and `vacuous > 0` agree.
fn unknown_reason_is_vacuous(reason: &UnknownReason) -> bool {
    matches!(
        reason,
        UnknownReason::SolverMessage(message)
            if message == super::super::solver_tail::VACUOUS_PROOF_MESSAGE
                || message == super::super::solver_tail::VACUOUS_WITH_ENCODER_AXIOMS_MESSAGE
    )
}

thread_local! {
    /// The first structural refutation shape that fired for the obligation
    /// slice currently being decided, if any.
    ///
    /// The shapes do not end the slice (they fall through to the solver so a
    /// `Failed` can carry a validated model), so the invariant *a refuted
    /// slice never reaches a structural accept* is carried here rather than
    /// by control flow (D-28). `verify_single_obligation_slice_inner`
    /// opens a `SliceRefutationShapeScope` on entry, so the flag is
    /// slice-scoped and nest-safe.
    static SLICE_REFUTATION_SHAPE: std::cell::Cell<Option<&'static str>> =
        const { std::cell::Cell::new(None) };
}

/// Slice-scoped ownership of [`SLICE_REFUTATION_SHAPE`]: clears it on entry and
/// restores the enclosing slice's value on drop, so a nested verification (a
/// fresh base recheck, a type-invariant precheck) cannot clobber or inherit an
/// outer slice's shape.
struct SliceRefutationShapeScope(Option<&'static str>);

impl SliceRefutationShapeScope {
    fn enter() -> Self {
        Self(SLICE_REFUTATION_SHAPE.with(|cell| cell.replace(None)))
    }
}

impl Drop for SliceRefutationShapeScope {
    fn drop(&mut self) {
        SLICE_REFUTATION_SHAPE.with(|cell| cell.set(self.0));
    }
}

/// The shape that refuted the slice being decided, if one has fired.
fn slice_refutation_shape() -> Option<&'static str> {
    SLICE_REFUTATION_SHAPE.with(std::cell::Cell::get)
}

/// Demote a structural accept produced after a refutation shape fired for this
/// slice. `Failed` and `Unknown` pass through untouched — the rule forbids only
/// the accept.
fn withhold_structural_accept_after_shape(result: VerificationResult) -> VerificationResult {
    let Some(shape) = slice_refutation_shape() else {
        return result;
    };
    if !matches!(result, VerificationResult::Verified(_)) {
        return result;
    }
    structural_accept_withheld_after_shape(shape)
}

/// The withheld verdict for a structural accept lane reached after a shape
/// refuted this slice. Such a lane proves nothing the shape did not already
/// contradict, so the accept is refused outright (fail closed).
fn structural_accept_withheld_after_shape(shape: &'static str) -> VerificationResult {
    crate::verify::authority_trace(|| {
        format!(
            "structural accept lane refused: refutation shape `{shape}` already fired for this              slice"
        )
    });
    VerificationResult::Unknown(UnknownReason::SolverMessage(format!(
        "structural refutation shape `{shape}` refuted this obligation; a structural accept          lane may not discharge it"
    )))
}

/// The withheld verdict for a slice a structural shape refuted and the solver
/// proved.
fn structural_refutation_disagrees_with_proof() -> VerificationResult {
    crate::verify::authority_trace(|| {
        "structural slice refutation shape disagrees with the solver's proof; verdict withheld"
            .to_string()
    });
    VerificationResult::Unknown(UnknownReason::SolverMessage(
        "structural refutation shape refuted this obligation but the solver proved it; \
         verdict withheld"
            .to_string(),
    ))
}

/// `Failed` for a structurally refuted slice, backed by the fresh base witness
/// when the base solves to a validated SAT (the witness stays in its slot for
/// the pipeline's installer); the bare structural `Failed` otherwise.
fn structural_refutation_with_base_witness(ctx: &ObligationSliceContext<'_>) -> VerificationResult {
    crate::verify::solver_tail::clear_refutation_witness();
    if let Some(recheck) = ctx.literal_false_base_recheck {
        if matches!(recheck(), Ok(VerificationResult::Verified(_))) {
            if let Some(witness) = crate::verify::solver_tail::clone_refutation_witness() {
                crate::verify::authority_trace(|| {
                    "structural slice refutation backed by a validated base witness".to_string()
                });
                return VerificationResult::Failed(witness.counterexample);
            }
        }
    }
    crate::verify::structural_failed_traced()
}

/// Whether the recursive-logic-fn calls in `ensure` are covered by the ground
/// one-step unfolding instances the setup phase asserts before obligation
/// slicing.
///
/// This re-runs the SAME collection
/// (`super::collect_recursive_logic_fn_symbolic_unfoldings`) that
/// `assert_recursive_logic_fn_symbolic_unfoldings_for_goal_and_assumptions`
/// ran over `ctx.ensures` (a superset of this `ensure`) during encoder setup:
/// a non-empty collection here means each collected requires/path-guarded
/// defining-equation instance — at this ensure's own argument points — is
/// already asserted in the live solver context. That is the cheapest sound
/// signal that letting the solver run is not hopeless. Used ONLY to route
/// past the Unknown short-circuit; the solver still decides the obligation.
fn ensure_covered_by_ground_recursive_unfoldings(
    ensure: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> bool {
    let Some(logic_fns) = ctx.logic_fns else {
        return false;
    };
    let mut facts = Vec::new();
    let mut seen = HashSet::new();
    super::collect_recursive_logic_fn_symbolic_unfoldings(
        ensure,
        logic_fns,
        ctx.mode_overrides,
        &mut facts,
        &mut seen,
    );
    !facts.is_empty()
}

/// Tag the inner verification result with violated-postcondition metadata
/// when it reports a `Failed` counterexample, so the driver can render a
/// precise "violated ensures #N: <clause>" diagnostic. No-op for
/// non-`Failed` results, and idempotent if the inner solver already attached
/// metadata.
fn tag_continuation_with_violated_postcondition(
    cont: ResolveContinuation,
    obligation_index: usize,
    ensure: &PureExpr,
) -> ResolveContinuation {
    let info = PostconditionInfo {
        clause_idx: obligation_index,
        contract_text: ensure.to_string(),
        span: None,
    };
    match cont {
        ResolveContinuation::Continue(result) => {
            ResolveContinuation::Continue(result.tag_violated_postcondition(info))
        }
        ResolveContinuation::Abort(result) => {
            ResolveContinuation::Abort(result.tag_violated_postcondition(info))
        }
    }
}

fn exact_requirement_precheck_with_base_recheck(
    ctx: &ObligationSliceContext<'_>,
) -> Option<VerificationResult> {
    structurally_verified_precheck_with_base_recheck(ctx)
}

fn structurally_verified_precheck_with_base_recheck(
    ctx: &ObligationSliceContext<'_>,
) -> Option<VerificationResult> {
    let fresh_base_recheck = ctx.fresh_base_recheck?;
    match fresh_base_recheck() {
        Ok(VerificationResult::Verified(_)) => {
            // A SAT base says only that the precheck's accept was not vacuous;
            // it is not a proof of the obligation. Refuse it outright once a
            // refutation shape has fired for this slice.
            if let Some(shape) = slice_refutation_shape() {
                return Some(structural_accept_withheld_after_shape(shape));
            }
            Some(super::super::solver_tail::prove_prechecked_literal_false_with_solver_evidence())
        }
        Ok(VerificationResult::Failed(counterexample)) => {
            Some(VerificationResult::Failed(counterexample))
        }
        Ok(VerificationResult::Assumed(reason)) => Some(VerificationResult::Assumed(reason)),
        Ok(VerificationResult::Unknown(_)) => None,
        Err(_) => None,
    }
}

fn postcondition_or_return_contains_div_or_mod(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
) -> bool {
    expr_contains_div_or_mod(ensure) || return_expr.is_some_and(expr_contains_div_or_mod)
}

fn div_mod_denominators_guarded_by_requires(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    requires: &[PureExpr],
) -> bool {
    let mut denominators = Vec::new();
    collect_div_mod_denominators(ensure, &mut denominators);
    if let Some(return_expr) = return_expr {
        collect_div_mod_denominators(return_expr, &mut denominators);
    }
    !denominators.is_empty()
        && denominators
            .iter()
            .all(|denom| denominator_guarded_by_requires(denom, requires))
}

fn collect_div_mod_denominators(expr: &PureExpr, out: &mut Vec<PureExpr>) {
    expr.for_each_recursive(|node| {
        if let PureExpr::BinOp(
            _,
            BinOp::Div | BinOp::Mod | BinOp::DivTrunc | BinOp::RemTrunc,
            rhs,
        ) = node
        {
            out.push(rhs.as_ref().clone());
        }
    });
}

fn denominator_guarded_by_requires(denom: &PureExpr, requires: &[PureExpr]) -> bool {
    matches!(denom, PureExpr::Int(value) if *value != 0)
        || requires
            .iter()
            .any(|require| requirement_implies_nonzero_denominator(require, denom))
}

fn requirement_implies_nonzero_denominator(require: &PureExpr, denom: &PureExpr) -> bool {
    match require {
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            requirement_implies_nonzero_denominator(lhs, denom)
                || requirement_implies_nonzero_denominator(rhs, denom)
        }
        PureExpr::BinOp(lhs, BinOp::Ne, rhs) => {
            same_expr_zero_pair(lhs, rhs, denom) || same_expr_zero_pair(rhs, lhs, denom)
        }
        PureExpr::BinOp(lhs, BinOp::Gt, rhs) => {
            same_expr(lhs, denom) && matches!(rhs.as_ref(), PureExpr::Int(value) if *value >= 0)
        }
        PureExpr::BinOp(lhs, BinOp::Lt, rhs) => {
            same_expr(lhs, denom) && matches!(rhs.as_ref(), PureExpr::Int(value) if *value <= 0)
        }
        _ => false,
    }
}

fn same_expr_zero_pair(candidate: &PureExpr, zero: &PureExpr, denom: &PureExpr) -> bool {
    same_expr(candidate, denom) && matches!(zero, PureExpr::Int(0))
}

fn expr_contains_div_or_mod(expr: &PureExpr) -> bool {
    let mut found = false;
    expr.for_each_recursive(|node| {
        if matches!(
            node,
            PureExpr::BinOp(
                _,
                BinOp::Div | BinOp::Mod | BinOp::DivTrunc | BinOp::RemTrunc,
                _
            )
        ) {
            found = true;
        }
    });
    found
}

fn result_postcondition_matches_return_expr_with_encoder_type_constants(
    encoder: &AYEncoder,
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    requires: &[PureExpr],
) -> bool {
    let Some(return_expr) = return_expr else {
        return false;
    };

    let mut substitutions = HashMap::new();
    collect_encoder_type_constant_substitutions(encoder, ensure, &mut substitutions);
    collect_encoder_type_constant_substitutions(encoder, return_expr, &mut substitutions);
    for require in requires {
        collect_encoder_type_constant_substitutions(encoder, require, &mut substitutions);
    }
    if substitutions.is_empty() {
        return false;
    }

    let ensure = ensure.substitute(&substitutions);
    let return_expr = return_expr.substitute(&substitutions);
    let requires = requires
        .iter()
        .map(|require| require.substitute(&substitutions))
        .collect::<Vec<_>>();
    result_postcondition_matches_return_expr(&ensure, Some(&return_expr), &requires)
}

fn collect_encoder_type_constant_substitutions(
    encoder: &AYEncoder,
    expr: &PureExpr,
    substitutions: &mut HashMap<String, PureExpr>,
) {
    expr.for_each_recursive(|node| {
        let PureExpr::Var(name, _) = node else {
            return;
        };
        if let Some(value) = encoder.type_constant_cloned(name) {
            substitutions.entry(name.clone()).or_insert(value);
        }
    });
}

fn requirement_includes_ensure(requires: &[PureExpr], ensure: &PureExpr) -> bool {
    requires
        .iter()
        .any(|require| requirement_expr_includes_ensure(require, ensure))
}

/// Exact, explicitly typed Seq law used by iterator `produces` contracts:
///
/// `a.ext_eq(b.concat(c))  ==>  a.len() == b.len() + c.len()`.
///
/// This matcher is intentionally narrower than the encoder's general
/// extensional-equality support. It accepts only explicit `Seq` operands and
/// requires the postcondition to reuse the exact three operands. That makes
/// the discharge independent of the quantified Array-backed Seq model while
/// keeping arbitrary `ext_eq`, aliased operands, and non-Seq methods on the
/// normal solver path.
fn seq_ext_eq_concat_length_conservation_follows_requires(
    ensure: &PureExpr,
    requires: &[PureExpr],
) -> bool {
    let Some((ensure_seq, ensure_left, ensure_right)) = seq_concat_length_equality_parts(ensure)
    else {
        return false;
    };

    requires.iter().any(|require| {
        requirement_ext_eq_concat_parts(require).is_some_and(
            |(required_seq, required_left, required_right)| {
                same_expr(ensure_seq, required_seq)
                    && ((same_expr(ensure_left, required_left)
                        && same_expr(ensure_right, required_right))
                        || (same_expr(ensure_left, required_right)
                            && same_expr(ensure_right, required_left)))
            },
        )
    })
}

/// Exact non-negativity corollary for the same explicitly typed Seq law:
///
/// `a.ext_eq(b.concat(c))  ==>  b.len() <= a.len()`.
///
/// Sequence lengths are non-negative, so this is the conservation equality
/// above with `c.len() >= 0`. As with the equality matcher, no aliases or
/// inferred/non-Seq method meanings are admitted.
fn seq_ext_eq_concat_left_length_bound_follows_requires(
    ensure: &PureExpr,
    requires: &[PureExpr],
) -> bool {
    let Some((ensure_left, ensure_seq)) = seq_length_le_parts(ensure) else {
        return false;
    };
    requires.iter().any(|require| {
        requirement_ext_eq_concat_parts(require).is_some_and(|(required_seq, required_left, _)| {
            same_expr(ensure_seq, required_seq) && same_expr(ensure_left, required_left)
        })
    })
}

fn seq_length_le_parts(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(left, op, right) = expr else {
        return None;
    };
    match op {
        BinOp::Le => Some((
            explicit_seq_len_receiver(left)?,
            explicit_seq_len_receiver(right)?,
        )),
        BinOp::Ge => Some((
            explicit_seq_len_receiver(right)?,
            explicit_seq_len_receiver(left)?,
        )),
        _ => None,
    }
}

fn requirement_ext_eq_concat_parts(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr, &PureExpr)> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    if method != "ext_eq" || !is_explicit_seq_operand(receiver) {
        return None;
    }
    let [other] = args.as_slice() else {
        return None;
    };
    let PureExpr::MethodCall {
        receiver: left,
        method,
        args,
    } = other
    else {
        return None;
    };
    if method != "concat" || !is_explicit_seq_operand(left) {
        return None;
    }
    let [right] = args.as_slice() else {
        return None;
    };
    is_explicit_seq_operand(right).then_some((receiver, left, right))
}

fn seq_concat_length_equality_parts(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr, &PureExpr)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return None;
    };
    seq_len_equals_sum_parts(left, right).or_else(|| seq_len_equals_sum_parts(right, left))
}

fn seq_len_equals_sum_parts<'a>(
    len_expr: &'a PureExpr,
    sum_expr: &'a PureExpr,
) -> Option<(&'a PureExpr, &'a PureExpr, &'a PureExpr)> {
    let seq = explicit_seq_len_receiver(len_expr)?;
    let PureExpr::BinOp(left, BinOp::Add, right) = sum_expr else {
        return None;
    };
    Some((
        seq,
        explicit_seq_len_receiver(left)?,
        explicit_seq_len_receiver(right)?,
    ))
}

fn explicit_seq_len_receiver(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    (method == "len" && args.is_empty() && is_explicit_seq_operand(receiver))
        .then_some(receiver.as_ref())
}

fn is_explicit_seq_operand(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(_, Some(trust_wp_core::formula::ExprSort::Seq)) => true,
        PureExpr::View(inner) => matches!(
            inner.as_ref(),
            PureExpr::Var(_, Some(trust_wp_core::formula::ExprSort::Seq))
        ),
        _ => false,
    }
}

fn requirement_expr_includes_ensure(require: &PureExpr, ensure: &PureExpr) -> bool {
    if same_expr(require, ensure) {
        return true;
    }
    match require {
        PureExpr::BinOp(left, BinOp::And, right) => {
            requirement_expr_includes_ensure(left, ensure)
                || requirement_expr_includes_ensure(right, ensure)
        }
        _ => false,
    }
}

fn prove_verified_obligation_with_solver(
    encoder: &mut AYEncoder,
    obligation_index: usize,
    ensure: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> Result<ResolveContinuation, EncodingError> {
    // Goal-side sort-coercion guard (#knights_tour): snapshot the unsoundness
    // counters before the negated-goal encode so a `SortCoercionBridge` fired
    // WHILE ENCODING THE GOAL can be detected. A coerced goal ranges over
    // fresh unconstrained constants, so any sat model for it is meaningless as
    // a counterexample and must not be accepted as `Failed`.
    let goal_coercion_baseline = unsoundness::snapshot();
    let negated_ensure = catch_verification_phase_ay_panics(
        "encode_negated_ensure",
        AssertUnwindSafe(|| {
            encode_negated_postcondition(encoder, ensure, ctx.logic_fns, ctx.return_expr)
        }),
    )?;
    let goal_encode_coerced =
        super::super::solver_tail::negated_goal_encode_introduced_sort_coercion(
            &goal_coercion_baseline,
        );
    super::assert_ground_tuple_destructor_instances(encoder, ctx.requires)?;
    catch_verification_phase_ay_panics(
        "assert_eager_ground_fn_mut_law",
        AssertUnwindSafe(|| encoder.assert_eager_fn_mut_ground_instantiation(ensure)),
    )?;
    catch_verification_phase_ay_panics(
        "assert_eager_ground_fn_once_law",
        AssertUnwindSafe(|| encoder.assert_eager_fn_once_ground_instantiation(ensure)),
    )?;

    let cont = catch_verification_phase_ay_panics(
        "verify_obligation_tail",
        AssertUnwindSafe(|| {
            super::super::solver_tail::verify_negated_obligation_slice(
                encoder,
                negated_ensure,
                ctx,
                AliasConstraintMode::ByValue,
                obligation_index,
            )
        }),
    )?;
    if goal_encode_coerced {
        return Ok(
            super::super::solver_tail::demote_sort_coerced_goal_counterexample(
                cont,
                obligation_index,
            ),
        );
    }
    Ok(cont)
}

fn type_invariant_postcondition_prechecked(
    ensure: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> bool {
    matches!(
        super::precheck_type_invariant_postconditions(
            ctx.requires,
            std::slice::from_ref(ensure),
            ctx.return_expr,
            ctx.type_invariants,
            ctx.logic_fns,
        ),
        Some(VerificationResult::Verified(_))
    )
}

fn prove_prechecked_literal_false_obligation_with_solver(
    _encoder: &mut AYEncoder,
    _obligation_index: usize,
    _ctx: &ObligationSliceContext<'_>,
) -> Result<ResolveContinuation, EncodingError> {
    // This helper asserts `false` in a FRESH encoder and returns the trivial
    // UNSAT as evidence: it proves `false ⊨ anything` and checks nothing about
    // the obligation. It is only ever a re-packaging of a structural
    // precheck's decision, so it must never be the evidence for a slice a
    // refutation shape has already refuted.
    if let Some(shape) = slice_refutation_shape() {
        return Ok(ResolveContinuation::Continue(
            structural_accept_withheld_after_shape(shape),
        ));
    }
    let result = super::super::solver_tail::prove_prechecked_literal_false_with_solver_evidence();
    Ok(ResolveContinuation::Continue(result))
}

pub(in crate::verify) fn prove_implication_false_guard_with_solver(
    encoder: &mut AYEncoder,
    obligation_index: usize,
    ensure: &PureExpr,
    requires: &[PureExpr],
) -> Result<Option<ResolveContinuation>, EncodingError> {
    let Some(guard) = implication_false_guard_candidate(ensure, requires) else {
        return Ok(None);
    };

    encoder.push_scope()?;
    let guard_term = encoder.encode_pure(guard)?;
    // The guard is the goal side of this refutation (guard ∧ base UNSAT ⇒ the
    // implication holds); never classify it as an encoder axiom.
    encoder.with_goal_assertions(|encoder| encoder.assert_term(guard_term));

    let original_timeout = encoder.solver().timeout();
    let probe_timeout = Duration::from_millis(500);
    let effective_probe = match original_timeout {
        Some(orig) if orig <= probe_timeout => orig,
        _ => probe_timeout,
    };
    encoder.set_timeout(Some(effective_probe));
    let goal_label_prefix = format!("__trust_wp_false_implication_guard_slice_{obligation_index}");
    let result =
        encoder.with_negated_goal_label_prefix(goal_label_prefix, |encoder| encoder.check_sat());
    encoder.set_timeout(original_timeout);

    let verified = matches!(result, ay_dpll::api::SolveResult::Unsat(_))
        && encoder.last_solve_evidence().is_some_and(|evidence| {
            evidence.accepted_for_consumer && solve_evidence_result_is_unsat(&evidence.result)
        });

    // Attach the refutation's strict proof authority while the guard is still
    // scoped. The guard solve above is a REAL solve on the live incremental
    // encoder, which runs with `set_produce_proofs(false)` by design, so
    // without this replay the arm would return a certificate-free
    // `Verified(None)` for an UNSAT it had genuinely proved — and the
    // mandatory authority boundary would demote it to `Unknown(ProofTrusted)`.
    // The isolated strict replay is the attachment the encoder constructor's
    // comment names, and it is the same helper the loop lane uses after an
    // accepted loop UNSAT.
    //
    // Order matters: `pop_scope` removes the guard assertion, so the replay
    // must run first or it would re-solve a different stack. Fail-closed —
    // `authorize_current_stack_unsat_with_strict_proof` returns `None` unless
    // the identical stack is again UNSAT with a fully verified, trust-free,
    // hole-free certificate, leaving exactly the previous `Verified(None)`.
    // `verified` still decides acceptance; this only stops an accepted verdict
    // from discarding its own evidence.
    let proof_summary = if verified {
        encoder.authorize_current_stack_unsat_with_strict_proof()
    } else {
        None
    };

    encoder.pop_scope()?;

    Ok(
        verified.then_some(ResolveContinuation::Continue(VerificationResult::Verified(
            proof_summary,
        ))),
    )
}

pub(in crate::verify) fn implication_false_guard_candidate<'a>(
    ensure: &'a PureExpr,
    requires: &[PureExpr],
) -> Option<&'a PureExpr> {
    let PureExpr::BinOp(guard, BinOp::Implies, _) = ensure else {
        return None;
    };
    len_equality_guard_contradicts_requirements(guard, requires).then_some(guard)
}

fn len_equality_guard_contradicts_requirements(guard: &PureExpr, requires: &[PureExpr]) -> bool {
    let Some((seq, value)) = len_equality_to_int_value(guard) else {
        return false;
    };
    sequence_lasso_requirement_conjuncts(requires)
        .iter()
        .any(|require| {
            len_requirement_lower_bound(require, seq).is_some_and(|lower| lower > value)
                || len_requirement_upper_bound(require, seq).is_some_and(|upper| upper < value)
        })
}

fn len_equality_to_int_value(expr: &PureExpr) -> Option<(&PureExpr, i64)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return None;
    };
    match (len_receiver(left), right.as_ref()) {
        (Some(receiver), PureExpr::Int(value)) => Some((receiver, *value)),
        _ => match (left.as_ref(), len_receiver(right)) {
            (PureExpr::Int(value), Some(receiver)) => Some((receiver, *value)),
            _ => None,
        },
    }
}

fn len_requirement_lower_bound(require: &PureExpr, seq: &PureExpr) -> Option<i64> {
    let PureExpr::BinOp(left, op, right) = require else {
        return None;
    };
    match op {
        BinOp::Gt if is_len_of(left, seq) => {
            int_value(right).and_then(|value| value.checked_add(1))
        }
        BinOp::Ge if is_len_of(left, seq) => int_value(right),
        BinOp::Lt if is_len_of(right, seq) => {
            int_value(left).and_then(|value| value.checked_add(1))
        }
        BinOp::Le if is_len_of(right, seq) => int_value(left),
        _ => None,
    }
}

fn len_requirement_upper_bound(require: &PureExpr, seq: &PureExpr) -> Option<i64> {
    let PureExpr::BinOp(left, op, right) = require else {
        return None;
    };
    match op {
        BinOp::Lt if is_len_of(left, seq) => {
            int_value(right).and_then(|value| value.checked_sub(1))
        }
        BinOp::Le if is_len_of(left, seq) => int_value(right),
        BinOp::Gt if is_len_of(right, seq) => {
            int_value(left).and_then(|value| value.checked_sub(1))
        }
        BinOp::Ge if is_len_of(right, seq) => int_value(left),
        _ => None,
    }
}

fn int_value(expr: &PureExpr) -> Option<i64> {
    match expr {
        PureExpr::Int(value) => Some(*value),
        _ => None,
    }
}

fn solve_evidence_result_is_unsat(result: &str) -> bool {
    result.eq_ignore_ascii_case("unsat")
        || result
            .strip_prefix("Unsat")
            .is_some_and(|suffix| suffix.is_empty() || suffix.starts_with('('))
}

fn result_equality_follows_from_context_fact(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    facts: &[PureExpr],
) -> bool {
    let Some(return_expr) = return_expr.map(strip_let_assume) else {
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
    let required = PureExpr::BinOp(
        Arc::new(return_expr.clone()),
        BinOp::Eq,
        Arc::new(expected.clone()),
    );
    let fact_refs: Vec<&PureExpr> = facts.iter().collect();
    facts
        .iter()
        .any(|fact| fact_implies_expr(fact, &required, &fact_refs, 0))
}

fn rewrite_tuple_getters_from_requirements(ensure: &PureExpr, requires: &[PureExpr]) -> PureExpr {
    let mut tuple_bindings = HashMap::new();
    for require in requires {
        collect_tuple_constructor_bindings(require, &mut tuple_bindings);
    }
    if tuple_bindings.is_empty() {
        return ensure.clone();
    }
    rewrite_tuple_getters(ensure, &tuple_bindings)
}

fn collect_tuple_constructor_bindings(
    expr: &PureExpr,
    bindings: &mut HashMap<String, Vec<PureExpr>>,
) {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_tuple_constructor_bindings(left, bindings);
            collect_tuple_constructor_bindings(right, bindings);
        }
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            collect_tuple_constructor_binding_side(left, right, bindings);
            collect_tuple_constructor_binding_side(right, left, bindings);
        }
        _ => {}
    }
}

fn collect_tuple_constructor_binding_side(
    target: &PureExpr,
    value: &PureExpr,
    bindings: &mut HashMap<String, Vec<PureExpr>>,
) {
    let PureExpr::Var(target_name, _) = target else {
        return;
    };
    let PureExpr::LogicFnCall { name, args } = value else {
        return;
    };
    if tuple_logic_fn_arity(name) != Some(args.len()) {
        return;
    }
    bindings.insert(target_name.clone(), args.clone());
}

fn rewrite_tuple_getters(expr: &PureExpr, bindings: &HashMap<String, Vec<PureExpr>>) -> PureExpr {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            if let Some(index) = tuple_field_logic_fn_index(name) {
                if let [PureExpr::Var(receiver, _)] = args.as_slice() {
                    if let Some(fields) =
                        bindings.get(receiver).and_then(|fields| fields.get(index))
                    {
                        return fields.clone();
                    }
                }
            }
            PureExpr::LogicFnCall {
                name: name.clone(),
                args: args
                    .iter()
                    .map(|arg| rewrite_tuple_getters(arg, bindings))
                    .collect(),
            }
        }
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(rewrite_tuple_getters(left, bindings)),
            *op,
            Arc::new(rewrite_tuple_getters(right, bindings)),
        ),
        PureExpr::UnOp(op, inner) => {
            PureExpr::UnOp(*op, Arc::new(rewrite_tuple_getters(inner, bindings)))
        }
        PureExpr::Ite(cond, then_branch, else_branch) => PureExpr::Ite(
            Arc::new(rewrite_tuple_getters(cond, bindings)),
            Arc::new(rewrite_tuple_getters(then_branch, bindings)),
            Arc::new(rewrite_tuple_getters(else_branch, bindings)),
        ),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(rewrite_tuple_getters(receiver, bindings)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| rewrite_tuple_getters(arg, bindings))
                .collect(),
        },
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(rewrite_tuple_getters(inner, bindings))),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(rewrite_tuple_getters(inner, bindings))),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(rewrite_tuple_getters(inner, bindings))),
        PureExpr::View(inner) => PureExpr::View(Arc::new(rewrite_tuple_getters(inner, bindings))),
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::new(rewrite_tuple_getters(value, bindings)),
            body: Arc::new(rewrite_tuple_getters(body, bindings)),
        },
        PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
            assumption: Arc::new(rewrite_tuple_getters(assumption, bindings)),
            body: Arc::new(rewrite_tuple_getters(body, bindings)),
        },
        PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
            obligation: Arc::new(rewrite_tuple_getters(obligation, bindings)),
            body: Arc::new(rewrite_tuple_getters(body, bindings)),
        },
        other => other.clone(),
    }
}

fn result_match_postcondition_follows_return_branches(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    requires: &[PureExpr],
) -> bool {
    let Some((ok_payload, err_payload)) = return_expr.and_then(return_ok_err_payloads) else {
        return false;
    };
    result_match_postcondition_follows_payloads(ensure, ok_payload, err_payload, requires)
}

/// Certify the extracted `match self { Ok(..) => Ok(..), Err(..) => Err(..) }`
/// result shape against its tuple-match postcondition.
///
/// Unlike the ITE routing helper above, this requires the return match to
/// scrutinize the exact enum value named by the postcondition, cover exactly
/// the `Ok` and `Err` constructors, and preserve each constructor.  Replacing
/// a branch payload with the corresponding `self.0` projection then reduces
/// both postcondition arms to an authenticated requirement or reflexive
/// equality.  The shape is therefore a finite structural proof, not merely a
/// hint that sends a quantified datatype VC to the solver.
fn result_constructor_match_postcondition_follows_return_branches(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    requires: &[PureExpr],
) -> bool {
    let Some((self_expr, _)) = result_tuple_match_parts(ensure) else {
        return false;
    };
    let Some((ok_constructor, err_constructor)) = result_tuple_match_constructor_families(ensure)
    else {
        return false;
    };
    let Some((ok_payload, err_payload)) = return_expr.and_then(|expr| {
        constructor_match_ok_err_payloads(expr, self_expr, &ok_constructor, &err_constructor)
    }) else {
        return false;
    };
    result_match_postcondition_follows_payloads(ensure, &ok_payload, &err_payload, requires)
}

fn result_match_postcondition_follows_payloads(
    ensure: &PureExpr,
    ok_payload: &PureExpr,
    err_payload: &PureExpr,
    requires: &[PureExpr],
) -> bool {
    let Some((self_expr, arms)) = result_tuple_match_parts(ensure) else {
        return false;
    };
    let Some(self_payload) = enum_first_payload_projection(self_expr) else {
        return false;
    };

    let mut saw_ok = false;
    let mut saw_err = false;
    let mut saw_wildcard_false = false;
    for arm in arms {
        match &arm.pattern {
            Pattern::Tuple(patterns) if patterns.len() == 2 => {
                let Some((self_ctor, self_binding)) = constructor_binding(&patterns[0]) else {
                    return false;
                };
                let Some((result_ctor, result_binding)) = constructor_binding(&patterns[1]) else {
                    return false;
                };
                if self_ctor != result_ctor {
                    return false;
                }
                match self_ctor {
                    "Ok" => {
                        if !method_postcondition_required_for_arm(
                            &arm.body,
                            self_binding,
                            result_binding,
                            &self_payload,
                            ok_payload,
                            requires,
                        ) && !copied_mut_ref_arm_matches(
                            &arm.body,
                            self_binding,
                            result_binding,
                            &self_payload,
                            ok_payload,
                        ) {
                            return false;
                        }
                        saw_ok = true;
                    }
                    "Err" => {
                        if !equality_arm_matches_same_payload(
                            &arm.body,
                            self_binding,
                            result_binding,
                            &self_payload,
                            err_payload,
                        ) {
                            return false;
                        }
                        saw_err = true;
                    }
                    _ => return false,
                }
            }
            Pattern::Wildcard if matches!(arm.body, PureExpr::Bool(false)) => {
                saw_wildcard_false = true;
            }
            _ => return false,
        }
    }

    saw_ok && saw_err && saw_wildcard_false
}

fn result_tuple_match_parts(ensure: &PureExpr) -> Option<(&PureExpr, &[MatchArm])> {
    let PureExpr::Match { scrutinee, arms } = ensure else {
        return None;
    };
    if arms.len() != 3 {
        return None;
    }

    let PureExpr::LogicFnCall { name, args } = scrutinee.as_ref() else {
        return None;
    };
    if tuple_logic_fn_arity(name) != Some(2) || args.len() != 2 {
        return None;
    }
    let self_expr = &args[0];
    if !matches!(&args[1], PureExpr::Var(name, _) if name == "result") {
        return None;
    }
    Some((self_expr, arms))
}

fn result_tuple_match_constructor_families(ensure: &PureExpr) -> Option<(String, String)> {
    let (_, arms) = result_tuple_match_parts(ensure)?;
    let mut ok_constructor = None;
    let mut err_constructor = None;
    for arm in arms {
        let Pattern::Tuple(patterns) = &arm.pattern else {
            continue;
        };
        let [Pattern::Constructor {
            name: self_name, ..
        }, Pattern::Constructor {
            name: result_name, ..
        }] = patterns.as_slice()
        else {
            return None;
        };
        if self_name != result_name {
            return None;
        }
        let slot = match short_constructor_name(self_name) {
            "Ok" => &mut ok_constructor,
            "Err" => &mut err_constructor,
            _ => return None,
        };
        if slot.replace(self_name.clone()).is_some() {
            return None;
        }
    }
    let ok_constructor = ok_constructor?;
    let err_constructor = err_constructor?;
    let ok_family = ok_constructor.strip_suffix(short_constructor_name(&ok_constructor))?;
    let err_family = err_constructor.strip_suffix(short_constructor_name(&err_constructor))?;
    (ok_family == err_family).then_some((ok_constructor, err_constructor))
}

fn result_match_over_option_ite_follows_selected_branch(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    requires: &[PureExpr],
) -> bool {
    let PureExpr::Match { scrutinee, arms } = ensure else {
        return false;
    };
    if !matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == "result") {
        return false;
    }
    let Some((selected_ctor, selected_payload, branch_assumptions)) =
        selected_option_ite_branch(return_expr, requires)
    else {
        return false;
    };
    let Some(arm_body) = selected_option_match_arm_body(arms, selected_ctor, selected_payload)
    else {
        return false;
    };
    let mut facts: Vec<&PureExpr> = requires.iter().collect();
    facts.extend(branch_assumptions);
    expr_follows_from_facts(&arm_body, &facts)
}

fn selected_option_ite_branch<'a>(
    return_expr: Option<&'a PureExpr>,
    requires: &[PureExpr],
) -> Option<(&'static str, Option<&'a PureExpr>, Vec<&'a PureExpr>)> {
    let PureExpr::Ite(condition, then_branch, else_branch) = strip_let_assume(return_expr?) else {
        return None;
    };
    let condition_value = expr_truth_from_facts(condition, &requires.iter().collect::<Vec<_>>())?;
    let selected = if condition_value {
        then_branch.as_ref()
    } else {
        else_branch.as_ref()
    };
    let (branch_body, assumptions) = peel_let_assume_assumptions(selected);
    let (ctor, payload) = option_constructor(branch_body)?;
    Some((ctor, payload, assumptions))
}

fn peel_let_assume_assumptions(mut expr: &PureExpr) -> (&PureExpr, Vec<&PureExpr>) {
    let mut assumptions = Vec::new();
    while let PureExpr::LetAssume { assumption, body } = expr {
        assumptions.push(assumption.as_ref());
        expr = body;
    }
    (expr, assumptions)
}

fn selected_option_match_arm_body(
    arms: &[MatchArm],
    selected_ctor: &str,
    selected_payload: Option<&PureExpr>,
) -> Option<PureExpr> {
    for arm in arms {
        let Pattern::Constructor { name, inner } = &arm.pattern else {
            continue;
        };
        if short_constructor_name(name) != selected_ctor {
            continue;
        }
        let mut substitutions = HashMap::new();
        match (selected_ctor, inner.as_deref(), selected_payload) {
            ("None", None, None) => {}
            ("Some", Some(Pattern::Binding(binding)), Some(payload)) => {
                substitutions.insert(binding.clone(), payload.clone());
            }
            ("Some", Some(Pattern::Wildcard), Some(_)) => {}
            _ => return None,
        }
        return Some(arm.body.substitute(&substitutions));
    }
    None
}

fn expr_follows_from_facts(expr: &PureExpr, facts: &[&PureExpr]) -> bool {
    if is_trivially_true_postcondition(expr) {
        return true;
    }
    if facts
        .iter()
        .any(|fact| fact_implies_expr(fact, expr, facts, 0))
    {
        return true;
    }
    matches!(expr_truth_from_facts(expr, facts), Some(true))
}

fn increment_by_one_postcondition_follows_from_facts(
    ensure: &PureExpr,
    facts: &[PureExpr],
) -> bool {
    let Some((target, value)) = equality_to_int_value(ensure) else {
        return false;
    };
    if value != 1 {
        return false;
    }

    let fact_refs: Vec<&PureExpr> = facts.iter().collect();
    facts.iter().any(|fact| {
        increment_fact_base_for_target(fact, target, &fact_refs, 0)
            .is_some_and(|base| fact_refs_imply_zero(&base, &fact_refs, 0))
    })
}

fn equality_to_int_value(expr: &PureExpr) -> Option<(&PureExpr, i64)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return None;
    };
    match (left.as_ref(), right.as_ref()) {
        (expr, PureExpr::Int(value)) => Some((expr, *value)),
        (PureExpr::Int(value), expr) => Some((expr, *value)),
        _ => None,
    }
}

fn increment_fact_base_for_target(
    fact: &PureExpr,
    target: &PureExpr,
    facts: &[&PureExpr],
    depth: usize,
) -> Option<PureExpr> {
    if depth > 4 {
        return None;
    }
    match fact {
        PureExpr::BinOp(left, BinOp::And, right) => {
            increment_fact_base_for_target(left, target, facts, depth + 1)
                .or_else(|| increment_fact_base_for_target(right, target, facts, depth + 1))
        }
        PureExpr::BinOp(antecedent, BinOp::Implies, consequent)
            if bool_condition_follows_from_facts(antecedent, facts, depth + 1) =>
        {
            increment_fact_base_for_target(consequent, target, facts, depth + 1)
        }
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            increment_base_from_equality(target, left, right)
                .or_else(|| increment_base_from_equality(target, right, left))
        }
        _ => None,
    }
}

fn increment_base_from_equality(
    target: &PureExpr,
    maybe_target: &PureExpr,
    maybe_add: &PureExpr,
) -> Option<PureExpr> {
    if !same_expr(target, maybe_target) {
        return None;
    }
    let PureExpr::BinOp(left, BinOp::Add, right) = maybe_add else {
        return None;
    };
    if matches!(right.as_ref(), PureExpr::Int(1)) {
        return Some(left.as_ref().clone());
    }
    if matches!(left.as_ref(), PureExpr::Int(1)) {
        return Some(right.as_ref().clone());
    }
    None
}

fn fact_refs_imply_zero(expr: &PureExpr, facts: &[&PureExpr], depth: usize) -> bool {
    if depth > 4 {
        return false;
    }
    facts
        .iter()
        .any(|fact| fact_contains_int_equality(fact, expr, 0, depth + 1))
}

fn fact_contains_int_equality(fact: &PureExpr, expr: &PureExpr, value: i64, depth: usize) -> bool {
    if depth > 4 {
        return false;
    }
    match fact {
        PureExpr::BinOp(left, BinOp::And, right) => {
            fact_contains_int_equality(left, expr, value, depth + 1)
                || fact_contains_int_equality(right, expr, value, depth + 1)
        }
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            (same_expr(left, expr) && matches!(right.as_ref(), PureExpr::Int(v) if *v == value))
                || (same_expr(right, expr)
                    && matches!(left.as_ref(), PureExpr::Int(v) if *v == value))
        }
        _ => false,
    }
}

fn bool_condition_follows_from_facts(expr: &PureExpr, facts: &[&PureExpr], depth: usize) -> bool {
    if depth > 4 {
        return false;
    }
    if expr_follows_from_facts_with_depth(expr, facts, depth + 1) {
        return true;
    }
    match expr {
        PureExpr::Var(name, _) => facts
            .iter()
            .any(|fact| bool_var_equivalence_follows_from_fact(fact, name, facts, depth + 1)),
        PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, inner) => {
            facts
                .iter()
                .any(|fact| quantified_fact_implies_expr(fact, expr, depth + 1))
                || facts.iter().any(|fact| {
                    same_expr(fact, expr) || fact_implies_expr(fact, expr, facts, depth + 1)
                })
                || facts.iter().any(|fact| {
                    matches!(
                        fact,
                        PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, fact_inner)
                            if same_expr(fact_inner, inner)
                    )
                })
        }
        _ => facts
            .iter()
            .any(|fact| quantified_fact_implies_expr(fact, expr, depth + 1)),
    }
}

fn bool_var_equivalence_follows_from_fact(
    fact: &PureExpr,
    name: &str,
    facts: &[&PureExpr],
    depth: usize,
) -> bool {
    if depth > 4 {
        return false;
    }
    match fact {
        PureExpr::BinOp(left, BinOp::And, right) => {
            bool_var_equivalence_follows_from_fact(left, name, facts, depth + 1)
                || bool_var_equivalence_follows_from_fact(right, name, facts, depth + 1)
        }
        PureExpr::BinOp(left, BinOp::Eq, right) => match (left.as_ref(), right.as_ref()) {
            (PureExpr::Var(var, _), rhs) if var == name => {
                bool_condition_follows_from_facts(rhs, facts, depth + 1)
            }
            (lhs, PureExpr::Var(var, _)) if var == name => {
                bool_condition_follows_from_facts(lhs, facts, depth + 1)
            }
            _ => false,
        },
        _ => false,
    }
}

fn quantified_fact_implies_expr(fact: &PureExpr, expr: &PureExpr, depth: usize) -> bool {
    if depth > 4 {
        return false;
    }
    match fact {
        PureExpr::BinOp(left, BinOp::And, right) => {
            quantified_fact_implies_expr(left, expr, depth + 1)
                || quantified_fact_implies_expr(right, expr, depth + 1)
        }
        PureExpr::Forall { var, body, .. } => {
            let mut binding = None;
            quantified_pattern_matches(body, expr, var, &mut binding)
        }
        _ => false,
    }
}

fn quantified_pattern_matches(
    pattern: &PureExpr,
    expr: &PureExpr,
    var: &str,
    binding: &mut Option<PureExpr>,
) -> bool {
    match pattern {
        PureExpr::Var(name, _) if name == var => bind_quantified_instance(binding, expr),
        PureExpr::Var(_, _) | PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => {
            same_expr(pattern, expr)
        }
        PureExpr::UnOp(op, inner) => matches!(
            expr,
            PureExpr::UnOp(expr_op, expr_inner)
                if op == expr_op && quantified_pattern_matches(inner, expr_inner, var, binding)
        ),
        PureExpr::BinOp(left, op, right) => matches!(
            expr,
            PureExpr::BinOp(expr_left, expr_op, expr_right)
                if op == expr_op
                    && quantified_pattern_matches(left, expr_left, var, binding)
                    && quantified_pattern_matches(right, expr_right, var, binding)
        ),
        PureExpr::LogicFnCall { name, args } => {
            let PureExpr::LogicFnCall {
                name: expr_name,
                args: expr_args,
            } = expr
            else {
                return false;
            };
            name == expr_name
                && args.len() == expr_args.len()
                && args
                    .iter()
                    .zip(expr_args.iter())
                    .all(|(pattern_arg, expr_arg)| {
                        quantified_pattern_matches(pattern_arg, expr_arg, var, binding)
                    })
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let PureExpr::MethodCall {
                receiver: expr_receiver,
                method: expr_method,
                args: expr_args,
            } = expr
            else {
                return false;
            };
            method == expr_method
                && args.len() == expr_args.len()
                && quantified_pattern_matches(receiver, expr_receiver, var, binding)
                && args
                    .iter()
                    .zip(expr_args.iter())
                    .all(|(pattern_arg, expr_arg)| {
                        quantified_pattern_matches(pattern_arg, expr_arg, var, binding)
                    })
        }
        PureExpr::Old(inner) => matches!(
            expr,
            PureExpr::Old(expr_inner)
                if quantified_pattern_matches(inner, expr_inner, var, binding)
        ),
        PureExpr::Deref(inner) => matches!(
            expr,
            PureExpr::Deref(expr_inner)
                if quantified_pattern_matches(inner, expr_inner, var, binding)
        ),
        PureExpr::Final(inner) => matches!(
            expr,
            PureExpr::Final(expr_inner)
                if quantified_pattern_matches(inner, expr_inner, var, binding)
        ),
        PureExpr::View(inner) => matches!(
            expr,
            PureExpr::View(expr_inner)
                if quantified_pattern_matches(inner, expr_inner, var, binding)
        ),
        _ => same_expr(pattern, expr),
    }
}

fn bind_quantified_instance(binding: &mut Option<PureExpr>, expr: &PureExpr) -> bool {
    match binding {
        Some(existing) => same_expr(existing, expr),
        None => {
            *binding = Some(expr.clone());
            true
        }
    }
}

fn expr_truth_from_facts(expr: &PureExpr, facts: &[&PureExpr]) -> Option<bool> {
    expr_truth_from_facts_with_depth(expr, facts, 0)
}

// The depth is the caller's, never restarted: a fact `(a == b) ==> c` sends an equality
// query through `fact_implies_expr` back to its own antecedent, so a walk that restarts
// its depth here recurses until the stack overflows.
fn expr_truth_from_facts_with_depth(
    expr: &PureExpr,
    facts: &[&PureExpr],
    depth: usize,
) -> Option<bool> {
    match expr {
        PureExpr::Bool(value) => Some(*value),
        PureExpr::Var(name, _) => facts
            .iter()
            .find_map(|fact| bool_var_value_from_fact(fact, name)),
        PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, inner) => {
            Some(!expr_truth_from_facts_with_depth(inner, facts, depth)?)
        }
        PureExpr::BinOp(_, BinOp::Eq, _) => {
            if facts
                .iter()
                .any(|fact| fact_implies_expr(fact, expr, facts, depth))
            {
                return Some(true);
            }
            if discriminant_equality_follows_from_constructor_fact(expr, facts, depth) {
                return Some(true);
            }
            None
        }
        _ => None,
    }
}

fn bool_var_value_from_fact(fact: &PureExpr, name: &str) -> Option<bool> {
    match fact {
        PureExpr::BinOp(left, BinOp::Eq, right) => match (left.as_ref(), right.as_ref()) {
            (PureExpr::Var(var, _), PureExpr::Bool(value)) if var == name => Some(*value),
            (PureExpr::Bool(value), PureExpr::Var(var, _)) if var == name => Some(*value),
            _ => None,
        },
        PureExpr::Var(var, _) if var == name => Some(true),
        _ => None,
    }
}

fn fact_implies_expr(fact: &PureExpr, expr: &PureExpr, facts: &[&PureExpr], depth: usize) -> bool {
    if crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(fact, expr) {
        return true;
    }
    if depth > 4 {
        return false;
    }
    match fact {
        PureExpr::BinOp(left, BinOp::And, right) => {
            fact_implies_expr(left, expr, facts, depth + 1)
                || fact_implies_expr(right, expr, facts, depth + 1)
        }
        PureExpr::BinOp(antecedent, BinOp::Implies, consequent) => {
            expr_follows_from_facts_with_depth(antecedent, facts, depth + 1)
                && fact_implies_expr(consequent, expr, facts, depth + 1)
        }
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            let PureExpr::BinOp(expr_left, BinOp::Eq, expr_right) = expr else {
                return false;
            };
            (same_expr(left, expr_left) && same_expr(right, expr_right))
                || (same_expr(left, expr_right) && same_expr(right, expr_left))
        }
        _ => false,
    }
}

fn expr_follows_from_facts_with_depth(expr: &PureExpr, facts: &[&PureExpr], depth: usize) -> bool {
    if is_trivially_true_postcondition(expr) {
        return true;
    }
    if depth > 4 {
        return false;
    }
    facts
        .iter()
        .any(|fact| fact_implies_expr(fact, expr, facts, depth + 1))
        || matches!(
            expr_truth_from_facts_with_depth(expr, facts, depth),
            Some(true)
        )
}

fn discriminant_equality_follows_from_constructor_fact(
    expr: &PureExpr,
    facts: &[&PureExpr],
    depth: usize,
) -> bool {
    let Some((receiver, value)) = option_discriminant_equality(expr) else {
        return false;
    };
    let Some(ctor) = known_option_constructor_for_expr(receiver, facts, depth) else {
        return false;
    };
    matches!((ctor, value), ("None", 0) | ("Some", 1))
}

fn known_option_constructor_for_expr<'a>(
    expr: &PureExpr,
    facts: &[&'a PureExpr],
    depth: usize,
) -> Option<&'static str> {
    if depth > 4 {
        return None;
    }
    for fact in facts {
        match fact {
            PureExpr::BinOp(left, BinOp::Eq, right) => {
                if same_expr(left, expr) {
                    if let Some((ctor, _)) = option_constructor(right) {
                        return Some(ctor);
                    }
                }
                if same_expr(right, expr) {
                    if let Some((ctor, _)) = option_constructor(left) {
                        return Some(ctor);
                    }
                }
            }
            PureExpr::BinOp(antecedent, BinOp::Implies, consequent)
                if expr_follows_from_facts_with_depth(antecedent, facts, depth + 1) =>
            {
                if let Some(ctor) = known_option_constructor_for_expr(
                    expr,
                    &std::iter::once(consequent.as_ref()).collect::<Vec<_>>(),
                    depth + 1,
                ) {
                    return Some(ctor);
                }
            }
            _ => {}
        }
    }
    None
}

fn option_constructor(expr: &PureExpr) -> Option<(&'static str, Option<&PureExpr>)> {
    match expr {
        PureExpr::Var(name, _) if short_constructor_name(name) == "None" => Some(("None", None)),
        PureExpr::LogicFnCall { name, args }
            if short_constructor_name(name) == "None" && args.is_empty() =>
        {
            Some(("None", None))
        }
        PureExpr::LogicFnCall { name, args }
            if short_constructor_name(name) == "Some" && args.len() == 1 =>
        {
            Some(("Some", Some(&args[0])))
        }
        _ => None,
    }
}

pub(in crate::verify) fn sequence_tail_reverse_push_front_index_proof_assert_matches(
    ensure: &PureExpr,
) -> bool {
    let PureExpr::BinOp(guard, BinOp::Implies, quantified) = ensure else {
        return false;
    };
    let Some(seq) = len_gt_zero_guard_sequence(guard) else {
        return false;
    };
    sequence_tail_reverse_push_front_index_quantifier_matches(quantified, seq)
}

pub(in crate::verify) fn sequence_tail_reverse_push_front_index_proof_assert_follows_requires(
    ensure: &PureExpr,
    requires: &[PureExpr],
) -> bool {
    let conjuncts = sequence_lasso_requirement_conjuncts(requires);
    conjuncts.iter().any(|require| {
        len_gt_zero_guard_sequence(require).is_some_and(|seq| {
            sequence_tail_reverse_push_front_index_quantifier_matches(ensure, seq)
                || conjuncts.iter().any(|alias_require| {
                    explicit_sequence_alias_for(seq, alias_require).is_some_and(|alias| {
                        sequence_tail_reverse_push_front_index_quantifier_matches(ensure, alias)
                    })
                })
        })
    })
}

fn sequence_lasso_requirement_conjuncts(requires: &[PureExpr]) -> Vec<&PureExpr> {
    let mut conjuncts = Vec::new();
    for require in requires {
        collect_sequence_lasso_requirement_conjuncts(require, &mut conjuncts);
    }
    conjuncts
}

fn collect_sequence_lasso_requirement_conjuncts<'a>(
    expr: &'a PureExpr,
    conjuncts: &mut Vec<&'a PureExpr>,
) {
    if let PureExpr::BinOp(left, BinOp::And, right) = expr {
        collect_sequence_lasso_requirement_conjuncts(left, conjuncts);
        collect_sequence_lasso_requirement_conjuncts(right, conjuncts);
    } else {
        conjuncts.push(expr);
    }
}

fn explicit_sequence_alias_for<'a>(
    guarded_seq: &PureExpr,
    require: &'a PureExpr,
) -> Option<&'a PureExpr> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = require else {
        return None;
    };
    if same_sequence_alias_base(left, guarded_seq) {
        return sequence_alias_candidate(right);
    }
    if same_sequence_alias_base(right, guarded_seq) {
        return sequence_alias_candidate(left);
    }
    None
}

fn same_sequence_alias_base(left: &PureExpr, right: &PureExpr) -> bool {
    same_expr(
        transparent_sequence_expr(left),
        transparent_sequence_expr(right),
    )
}

fn sequence_alias_candidate(expr: &PureExpr) -> Option<&PureExpr> {
    let candidate = transparent_sequence_expr(expr);
    matches!(candidate, PureExpr::Var(_, _)).then_some(candidate)
}

fn transparent_sequence_expr(mut expr: &PureExpr) -> &PureExpr {
    while let PureExpr::View(inner) = expr {
        expr = inner;
    }
    expr
}

fn sequence_tail_reverse_push_front_index_quantifier_matches(
    quantified: &PureExpr,
    seq: &PureExpr,
) -> bool {
    let PureExpr::Forall { var, body, .. } = quantified else {
        return false;
    };
    let PureExpr::BinOp(bounds, BinOp::Implies, equality) = body.as_ref() else {
        return false;
    };
    if !sequence_lasso_index_bounds(bounds, var, seq) {
        return false;
    }
    let PureExpr::BinOp(left, BinOp::Eq, right) = equality.as_ref() else {
        return false;
    };
    sequence_lasso_left_side(left, var, seq) && sequence_lasso_right_side(right, var, seq)
}

fn len_gt_zero_guard_sequence(expr: &PureExpr) -> Option<&PureExpr> {
    match expr {
        PureExpr::BinOp(left, BinOp::Gt, right) if is_int_value(right, 0) => {
            let seq = len_receiver(left)?;
            matches!(seq, PureExpr::Var(_, _)).then_some(seq)
        }
        PureExpr::BinOp(left, BinOp::Lt, right) if is_int_value(left, 0) => {
            let seq = len_receiver(right)?;
            matches!(seq, PureExpr::Var(_, _)).then_some(seq)
        }
        _ => None,
    }
}

fn sequence_lasso_index_bounds(bounds: &PureExpr, index_var: &str, seq: &PureExpr) -> bool {
    let PureExpr::BinOp(lower, BinOp::And, upper) = bounds else {
        return false;
    };
    is_zero_le_index_var(lower, index_var) && is_index_var_lt_seq_len(upper, index_var, seq)
}

fn sequence_lasso_left_side(expr: &PureExpr, index_var: &str, seq: &PureExpr) -> bool {
    let Some((push_front_expr, index_arg)) = method_call1(expr, "index_logic") else {
        return false;
    };
    if !is_var_named(index_arg, index_var) {
        return false;
    }
    let Some((reverse_subseq_expr, pushed_value)) = method_call1(push_front_expr, "push_front")
    else {
        return false;
    };
    if !is_seq_index_zero(pushed_value, seq) {
        return false;
    }
    let Some(subseq_expr) = method_call0(reverse_subseq_expr, "reverse") else {
        return false;
    };
    is_tail_subsequence_to_len(subseq_expr, seq)
}

fn sequence_lasso_right_side(expr: &PureExpr, index_var: &str, seq: &PureExpr) -> bool {
    let PureExpr::Ite(condition, then_branch, else_branch) = expr else {
        return false;
    };
    is_index_var_eq_zero(condition, index_var)
        && is_seq_index_zero(then_branch, seq)
        && is_reverse_index_previous(else_branch, index_var, seq)
}

fn is_tail_subsequence_to_len(expr: &PureExpr, seq: &PureExpr) -> bool {
    let Some((receiver, args)) = method_call_args(expr, "subsequence") else {
        return false;
    };
    let [from, to] = args else {
        return false;
    };
    same_expr(receiver, seq) && is_int_value(from, 1) && is_len_of(to, seq)
}

fn is_reverse_index_previous(expr: &PureExpr, index_var: &str, seq: &PureExpr) -> bool {
    let Some((reverse_expr, index_arg)) = method_call1(expr, "index_logic") else {
        return false;
    };
    let Some(reverse_receiver) = method_call0(reverse_expr, "reverse") else {
        return false;
    };
    same_expr(reverse_receiver, seq) && is_index_var_minus_one(index_arg, index_var)
}

fn is_seq_index_zero(expr: &PureExpr, seq: &PureExpr) -> bool {
    let Some((receiver, index_arg)) = method_call1(expr, "index_logic") else {
        return false;
    };
    same_expr(receiver, seq) && is_int_value(index_arg, 0)
}

fn is_zero_le_index_var(expr: &PureExpr, index_var: &str) -> bool {
    matches!(
        expr,
        PureExpr::BinOp(left, BinOp::Le, right)
            if is_int_value(left, 0) && is_var_named(right, index_var)
    )
}

fn is_index_var_lt_seq_len(expr: &PureExpr, index_var: &str, seq: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::BinOp(left, BinOp::Lt, right)
            if is_var_named(left, index_var) && is_len_of(right, seq)
    )
}

fn is_index_var_eq_zero(expr: &PureExpr, index_var: &str) -> bool {
    matches!(
        expr,
        PureExpr::BinOp(left, BinOp::Eq, right)
            if is_var_named(left, index_var) && is_int_value(right, 0)
    )
}

fn is_index_var_minus_one(expr: &PureExpr, index_var: &str) -> bool {
    matches!(
        expr,
        PureExpr::BinOp(left, BinOp::Sub, right)
            if is_var_named(left, index_var) && is_int_value(right, 1)
    )
}

fn is_len_of(expr: &PureExpr, seq: &PureExpr) -> bool {
    len_receiver(expr).is_some_and(|receiver| same_expr(receiver, seq))
}

fn len_receiver(expr: &PureExpr) -> Option<&PureExpr> {
    method_call0(expr, "len")
}

fn method_call0<'a>(expr: &'a PureExpr, expected_method: &str) -> Option<&'a PureExpr> {
    let (receiver, args) = method_call_args(expr, expected_method)?;
    args.is_empty().then_some(receiver)
}

fn method_call1<'a>(
    expr: &'a PureExpr,
    expected_method: &str,
) -> Option<(&'a PureExpr, &'a PureExpr)> {
    let (receiver, args) = method_call_args(expr, expected_method)?;
    let [arg] = args else {
        return None;
    };
    Some((receiver, arg))
}

fn method_call_args<'a>(
    expr: &'a PureExpr,
    expected_method: &str,
) -> Option<(&'a PureExpr, &'a [PureExpr])> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return None;
    };
    (method == expected_method).then_some((receiver.as_ref(), args.as_slice()))
}

fn is_int_value(expr: &PureExpr, value: i64) -> bool {
    matches!(expr, PureExpr::Int(actual) if *actual == value)
}

fn result_postcondition_matches_direct_logic_call_contract(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    requires: &[PureExpr],
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> bool {
    let (Some(PureExpr::LogicFnCall { name, args }), Some(logic_fns)) =
        (return_expr.map(strip_let_assume), logic_fns)
    else {
        return false;
    };
    let Some(logic_fn) = logic_fns
        .iter()
        .find(|logic_fn| logic_fn.name() == name && logic_fn.params().len() == args.len())
    else {
        return false;
    };

    let return_call = PureExpr::LogicFnCall {
        name: name.clone(),
        args: args.clone(),
    };
    let mut substitutions: HashMap<String, PureExpr> = logic_fn
        .params()
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    substitutions.insert("result".to_string(), return_call.clone());

    let facts: Vec<&PureExpr> = requires.iter().collect();
    if !logic_fn
        .requires()
        .iter()
        .map(|require| require.substitute(&substitutions))
        .all(|require| expr_follows_from_facts(&require, &facts))
    {
        return false;
    }

    let mut result_substitution = HashMap::new();
    result_substitution.insert("result".to_string(), return_call);
    let caller_goal = ensure.substitute(&result_substitution);
    logic_fn.ensures().iter().any(|callee_ensure| {
        let instantiated = callee_ensure.substitute(&substitutions);
        crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
            &caller_goal,
            &instantiated,
        )
    })
}

fn result_postcondition_matches_logic_call_ite_condition_contract(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    requires: &[PureExpr],
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> bool {
    let Some(PureExpr::Ite(condition, then_branch, _)) = return_expr.map(strip_let_assume) else {
        return false;
    };
    if !matches!(condition.as_ref(), PureExpr::LogicFnCall { .. }) {
        return false;
    }
    result_equality_matches_expr(ensure, then_branch)
        && logic_call_contract_implies_condition(condition, requires, logic_fns)
}

fn result_equality_matches_expr(ensure: &PureExpr, expected: &PureExpr) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = ensure else {
        return false;
    };
    let candidate = if matches!(left.as_ref(), PureExpr::Var(name, _) if name == "result") {
        right.as_ref()
    } else if matches!(right.as_ref(), PureExpr::Var(name, _) if name == "result") {
        left.as_ref()
    } else {
        return false;
    };
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(candidate, expected)
}

fn logic_call_contract_implies_condition(
    condition: &PureExpr,
    requires: &[PureExpr],
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
) -> bool {
    let (PureExpr::LogicFnCall { name, args }, Some(logic_fns)) = (condition, logic_fns) else {
        return false;
    };
    let Some(logic_fn) = logic_fns
        .iter()
        .find(|logic_fn| logic_fn.name() == name && logic_fn.params().len() == args.len())
    else {
        return false;
    };

    let mut substitutions: HashMap<String, PureExpr> = logic_fn
        .params()
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    substitutions.insert("result".to_string(), condition.clone());

    let facts: Vec<&PureExpr> = requires.iter().collect();
    if !logic_fn
        .requires()
        .iter()
        .map(|require| require.substitute(&substitutions))
        .all(|require| expr_follows_from_facts(&require, &facts))
    {
        return false;
    }

    logic_fn.ensures().iter().any(|ensure| {
        let instantiated = ensure.substitute(&substitutions);
        crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(
            &instantiated,
            condition,
        ) || bool_equality_to_true_matches(&instantiated, condition)
    })
}

fn bool_equality_to_true_matches(expr: &PureExpr, expected: &PureExpr) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return false;
    };
    (crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(left, expected)
        && matches!(right.as_ref(), PureExpr::Bool(true)))
        || (crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(right, expected)
            && matches!(left.as_ref(), PureExpr::Bool(true)))
}

fn take_first_mut_result_match_follows_split_first_source(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
    requires: &[PureExpr],
) -> bool {
    let Some(match_arms) = option_result_match_arms(ensure) else {
        return false;
    };
    if !take_first_mut_result_match_shape(
        match_arms.some_binding,
        match_arms.some_body,
        match_arms.none_body,
    ) {
        return false;
    }
    let Some(source) = take_first_mut_return_source(return_expr) else {
        return false;
    };
    let has_split_first_source = requires
        .iter()
        .any(|req| split_first_mut_source_fact_shape(req, source));
    let has_mem_take_empty_final = requires.iter().any(mem_take_self_final_empty_fact);
    has_split_first_source && has_mem_take_empty_final
}

struct OptionResultMatchArms<'a> {
    some_binding: &'a str,
    some_body: &'a PureExpr,
    none_body: &'a PureExpr,
}

fn option_result_match_arms(expr: &PureExpr) -> Option<OptionResultMatchArms<'_>> {
    let PureExpr::Match { scrutinee, arms } = expr else {
        return None;
    };
    if !is_var_named(scrutinee, "result") || arms.len() != 2 {
        return None;
    }

    let mut some_body = None;
    let mut some_binding = None;
    let mut none_body = None;
    for arm in arms {
        let Pattern::Constructor { name, inner } = &arm.pattern else {
            return None;
        };
        match short_constructor_name(name) {
            "Some" => {
                let Some(Pattern::Binding(binding)) = inner.as_deref() else {
                    return None;
                };
                some_binding = Some(binding.as_str());
                some_body = Some(&arm.body);
            }
            "None" => {
                if inner.is_some() {
                    return None;
                }
                none_body = Some(&arm.body);
            }
            _ => return None,
        }
    }

    Some(OptionResultMatchArms {
        some_binding: some_binding?,
        some_body: some_body?,
        none_body: none_body?,
    })
}

fn take_first_mut_result_match_shape(
    result_binding: &str,
    some_body: &PureExpr,
    none_body: &PureExpr,
) -> bool {
    let mut some_conjuncts = Vec::new();
    collect_conjuncts(some_body, &mut some_conjuncts);
    let has_r_current = has_eq(
        &some_conjuncts,
        &deref_expr(var_expr(result_binding)),
        &method_expr(
            current_self_ref_expr(),
            "index_logic",
            vec![PureExpr::Int(0)],
        ),
    );
    let has_r_final = has_eq(
        &some_conjuncts,
        &final_expr(var_expr(result_binding)),
        &method_expr(final_self_ref_expr(), "index_logic", vec![PureExpr::Int(0)]),
    );
    let has_current_len = has_ordered_binop(
        &some_conjuncts,
        &method_expr(current_self_seq_expr(), "len", vec![]),
        BinOp::Gt,
        &PureExpr::Int(0),
    );
    let has_final_len = has_ordered_binop(
        &some_conjuncts,
        &method_expr(final_self_seq_expr(), "len", vec![]),
        BinOp::Gt,
        &PureExpr::Int(0),
    );
    let has_current_tail = has_eq(
        &some_conjuncts,
        &view_expr(deref_expr(final_expr(var_expr("self_")))),
        &method_expr(current_self_seq_expr(), "tail", vec![]),
    );
    let has_final_tail = has_eq(
        &some_conjuncts,
        &view_expr(final_expr(final_expr(var_expr("self_")))),
        &method_expr(final_self_seq_expr(), "tail", vec![]),
    );

    let mut none_conjuncts = Vec::new();
    collect_conjuncts(none_body, &mut none_conjuncts);
    let has_current_written_empty = has_eq_to_seq_empty(
        &none_conjuncts,
        &view_expr(deref_expr(final_expr(var_expr("self_")))),
    );
    let has_current_self_empty = has_eq_to_seq_empty(&none_conjuncts, &current_self_seq_expr());
    let has_final_self_empty = has_eq_to_seq_empty(&none_conjuncts, &final_self_seq_expr());
    let has_final_written_empty = has_eq_to_seq_empty(
        &none_conjuncts,
        &view_expr(final_expr(final_expr(var_expr("self_")))),
    );

    has_r_current
        && has_r_final
        && has_current_len
        && has_final_len
        && has_current_tail
        && has_final_tail
        && has_current_written_empty
        && has_current_self_empty
        && has_final_self_empty
        && has_final_written_empty
}

fn take_first_mut_return_source(return_expr: Option<&PureExpr>) -> Option<&PureExpr> {
    let PureExpr::Ite(condition, then_branch, else_branch) = strip_let_assume(return_expr?) else {
        return None;
    };
    let (source, discriminant_value) = option_discriminant_equality(condition)?;
    let (none_branch, some_branch) =
        option_branches_for_discriminant_raw(discriminant_value, then_branch, else_branch)?;
    if !is_none_constructor(strip_let_assume(none_branch)) {
        return None;
    }

    let mut current = some_branch;
    let mut saw_self_writeback = false;
    while let PureExpr::LetAssume { assumption, body } = current {
        saw_self_writeback |= self_writeback_matches_split_rem(assumption, source);
        current = body;
    }
    if !saw_self_writeback {
        return None;
    }

    let payload = some_constructor_payload(current)?;
    let tuple_payload = tuple_get_expr(0, source.clone());
    is_tuple_get_of(payload, 0, &tuple_payload).then_some(source)
}

fn self_writeback_matches_split_rem(assumption: &PureExpr, source: &PureExpr) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = assumption else {
        return false;
    };
    let split_payload = tuple_get_expr(0, source.clone());
    let rem = tuple_get_expr(1, split_payload);
    (is_var_named(left, "self_") && same_expr(right, &rem))
        || (is_var_named(right, "self_") && same_expr(left, &rem))
}

fn split_first_mut_source_fact_shape(req: &PureExpr, source: &PureExpr) -> bool {
    let PureExpr::Match { scrutinee, arms } = req else {
        return false;
    };
    if !same_expr(scrutinee, source) || arms.len() != 2 {
        return false;
    }
    let Some(some_arm) = find_constructor_arm(arms, "Some") else {
        return false;
    };
    let Some(none_arm) = find_constructor_arm(arms, "None") else {
        return false;
    };
    let Some((first_binding, rem_binding)) = split_first_mut_some_tuple_pattern(&some_arm.pattern)
    else {
        return false;
    };

    split_first_mut_branch_bodies_shape(first_binding, rem_binding, &some_arm.body, &none_arm.body)
}

fn split_first_mut_some_tuple_pattern(pattern: &Pattern) -> Option<(&str, &str)> {
    let Pattern::Constructor { name, inner } = pattern else {
        return None;
    };
    if short_constructor_name(name) != "Some" {
        return None;
    }
    let Some(Pattern::Tuple(elements)) = inner.as_deref() else {
        return None;
    };
    let [Pattern::Binding(first), Pattern::Binding(rem)] = elements.as_slice() else {
        return None;
    };
    Some((first.as_str(), rem.as_str()))
}

fn split_first_mut_branch_bodies_shape(
    first_binding: &str,
    rem_binding: &str,
    some_body: &PureExpr,
    none_body: &PureExpr,
) -> bool {
    let mut some_conjuncts = Vec::new();
    collect_conjuncts(some_body, &mut some_conjuncts);
    let has_first_current = has_eq(
        &some_conjuncts,
        &deref_expr(var_expr(first_binding)),
        &method_expr(
            source_current_seq_expr(),
            "index_logic",
            vec![PureExpr::Int(0)],
        ),
    );
    let has_first_final = has_eq(
        &some_conjuncts,
        &final_expr(var_expr(first_binding)),
        &method_expr(
            source_final_seq_expr(),
            "index_logic",
            vec![PureExpr::Int(0)],
        ),
    );
    let has_rem_current = has_eq(
        &some_conjuncts,
        &view_expr(deref_expr(var_expr(rem_binding))),
        &method_expr(source_current_seq_expr(), "tail", vec![]),
    );
    let has_rem_final = has_eq(
        &some_conjuncts,
        &view_expr(final_expr(var_expr(rem_binding))),
        &method_expr(source_final_seq_expr(), "tail", vec![]),
    );
    let has_current_len = has_ordered_binop(
        &some_conjuncts,
        &method_expr(source_current_seq_expr(), "len", vec![]),
        BinOp::Gt,
        &PureExpr::Int(0),
    );
    let has_final_len = has_ordered_binop(
        &some_conjuncts,
        &method_expr(source_final_seq_expr(), "len", vec![]),
        BinOp::Gt,
        &PureExpr::Int(0),
    );

    let mut none_conjuncts = Vec::new();
    collect_conjuncts(none_body, &mut none_conjuncts);
    let has_current_empty_len = has_ordered_binop(
        &none_conjuncts,
        &method_expr(source_current_seq_expr(), "len", vec![]),
        BinOp::Eq,
        &PureExpr::Int(0),
    );
    let has_identity_final = has_eq(
        &none_conjuncts,
        &source_final_seq_expr(),
        &source_current_seq_expr(),
    );
    let has_empty = has_eq_to_seq_empty(&none_conjuncts, &source_current_seq_expr());

    has_first_current
        && has_first_final
        && has_rem_current
        && has_rem_final
        && has_current_len
        && has_final_len
        && has_current_empty_len
        && has_identity_final
        && has_empty
}

fn mem_take_self_final_empty_fact(expr: &PureExpr) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return false;
    };
    let final_self = view_expr(final_expr(var_expr("self_")));
    (same_expr(left, &final_self) && is_seq_empty_expr(right))
        || (same_expr(right, &final_self) && is_seq_empty_expr(left))
}

fn has_eq(conjuncts: &[&PureExpr], expected_left: &PureExpr, expected_right: &PureExpr) -> bool {
    conjuncts
        .iter()
        .any(|conjunct| eq_matches(conjunct, expected_left, expected_right))
}

fn has_eq_to_seq_empty(conjuncts: &[&PureExpr], expected_side: &PureExpr) -> bool {
    conjuncts.iter().any(|conjunct| {
        let PureExpr::BinOp(left, BinOp::Eq, right) = conjunct else {
            return false;
        };
        (same_expr(left, expected_side) && is_seq_empty_expr(right))
            || (same_expr(right, expected_side) && is_seq_empty_expr(left))
    })
}

fn eq_matches(expr: &PureExpr, expected_left: &PureExpr, expected_right: &PureExpr) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return false;
    };
    (same_expr(left, expected_left) && same_expr(right, expected_right))
        || (same_expr(left, expected_right) && same_expr(right, expected_left))
}

fn has_ordered_binop(
    conjuncts: &[&PureExpr],
    expected_left: &PureExpr,
    expected_op: BinOp,
    expected_right: &PureExpr,
) -> bool {
    conjuncts.iter().any(|conjunct| {
        let PureExpr::BinOp(left, op, right) = conjunct else {
            return false;
        };
        *op == expected_op && same_expr(left, expected_left) && same_expr(right, expected_right)
    })
}

fn source_current_seq_expr() -> PureExpr {
    view_expr(old_expr(deref_expr(var_expr("self_"))))
}

fn source_final_seq_expr() -> PureExpr {
    view_expr(final_expr(old_expr(deref_expr(var_expr("self_")))))
}

fn current_self_ref_expr() -> PureExpr {
    deref_expr(deref_expr(var_expr("self_")))
}

fn final_self_ref_expr() -> PureExpr {
    final_expr(deref_expr(var_expr("self_")))
}

fn current_self_seq_expr() -> PureExpr {
    view_expr(current_self_ref_expr())
}

fn final_self_seq_expr() -> PureExpr {
    view_expr(final_self_ref_expr())
}

fn method_expr(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::MethodCall {
        receiver: std::sync::Arc::new(receiver),
        method: method.to_string(),
        args,
    }
}

fn var_expr(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn deref_expr(expr: PureExpr) -> PureExpr {
    PureExpr::Deref(std::sync::Arc::new(expr))
}

fn final_expr(expr: PureExpr) -> PureExpr {
    PureExpr::Final(std::sync::Arc::new(expr))
}

fn old_expr(expr: PureExpr) -> PureExpr {
    PureExpr::Old(std::sync::Arc::new(expr))
}

fn view_expr(expr: PureExpr) -> PureExpr {
    PureExpr::View(std::sync::Arc::new(expr))
}

fn is_seq_empty_expr(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::LogicFnCall { name, args }
            if args.is_empty() && (name == "Seq::empty" || name.ends_with("Seq_P__P_empty"))
    )
}

fn is_none_constructor(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            short_constructor_name(name) == "None" && args.is_empty()
        }
        PureExpr::Var(name, _) => short_constructor_name(name) == "None",
        _ => false,
    }
}

fn some_constructor_payload(expr: &PureExpr) -> Option<&PureExpr> {
    match expr {
        PureExpr::LogicFnCall { name, args }
            if short_constructor_name(name) == "Some" && args.len() == 1 =>
        {
            Some(&args[0])
        }
        _ => None,
    }
}

/// Is this obligation exactly one instance of some visible logic function's
/// own `#[ensures]`, AT ARGUMENTS ITS `#[requires]` ADMITS?
///
/// The postcondition of a guarded logic function is proved only under that
/// function's precondition, so the fact a caller may use is the implication
/// `requires(args) => ensures(args)` — the shape the SMT spec axiom and the
/// Creusot oracle both emit. Handing over the bare conclusion here would be a
/// SECOND emitter of the same fact with its domain dropped: the grant and the
/// obligation would then sit in different environments, and an argument the
/// domain excludes would harvest a postcondition the body never proved (two
/// clauses of one such postcondition can be jointly unsatisfiable, which makes
/// every obligation in that proof context worthless).
///
/// So the domain travels with the grant: every `requires` clause, instantiated
/// at the SAME arguments, must be established in the environment this
/// obligation is discharged in. When it is not, this lane declines and the
/// obligation falls through to the solver, which has only the guarded axiom.
/// (`logic_fn_ensures_granted_outside_requires.rs`)
fn postcondition_is_logic_fn_spec_instance(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    requires: &[PureExpr],
) -> bool {
    let Some(logic_fns) = logic_fns else {
        return false;
    };
    ensure.any_recursive(|node| {
        let PureExpr::LogicFnCall { name, args } = node else {
            return false;
        };
        logic_fns.iter().any(|logic_fn| {
            if logic_fn.name() != name || logic_fn.params().len() != args.len() {
                return false;
            }
            if !logic_fn_spec_domain_holds(logic_fn, args, requires) {
                return false;
            }
            logic_fn.ensures().iter().any(|spec| {
                let instantiated = instantiate_logic_fn_spec(logic_fn, args, node, spec);
                same_expr(&instantiated, ensure)
            })
        })
    })
}

/// Does the logic function's declared domain hold at `args`, here?
///
/// `requires` clauses never mention `result`, so the instantiation is the
/// parameter substitution alone — the same substitution
/// [`instantiate_logic_fn_spec`] applies to the postcondition, which is what
/// keeps grant and obligation in one environment. A clause this layer cannot
/// establish is not assumed: it fails closed and the caller routes to the
/// solver. (`logic_fn_ensures_granted_outside_requires.rs`)
fn logic_fn_spec_domain_holds(
    logic_fn: &trust_wp_core::logic::LogicFnDef,
    args: &[PureExpr],
    requires: &[PureExpr],
) -> bool {
    if logic_fn.requires().is_empty() {
        return true;
    }
    let substitutions: HashMap<String, PureExpr> = logic_fn
        .params()
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    logic_fn.requires().iter().all(|require| {
        let instantiated = require.substitute(&substitutions);
        crate::verify::postcondition::expr_established_by_context(&instantiated, requires)
    })
}

fn instantiate_logic_fn_spec(
    logic_fn: &trust_wp_core::logic::LogicFnDef,
    args: &[PureExpr],
    result_expr: &PureExpr,
    spec: &PureExpr,
) -> PureExpr {
    let mut substitutions: HashMap<String, PureExpr> = logic_fn
        .params()
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    substitutions.insert("result".to_string(), result_expr.clone());
    spec.substitute(&substitutions)
}

fn return_ok_err_payloads(return_expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::Ite(_, then_branch, else_branch) = strip_let_assume(return_expr) else {
        return None;
    };
    let (then_ctor, then_payload) = constructor_payload(then_branch)?;
    let (else_ctor, else_payload) = constructor_payload(else_branch)?;
    match (then_ctor, else_ctor) {
        ("Ok", "Err") => Some((then_payload, else_payload)),
        ("Err", "Ok") => Some((else_payload, then_payload)),
        _ => None,
    }
}

fn constructor_match_ok_err_payloads(
    return_expr: &PureExpr,
    expected_scrutinee: &PureExpr,
    expected_ok_constructor: &str,
    expected_err_constructor: &str,
) -> Option<(PureExpr, PureExpr)> {
    let PureExpr::Match { scrutinee, arms } = strip_let_assume(return_expr) else {
        return None;
    };
    if arms.len() != 2 || scrutinee.as_ref() != expected_scrutinee {
        return None;
    }

    let self_payload = enum_first_payload_projection(expected_scrutinee)?;
    let mut ok_payload = None;
    let mut err_payload = None;
    for arm in arms {
        let Pattern::Constructor {
            name: input_constructor,
            inner: Some(input_pattern),
        } = &arm.pattern
        else {
            return None;
        };
        let Pattern::Binding(input_binding) = input_pattern.as_ref() else {
            return None;
        };
        let PureExpr::LogicFnCall {
            name: output_constructor,
            args: output_args,
        } = &arm.body
        else {
            return None;
        };
        let [output_payload] = output_args.as_slice() else {
            return None;
        };
        let expected_constructor = match short_constructor_name(input_constructor) {
            "Ok" => expected_ok_constructor,
            "Err" => expected_err_constructor,
            _ => return None,
        };
        if input_constructor != expected_constructor || output_constructor != expected_constructor {
            return None;
        }
        let normalized_payload = output_payload.substitute(&HashMap::from([(
            input_binding.clone(),
            self_payload.clone(),
        )]));
        let slot = match short_constructor_name(input_constructor) {
            "Ok" => &mut ok_payload,
            "Err" => &mut err_payload,
            _ => return None,
        };
        if slot.replace(normalized_payload).is_some() {
            return None;
        }
    }
    Some((ok_payload?, err_payload?))
}

fn constructor_payload(expr: &PureExpr) -> Option<(&'static str, &PureExpr)> {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return None;
    };
    let ctor = match short_constructor_name(name) {
        "Ok" => "Ok",
        "Err" => "Err",
        _ => return None,
    };
    (args.len() == 1).then_some((ctor, strip_let_assume(&args[0])))
}

fn constructor_binding(pattern: &Pattern) -> Option<(&'static str, &str)> {
    let Pattern::Constructor { name, inner } = pattern else {
        return None;
    };
    let ctor = match short_constructor_name(name) {
        "Ok" => "Ok",
        "Err" => "Err",
        _ => return None,
    };
    let Some(Pattern::Binding(binding)) = inner.as_deref() else {
        return None;
    };
    Some((ctor, binding.as_str()))
}

fn enum_first_payload_projection(expr: &PureExpr) -> Option<PureExpr> {
    let PureExpr::Var(name, _) = expr else {
        return None;
    };
    Some(PureExpr::Var(format!("{name}.0"), None))
}

fn method_postcondition_required_for_arm(
    body: &PureExpr,
    self_binding: &str,
    result_binding: &str,
    self_payload: &PureExpr,
    result_payload: &PureExpr,
    requires: &[PureExpr],
) -> bool {
    match body {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            if method != "postcondition"
                || !postcondition_arm_uses_bindings(args, self_binding, result_binding)
            {
                return false;
            }
            requires.iter().any(|req| {
                matches!(
                    req,
                    PureExpr::MethodCall {
                        receiver: req_receiver,
                        method: req_method,
                        args: req_args,
                    } if req_receiver.as_ref() == receiver.as_ref()
                        && req_method == method
                        && postcondition_requirement_uses_payloads(
                            req_args,
                            self_payload,
                            result_payload,
                        )
                )
            })
        }
        PureExpr::LogicFnCall { name, args } => {
            if !name.ends_with(".postcondition")
                || !postcondition_arm_uses_bindings(args, self_binding, result_binding)
            {
                return false;
            }
            requires.iter().any(|req| {
                matches!(
                    req,
                    PureExpr::LogicFnCall {
                        name: req_name,
                        args: req_args,
                    } if req_name == name
                        && postcondition_requirement_uses_payloads(
                            req_args,
                            self_payload,
                            result_payload,
                        )
                )
            })
        }
        _ => false,
    }
}

fn postcondition_arm_uses_bindings(
    args: &[PureExpr],
    self_binding: &str,
    result_binding: &str,
) -> bool {
    args.len() == 2
        && matches!(&args[0], PureExpr::Var(name, _) if name == self_binding)
        && matches!(&args[1], PureExpr::Var(name, _) if name == result_binding)
}

fn postcondition_requirement_uses_payloads(
    args: &[PureExpr],
    self_payload: &PureExpr,
    result_payload: &PureExpr,
) -> bool {
    args.len() == 2 && args[0] == *self_payload && args[1] == *result_payload
}

fn copied_mut_ref_arm_matches(
    body: &PureExpr,
    self_binding: &str,
    result_binding: &str,
    self_payload: &PureExpr,
    result_payload: &PureExpr,
) -> bool {
    let PureExpr::BinOp(left, BinOp::And, right) = body else {
        return false;
    };
    equality_arm_matches_deref_payload(
        left,
        self_binding,
        result_binding,
        self_payload,
        result_payload,
    ) && resolve_call_matches(right, self_binding)
}

fn equality_arm_matches_deref_payload(
    body: &PureExpr,
    self_binding: &str,
    result_binding: &str,
    self_payload: &PureExpr,
    result_payload: &PureExpr,
) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = body else {
        return false;
    };
    let matches_binding_shape = matches!(left.as_ref(), PureExpr::Var(name, _) if name == result_binding)
        && matches!(
            right.as_ref(),
            PureExpr::Deref(inner)
                if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == self_binding)
        );
    matches_binding_shape
        && same_expr_ignoring_var_sort(
            result_payload,
            &PureExpr::Deref(std::sync::Arc::new(self_payload.clone())),
        )
}

fn resolve_call_matches(expr: &PureExpr, self_binding: &str) -> bool {
    matches!(
        expr,
        PureExpr::LogicFnCall { name, args }
            if name == "resolve"
                && args.len() == 1
                && matches!(&args[0], PureExpr::Var(var, _) if var == self_binding)
    )
}

fn equality_arm_matches_same_payload(
    body: &PureExpr,
    self_binding: &str,
    result_binding: &str,
    self_payload: &PureExpr,
    result_payload: &PureExpr,
) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = body else {
        return false;
    };
    let lhs_rhs_match = matches!(left.as_ref(), PureExpr::Var(name, _) if name == self_binding)
        && matches!(right.as_ref(), PureExpr::Var(name, _) if name == result_binding);
    let rhs_lhs_match = matches!(left.as_ref(), PureExpr::Var(name, _) if name == result_binding)
        && matches!(right.as_ref(), PureExpr::Var(name, _) if name == self_binding);
    (lhs_rhs_match || rhs_lhs_match) && same_expr_ignoring_var_sort(self_payload, result_payload)
}

fn same_expr_ignoring_var_sort(left: &PureExpr, right: &PureExpr) -> bool {
    match (left, right) {
        (PureExpr::Var(left_name, _), PureExpr::Var(right_name, _)) => left_name == right_name,
        (PureExpr::Deref(left), PureExpr::Deref(right))
        | (PureExpr::Final(left), PureExpr::Final(right))
        | (PureExpr::Old(left), PureExpr::Old(right))
        | (PureExpr::View(left), PureExpr::View(right)) => same_expr_ignoring_var_sort(left, right),
        _ => left == right,
    }
}

fn final_borrow_option_field_selector_matches(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
) -> bool {
    let PureExpr::Match { scrutinee, arms } = ensure else {
        return false;
    };
    if arms.len() != 2 {
        return false;
    }
    let Some(return_expr) = return_expr.map(strip_let_assume) else {
        return false;
    };
    let PureExpr::Ite(cond, then_branch, else_branch) = return_expr else {
        return false;
    };

    let Some((cond_scrutinee, discr_value)) = option_discriminant_equality(cond) else {
        return false;
    };
    if !same_expr(scrutinee, cond_scrutinee) {
        return false;
    }

    let Some(base_name) = tuple_get_base_var(scrutinee, 0) else {
        return false;
    };

    let Some((none_branch, some_branch)) =
        option_branches_for_discriminant(discr_value, then_branch, else_branch)
    else {
        return false;
    };
    if !is_tuple_get_of_var(none_branch, 1, base_name) {
        return false;
    }
    if !is_tuple_get_of(some_branch, 0, scrutinee) {
        return false;
    }

    let Some(none_arm) = find_constructor_arm(arms, "None") else {
        return false;
    };
    if !result_eq_expr(&none_arm.body, none_branch) {
        return false;
    }

    let Some(some_arm) = find_constructor_arm(arms, "Some") else {
        return false;
    };
    some_exists_arm_matches(&some_arm.body, base_name)
}

fn final_borrow_result_field_selector_matches(
    ensure: &PureExpr,
    return_expr: Option<&PureExpr>,
) -> bool {
    let Some(return_expr) = return_expr.map(strip_let_assume) else {
        return false;
    };
    let PureExpr::Ite(cond, then_branch, else_branch) = return_expr else {
        return false;
    };

    let Some((cond_scrutinee, discr_value)) = option_discriminant_equality(cond) else {
        return false;
    };
    let Some((ok_branch, err_branch)) =
        result_branches_for_discriminant(discr_value, then_branch, else_branch)
    else {
        return false;
    };

    let Some((ok_base, err_base)) = result_selector_exists_bases(ensure) else {
        return false;
    };
    if !same_expr(&ok_base, &err_base) {
        return false;
    }

    let expected_scrutinee = PureExpr::Deref(std::sync::Arc::new(ok_base.clone()));
    same_expr(cond_scrutinee, &expected_scrutinee)
        && result_return_branch_matches(ok_branch, "Ok", &ok_base)
        && result_return_branch_matches(err_branch, "Err", &ok_base)
}

fn result_branches_for_discriminant<'a>(
    discr_value: i64,
    then_branch: &'a PureExpr,
    else_branch: &'a PureExpr,
) -> Option<(&'a PureExpr, &'a PureExpr)> {
    match discr_value {
        0 => Some((strip_let_assume(then_branch), strip_let_assume(else_branch))),
        1 => Some((strip_let_assume(else_branch), strip_let_assume(then_branch))),
        _ => None,
    }
}

fn result_selector_exists_bases(ensure: &PureExpr) -> Option<(PureExpr, PureExpr)> {
    let PureExpr::Exists { var, body, .. } = ensure else {
        return None;
    };
    let PureExpr::BinOp(left, BinOp::Or, right) = body.as_ref() else {
        return None;
    };

    let mut ok_base = result_selector_branch_base(left, "Ok", var);
    let mut err_base = result_selector_branch_base(left, "Err", var);
    collect_result_selector_nested_exists(right, &mut ok_base, &mut err_base);

    if ok_base.is_none() || err_base.is_none() {
        ok_base = result_selector_branch_base(right, "Ok", var);
        err_base = result_selector_branch_base(right, "Err", var);
        collect_result_selector_nested_exists(left, &mut ok_base, &mut err_base);
    }

    Some((ok_base?, err_base?))
}

fn collect_result_selector_nested_exists(
    expr: &PureExpr,
    ok_base: &mut Option<PureExpr>,
    err_base: &mut Option<PureExpr>,
) {
    let PureExpr::Exists { var, body, .. } = expr else {
        return;
    };
    if ok_base.is_none() {
        *ok_base = result_selector_branch_base(body, "Ok", var);
    }
    if err_base.is_none() {
        *err_base = result_selector_branch_base(body, "Err", var);
    }
}

fn result_selector_branch_base(expr: &PureExpr, ctor: &str, witness_var: &str) -> Option<PureExpr> {
    let mut has_current_payload = false;
    let mut has_final_payload = false;
    let mut has_result_payload = false;
    let mut base: Option<PureExpr> = None;

    let mut conjuncts = Vec::new();
    collect_conjuncts(expr, &mut conjuncts);
    for conjunct in conjuncts {
        if let Some(candidate) =
            result_wrapped_payload_eq(conjunct, ctor, witness_var, Wrapper::Deref)
        {
            merge_selector_base(&mut base, candidate)?;
            has_current_payload = true;
        }
        if let Some(candidate) =
            result_wrapped_payload_eq(conjunct, ctor, witness_var, Wrapper::Final)
        {
            merge_selector_base(&mut base, candidate)?;
            has_final_payload = true;
        }
        has_result_payload |= result_eq_constructor_var(conjunct, ctor, witness_var);
    }

    if has_current_payload && has_final_payload && has_result_payload {
        base
    } else {
        None
    }
}

fn merge_selector_base(base: &mut Option<PureExpr>, candidate: PureExpr) -> Option<()> {
    if let Some(existing) = base {
        same_expr(existing, &candidate).then_some(())
    } else {
        *base = Some(candidate);
        Some(())
    }
}

fn result_wrapped_payload_eq(
    conjunct: &PureExpr,
    ctor: &str,
    witness_var: &str,
    wrapper: Wrapper,
) -> Option<PureExpr> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = conjunct else {
        return None;
    };
    wrapped_payload_pair(left, right, ctor, witness_var, wrapper)
        .or_else(|| wrapped_payload_pair(right, left, ctor, witness_var, wrapper))
}

fn wrapped_payload_pair(
    lhs: &PureExpr,
    rhs: &PureExpr,
    ctor: &str,
    witness_var: &str,
    wrapper: Wrapper,
) -> Option<PureExpr> {
    let base = unwrap_wrapper(lhs, wrapper)?;
    is_constructor_of_wrapped_var(rhs, ctor, witness_var, wrapper).then(|| base.clone())
}

fn unwrap_wrapper(expr: &PureExpr, wrapper: Wrapper) -> Option<&PureExpr> {
    match (wrapper, expr) {
        (Wrapper::Deref, PureExpr::Deref(inner)) | (Wrapper::Final, PureExpr::Final(inner)) => {
            Some(inner.as_ref())
        }
        _ => None,
    }
}

fn is_constructor_of_wrapped_var(
    expr: &PureExpr,
    ctor: &str,
    witness_var: &str,
    wrapper: Wrapper,
) -> bool {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return false;
    };
    short_constructor_name(name) == ctor
        && args.len() == 1
        && unwrap_wrapper(&args[0], wrapper).is_some_and(|arg| is_var_named(arg, witness_var))
}

fn result_eq_constructor_var(expr: &PureExpr, ctor: &str, witness_var: &str) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return false;
    };
    (is_var_named(left, "result") && is_constructor_of_var(right, ctor, witness_var))
        || (is_var_named(right, "result") && is_constructor_of_var(left, ctor, witness_var))
}

fn is_constructor_of_var(expr: &PureExpr, ctor: &str, witness_var: &str) -> bool {
    matches!(
        expr,
        PureExpr::LogicFnCall { name, args }
            if short_constructor_name(name) == ctor
                && args.len() == 1
                && is_var_named(&args[0], witness_var)
    )
}

fn result_return_branch_matches(expr: &PureExpr, ctor: &str, base: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::LogicFnCall { name, args }
            if short_constructor_name(name) == ctor
                && args.len() == 1
                && is_tuple_get_of(&args[0], 0, base)
    )
}

fn strip_let_assume(expr: &PureExpr) -> &PureExpr {
    let mut current = expr;
    while let PureExpr::LetAssume { body, .. } = current {
        current = body;
    }
    current
}

fn option_discriminant_equality(expr: &PureExpr) -> Option<(&PureExpr, i64)> {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return None;
    };
    match (left.as_ref(), right.as_ref()) {
        (method, PureExpr::Int(value)) => discriminant_receiver(method).map(|r| (r, *value)),
        (PureExpr::Int(value), method) => discriminant_receiver(method).map(|r| (r, *value)),
        _ => None,
    }
}

fn discriminant_receiver(expr: &PureExpr) -> Option<&PureExpr> {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "discriminant" && args.is_empty() => Some(receiver),
        _ => None,
    }
}

fn option_branches_for_discriminant<'a>(
    discr_value: i64,
    then_branch: &'a PureExpr,
    else_branch: &'a PureExpr,
) -> Option<(&'a PureExpr, &'a PureExpr)> {
    match discr_value {
        0 => Some((strip_let_assume(then_branch), strip_let_assume(else_branch))),
        1 => Some((strip_let_assume(else_branch), strip_let_assume(then_branch))),
        _ => None,
    }
}

fn option_branches_for_discriminant_raw<'a>(
    discr_value: i64,
    then_branch: &'a PureExpr,
    else_branch: &'a PureExpr,
) -> Option<(&'a PureExpr, &'a PureExpr)> {
    match discr_value {
        0 => Some((then_branch, else_branch)),
        1 => Some((else_branch, then_branch)),
        _ => None,
    }
}

fn find_constructor_arm<'a>(arms: &'a [MatchArm], ctor: &str) -> Option<&'a MatchArm> {
    arms.iter().find(|arm| {
        matches!(
            &arm.pattern,
            Pattern::Constructor { name, .. } if short_constructor_name(name) == ctor
        )
    })
}

fn some_exists_arm_matches(expr: &PureExpr, base_name: &str) -> bool {
    let PureExpr::Exists { var, body, .. } = expr else {
        return false;
    };

    let mut has_result_eq = false;
    let mut has_current_payload = false;
    let mut has_final_payload = false;
    let mut conjuncts = Vec::new();
    collect_conjuncts(body, &mut conjuncts);
    for conjunct in conjuncts {
        has_result_eq |= result_eq_var(conjunct, var);
        has_current_payload |= option_payload_eq(
            conjunct,
            &field_of_wrapped_base(base_name, Wrapper::Deref),
            &wrapped_var(var, Wrapper::Deref),
        );
        has_final_payload |= option_payload_eq(
            conjunct,
            &field_of_wrapped_base(base_name, Wrapper::Final),
            &wrapped_var(var, Wrapper::Final),
        );
    }

    has_result_eq && has_current_payload && has_final_payload
}

fn collect_conjuncts<'a>(expr: &'a PureExpr, out: &mut Vec<&'a PureExpr>) {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_conjuncts(left, out);
            collect_conjuncts(right, out);
        }
        _ => out.push(expr),
    }
}

#[derive(Clone, Copy)]
enum Wrapper {
    Deref,
    Final,
}

fn field_of_wrapped_base(base_name: &str, wrapper: Wrapper) -> PureExpr {
    let base = PureExpr::Var(base_name.to_string(), None);
    let wrapped = match wrapper {
        Wrapper::Deref => PureExpr::Deref(std::sync::Arc::new(base)),
        Wrapper::Final => PureExpr::Final(std::sync::Arc::new(base)),
    };
    PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(0),
        args: vec![wrapped],
    }
}

fn wrapped_var(var: &str, wrapper: Wrapper) -> PureExpr {
    let var = PureExpr::Var(var.to_string(), None);
    match wrapper {
        Wrapper::Deref => PureExpr::Deref(std::sync::Arc::new(var)),
        Wrapper::Final => PureExpr::Final(std::sync::Arc::new(var)),
    }
}

fn option_payload_eq(conjunct: &PureExpr, option_expr: &PureExpr, payload: &PureExpr) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = conjunct else {
        return false;
    };
    (same_expr(left, option_expr) && is_some_of(right, payload))
        || (same_expr(right, option_expr) && is_some_of(left, payload))
}

fn result_eq_var(expr: &PureExpr, var: &str) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return false;
    };
    (is_var_named(left, "result") && is_var_named(right, var))
        || (is_var_named(right, "result") && is_var_named(left, var))
}

fn result_eq_expr(expr: &PureExpr, expected: &PureExpr) -> bool {
    let PureExpr::BinOp(left, BinOp::Eq, right) = expr else {
        return false;
    };
    (is_var_named(left, "result") && same_expr(right, expected))
        || (is_var_named(right, "result") && same_expr(left, expected))
}

fn is_some_of(expr: &PureExpr, payload: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::LogicFnCall { name, args }
            if short_constructor_name(name) == "Some"
                && args.len() == 1
                && same_expr(&args[0], payload)
    )
}

fn tuple_get_base_var(expr: &PureExpr, field: usize) -> Option<&str> {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return None;
    };
    if name != &tuple_field_logic_fn_name(field) || args.len() != 1 {
        return None;
    }
    match &args[0] {
        PureExpr::Var(name, _) => Some(name.as_str()),
        _ => None,
    }
}

fn is_tuple_get_of_var(expr: &PureExpr, field: usize, base_name: &str) -> bool {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return false;
    };
    name == &tuple_field_logic_fn_name(field)
        && args.len() == 1
        && is_var_named(&args[0], base_name)
}

fn is_tuple_get_of(expr: &PureExpr, field: usize, base: &PureExpr) -> bool {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return false;
    };
    name == &tuple_field_logic_fn_name(field) && args.len() == 1 && same_expr(&args[0], base)
}

fn tuple_get_expr(field: usize, base: PureExpr) -> PureExpr {
    PureExpr::LogicFnCall {
        name: tuple_field_logic_fn_name(field),
        args: vec![base],
    }
}

fn is_var_named(expr: &PureExpr, expected: &str) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == expected)
}

fn closure_weakening_follows_from_requires(
    encoder: &mut AYEncoder,
    ensure: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> bool {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = ensure
    else {
        return false;
    };

    match method.as_str() {
        "postcondition_once" => {
            let receiver = normalize_closure_receiver_for_obligation(receiver);
            let has_fn_postcondition = ctx.requires.iter().any(|require| {
                requirement_contains_matching_postcondition(require, receiver, args)
            });
            let has_fnmut_postcondition = ctx.requires.iter().any(|require| {
                requirement_contains_matching_postcondition_mut_for_once(require, receiver, args)
            });
            has_fnmut_postcondition
                || (receiver_resolves_trivially(encoder, receiver) && has_fn_postcondition)
        }
        "postcondition_mut" => {
            if args.len() < 2 {
                return false;
            }
            let receiver = normalize_closure_receiver_for_obligation(receiver);
            let res_state = &args[args.len() - 2];
            let result = args.last().expect("postcondition_mut args is non-empty");
            let mut post_args = args[..args.len() - 2].to_vec();
            post_args.push(result.clone());
            let mut post_arg_variants = vec![post_args];
            if is_var_named(result, "result") {
                if let Some(return_expr) = ctx.return_expr {
                    let mut return_args = args[..args.len() - 2].to_vec();
                    return_args.push(return_expr.clone());
                    post_arg_variants.push(return_args);
                }
            }
            let has_post = post_arg_variants.iter().any(|post_args| {
                ctx.requires.iter().any(|require| {
                    requirement_contains_matching_postcondition(require, receiver, post_args)
                })
            });
            let mut mut_arg_variants = vec![args.clone()];
            if is_var_named(result, "result") {
                if let Some(return_expr) = ctx.return_expr {
                    let mut return_args = args.clone();
                    if let Some(last) = return_args.last_mut() {
                        *last = return_expr.clone();
                    }
                    mut_arg_variants.push(return_args);
                }
            }
            let has_mut_post = mut_arg_variants.iter().any(|mut_args| {
                ctx.requires.iter().any(|require| {
                    requirement_contains_matching_postcondition_mut_for_mut(
                        require, receiver, mut_args, ctx,
                    )
                })
            });
            let has_state_eq = ctx
                .requires
                .iter()
                .any(|require| requirement_contains_eq(require, receiver, res_state));
            let has_identity_final_state =
                closure_res_state_is_synthesized_identity(receiver, res_state, ctx);
            (has_post && (has_state_eq || has_identity_final_state)) || has_mut_post
        }
        _ => false,
    }
}

fn closure_res_state_is_synthesized_identity(
    receiver: &PureExpr,
    res_state: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> bool {
    let Some(final_values) = ctx.mut_borrow_final_values else {
        return false;
    };
    let final_base = match res_state {
        PureExpr::Final(inner) => normalize_closure_receiver_for_obligation(inner),
        PureExpr::Var(name, _) if name.contains("_final") => res_state,
        _ => return false,
    };
    let Some(final_name) = closure_receiver_base_name(final_base) else {
        return false;
    };
    let Some(identity_value) = final_values
        .get(final_name)
        .or_else(|| final_values.get(canonical_closure_state_name(final_name)))
    else {
        return false;
    };
    let identity_value = normalize_closure_receiver_for_obligation(identity_value);
    same_closure_receiver(identity_value, receiver)
}

fn closure_existential_postcondition_follows_from_requires(
    ensure: &PureExpr,
    requires: &[PureExpr],
) -> bool {
    let mut existential_vars = HashSet::new();
    let body = peel_consecutive_exists(ensure, &mut existential_vars);
    if existential_vars.is_empty() || !expr_has_closure_postcondition_method(body) {
        return false;
    }

    let mut goals = Vec::new();
    collect_conjuncts(body, &mut goals);
    if goals.is_empty() {
        return false;
    }

    let mut substitutions = HashMap::new();
    for goal in goals {
        let mut matched = false;
        for require in requires {
            let mut candidate_substitutions = substitutions.clone();
            if requirement_matches_existential_goal(
                goal,
                require,
                &existential_vars,
                &mut candidate_substitutions,
            ) {
                substitutions = candidate_substitutions;
                matched = true;
                break;
            }
        }
        if !matched {
            return false;
        }
    }
    true
}

fn peel_consecutive_exists<'a>(mut expr: &'a PureExpr, vars: &mut HashSet<String>) -> &'a PureExpr {
    while let PureExpr::Exists { var, body, .. } = expr {
        vars.insert(var.clone());
        expr = body;
    }
    expr
}

fn expr_has_closure_postcondition_method(expr: &PureExpr) -> bool {
    let mut found = false;
    expr.for_each_recursive(|node| {
        if matches!(
            node,
            PureExpr::MethodCall { method, .. }
                if matches!(
                    method.as_str(),
                    "precondition"
                        | "postcondition"
                        | "postcondition_mut"
                        | "postcondition_once"
                )
        ) {
            found = true;
        }
    });
    found
}

fn requirement_matches_existential_goal(
    goal: &PureExpr,
    require: &PureExpr,
    existential_vars: &HashSet<String>,
    substitutions: &mut HashMap<String, PureExpr>,
) -> bool {
    match require {
        PureExpr::BinOp(left, BinOp::And, right) => {
            let mut left_substitutions = substitutions.clone();
            if requirement_matches_existential_goal(
                goal,
                left,
                existential_vars,
                &mut left_substitutions,
            ) {
                *substitutions = left_substitutions;
                return true;
            }
            requirement_matches_existential_goal(goal, right, existential_vars, substitutions)
        }
        _ => unify_existential_goal(goal, require, existential_vars, substitutions),
    }
}

fn unify_existential_goal(
    goal: &PureExpr,
    require: &PureExpr,
    existential_vars: &HashSet<String>,
    substitutions: &mut HashMap<String, PureExpr>,
) -> bool {
    if let PureExpr::Var(name, _) = goal {
        if existential_vars.contains(name) {
            if let Some(existing) = substitutions.get(name) {
                return same_expr(existing, require);
            }
            substitutions.insert(name.clone(), require.clone());
            return true;
        }
    }

    match (goal, require) {
        (
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            },
            PureExpr::MethodCall {
                receiver: req_receiver,
                method: req_method,
                args: req_args,
            },
        ) if method == req_method && args.len() == req_args.len() => {
            let receiver = normalize_closure_receiver_for_obligation(receiver);
            let req_receiver = normalize_closure_receiver_for_obligation(req_receiver);
            unify_existential_goal(receiver, req_receiver, existential_vars, substitutions)
                && args.iter().zip(req_args).all(|(arg, req_arg)| {
                    unify_existential_goal(arg, req_arg, existential_vars, substitutions)
                })
        }
        (
            PureExpr::LogicFnCall { name, args },
            PureExpr::LogicFnCall {
                name: req_name,
                args: req_args,
            },
        ) if name == req_name && args.len() == req_args.len() => {
            args.iter().zip(req_args).all(|(arg, req_arg)| {
                unify_existential_goal(arg, req_arg, existential_vars, substitutions)
            })
        }
        (PureExpr::BinOp(left, op, right), PureExpr::BinOp(req_left, req_op, req_right))
            if op == req_op =>
        {
            unify_existential_goal(left, req_left, existential_vars, substitutions)
                && unify_existential_goal(right, req_right, existential_vars, substitutions)
        }
        (PureExpr::UnOp(op, inner), PureExpr::UnOp(req_op, req_inner)) if op == req_op => {
            unify_existential_goal(inner, req_inner, existential_vars, substitutions)
        }
        (PureExpr::Deref(inner), PureExpr::Deref(req_inner))
        | (PureExpr::Final(inner), PureExpr::Final(req_inner))
        | (PureExpr::Old(inner), PureExpr::Old(req_inner))
        | (PureExpr::View(inner), PureExpr::View(req_inner)) => {
            unify_existential_goal(inner, req_inner, existential_vars, substitutions)
        }
        _ => same_expr(goal, require),
    }
}

fn receiver_resolves_trivially(encoder: &mut AYEncoder, receiver: &PureExpr) -> bool {
    let Ok(term) = encoder.encode_pure(receiver) else {
        return false;
    };
    let sort = encoder.solver().get_sort(term);
    closure_env_sort_name(&sort).is_none()
}

fn normalize_closure_receiver_for_obligation(expr: &PureExpr) -> &PureExpr {
    match expr {
        PureExpr::Deref(inner) => normalize_closure_receiver_for_obligation(inner),
        _ => expr,
    }
}

fn closure_receiver_base_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner) => closure_receiver_base_name(inner),
        _ => None,
    }
}

fn same_closure_receiver(left: &PureExpr, right: &PureExpr) -> bool {
    same_expr(left, right)
}

fn canonical_closure_state_name(mut name: &str) -> &str {
    loop {
        if let Some(stripped) = name.strip_suffix("_current") {
            name = stripped;
            continue;
        }
        if let Some(stripped) = name.strip_suffix("_final") {
            name = stripped;
            continue;
        }
        return name;
    }
}

fn requirement_contains_matching_postcondition(
    require: &PureExpr,
    receiver: &PureExpr,
    args: &[PureExpr],
) -> bool {
    match require {
        PureExpr::MethodCall {
            receiver: req_receiver,
            method,
            args: req_args,
        } if method == "postcondition" => {
            let req_receiver = normalize_closure_receiver_for_obligation(req_receiver);
            same_closure_receiver(req_receiver, receiver) && same_exprs(req_args, args)
        }
        PureExpr::BinOp(left, BinOp::And, right) => {
            requirement_contains_matching_postcondition(left, receiver, args)
                || requirement_contains_matching_postcondition(right, receiver, args)
        }
        _ => false,
    }
}

fn requirement_contains_matching_postcondition_mut_for_once(
    require: &PureExpr,
    receiver: &PureExpr,
    once_args: &[PureExpr],
) -> bool {
    match require {
        PureExpr::MethodCall {
            receiver: req_receiver,
            method,
            args: mut_args,
        } if method == "postcondition_mut" => {
            let req_receiver = normalize_closure_receiver_for_obligation(req_receiver);
            same_closure_receiver(req_receiver, receiver)
                && fnmut_args_imply_fnonce_args(mut_args, once_args)
        }
        PureExpr::BinOp(left, BinOp::And, right) => {
            requirement_contains_matching_postcondition_mut_for_once(left, receiver, once_args)
                || requirement_contains_matching_postcondition_mut_for_once(
                    right, receiver, once_args,
                )
        }
        _ => false,
    }
}

fn requirement_contains_matching_postcondition_mut_for_mut(
    require: &PureExpr,
    receiver: &PureExpr,
    expected_args: &[PureExpr],
    ctx: &ObligationSliceContext<'_>,
) -> bool {
    match require {
        PureExpr::MethodCall {
            receiver: req_receiver,
            method,
            args: req_args,
        } if method == "postcondition_mut" => {
            let req_receiver = normalize_closure_receiver_for_obligation(req_receiver);
            same_closure_receiver(req_receiver, receiver)
                && fnmut_args_match_for_obligation(req_args, expected_args, receiver, ctx)
        }
        PureExpr::BinOp(left, BinOp::And, right) => {
            requirement_contains_matching_postcondition_mut_for_mut(
                left,
                receiver,
                expected_args,
                ctx,
            ) || requirement_contains_matching_postcondition_mut_for_mut(
                right,
                receiver,
                expected_args,
                ctx,
            )
        }
        _ => false,
    }
}

fn fnmut_args_match_for_obligation(
    actual: &[PureExpr],
    expected: &[PureExpr],
    receiver: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> bool {
    if actual.len() < 2 || actual.len() != expected.len() {
        return false;
    }
    let res_state_idx = actual.len() - 2;
    same_exprs(&actual[..res_state_idx], &expected[..res_state_idx])
        && same_expr(
            actual.last().expect("actual len checked"),
            expected.last().expect("expected len checked"),
        )
        && closure_res_states_compatible(
            &actual[res_state_idx],
            &expected[res_state_idx],
            receiver,
            ctx,
        )
}

fn closure_res_states_compatible(
    actual: &PureExpr,
    expected: &PureExpr,
    receiver: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> bool {
    same_expr(actual, expected)
        || (closure_res_state_is_synthesized_identity(receiver, actual, ctx)
            && closure_res_state_is_synthesized_identity(receiver, expected, ctx))
}

fn fnmut_args_imply_fnonce_args(mut_args: &[PureExpr], once_args: &[PureExpr]) -> bool {
    if once_args.is_empty() || mut_args.len() != once_args.len() + 1 {
        return false;
    }
    let once_result_index = once_args.len() - 1;
    same_exprs(
        &mut_args[..once_result_index],
        &once_args[..once_result_index],
    ) && same_expr(
        mut_args.last().expect("mut_args length checked"),
        once_args.last().expect("once_args is non-empty"),
    )
}

fn postcondition_depends_on_unconstrained_logic_fn(
    ensure: &PureExpr,
    logic_fns: Option<&[trust_wp_core::logic::LogicFnDef]>,
    requires: &[PureExpr],
) -> bool {
    let Some(logic_fns) = logic_fns else {
        return false;
    };
    if requires.iter().any(|require| same_expr(require, ensure)) {
        return false;
    }
    match ensure {
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            if same_expr(left, right) {
                return false;
            }
            expr_is_unconstrained_logic_call(left, logic_fns)
                || expr_is_unconstrained_logic_call(right, logic_fns)
        }
        PureExpr::LogicFnCall { .. } => expr_is_unconstrained_logic_call(ensure, logic_fns),
        _ => false,
    }
}

fn expr_is_unconstrained_logic_call(
    expr: &PureExpr,
    logic_fns: &[trust_wp_core::logic::LogicFnDef],
) -> bool {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return false;
    };
    logic_fns.iter().any(|logic_fn| {
        logic_fn.name() == name
            && logic_fn.params().len() == args.len()
            && logic_fn.ensures().is_empty()
            && (logic_fn.is_opaque() || logic_fn.mode() == LogicMode::Default)
    })
}

fn requirement_contains_eq(require: &PureExpr, lhs: &PureExpr, rhs: &PureExpr) -> bool {
    match require {
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            (same_expr(left, lhs) && same_expr(right, rhs))
                || (same_expr(left, rhs) && same_expr(right, lhs))
        }
        PureExpr::BinOp(left, BinOp::And, right) => {
            requirement_contains_eq(left, lhs, rhs) || requirement_contains_eq(right, lhs, rhs)
        }
        _ => false,
    }
}

fn same_exprs(left: &[PureExpr], right: &[PureExpr]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right.iter())
            .all(|(left, right)| same_expr(left, right))
}

fn same_expr(left: &PureExpr, right: &PureExpr) -> bool {
    crate::encoder::quantifier::pure_quantifier::is_sort_agnostic_equal(left, right)
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    /// `#[logic(open)] #[requires(x >= 0)] #[ensures(result == x)] fn idl(x)`.
    fn guarded_identity_logic_fn() -> trust_wp_core::logic::LogicFnDef {
        let mut logic_fn = trust_wp_core::logic::LogicFnDef::new_with_requires(
            "idl".to_string(),
            "mod::idl".to_string(),
            vec!["x".to_string()],
            vec![PureExpr::BinOp(
                Arc::new(var("x")),
                BinOp::Ge,
                Arc::new(PureExpr::Int(0)),
            )],
            var("x"),
        );
        logic_fn.set_ensures(vec![PureExpr::BinOp(
            Arc::new(var("result")),
            BinOp::Eq,
            Arc::new(var("x")),
        )]);
        logic_fn
    }

    /// `idl(<arg>) == <arg>` — one instance of `idl`'s postcondition.
    fn idl_spec_instance_at(arg: i64) -> PureExpr {
        let call = PureExpr::LogicFnCall {
            name: "idl".to_string(),
            args: vec![PureExpr::Int(arg)],
        };
        PureExpr::BinOp(Arc::new(call), BinOp::Eq, Arc::new(PureExpr::Int(arg)))
    }

    /// The grant and the obligation must sit in the same environment: an
    /// instance of a logic fn's `ensures` may discharge an obligation only
    /// where the SAME instance of its `requires` holds. Outside that domain
    /// the body proved nothing, so this lane must decline and let the solver —
    /// which holds only `forall x. requires => ensures` — decide.
    /// (`logic_fn_ensures_granted_outside_requires.rs`)
    #[test]
    fn a_logic_fn_spec_instance_is_granted_only_inside_its_requires() {
        let logic_fns = [guarded_identity_logic_fn()];

        assert!(
            postcondition_is_logic_fn_spec_instance(
                &idl_spec_instance_at(2),
                Some(&logic_fns),
                &[],
            ),
            "in-domain instance must still be discharged here"
        );
        assert!(
            !postcondition_is_logic_fn_spec_instance(
                &idl_spec_instance_at(-1),
                Some(&logic_fns),
                &[],
            ),
            "an argument the requires excludes must not harvest the ensures"
        );

        // A non-literal argument is in-domain only when the surrounding
        // requires say so; otherwise this layer cannot establish the domain
        // and fails closed.
        let call = PureExpr::LogicFnCall {
            name: "idl".to_string(),
            args: vec![var("n")],
        };
        let open_instance = PureExpr::BinOp(Arc::new(call), BinOp::Eq, Arc::new(var("n")));
        let n_nonneg = PureExpr::BinOp(Arc::new(var("n")), BinOp::Ge, Arc::new(PureExpr::Int(0)));
        assert!(postcondition_is_logic_fn_spec_instance(
            &open_instance,
            Some(&logic_fns),
            std::slice::from_ref(&n_nonneg),
        ));
        assert!(!postcondition_is_logic_fn_spec_instance(
            &open_instance,
            Some(&logic_fns),
            &[],
        ));
    }

    /// Once a refutation shape has fired for a slice, a structural accept lane
    /// reached afterwards is REFUSED — the rule holds by this guard, not by
    /// lane order, so re-ordering the lanes cannot reopen the accept (D-28).
    #[test]
    fn a_structural_accept_after_a_fired_shape_is_refused() {
        let _scope = SliceRefutationShapeScope::enter();
        assert_eq!(slice_refutation_shape(), None);
        // No shape: an accept passes through untouched.
        assert!(matches!(
            withhold_structural_accept_after_shape(VerificationResult::Verified(None)),
            VerificationResult::Verified(None)
        ));
        assert!(structural_refutation_hint(
            "postcondition-contradicts-requirements"
        ));
        assert_eq!(
            slice_refutation_shape(),
            Some("postcondition-contradicts-requirements")
        );
        match withhold_structural_accept_after_shape(VerificationResult::Verified(None)) {
            VerificationResult::Unknown(UnknownReason::SolverMessage(message)) => {
                assert!(
                    message.contains("postcondition-contradicts-requirements"),
                    "the withheld verdict must name the shape: {message}"
                );
                assert!(message.contains("may not discharge it"), "{message}");
            }
            other => panic!("a structural accept after a shape must be refused, got {other:?}"),
        }
        // Rejections and inconclusive verdicts are untouched: the rule forbids
        // only the accept.
        assert!(matches!(
            withhold_structural_accept_after_shape(VerificationResult::Unknown(
                UnknownReason::Timeout
            )),
            VerificationResult::Unknown(UnknownReason::Timeout)
        ));
        assert!(matches!(
            withhold_structural_accept_after_shape(VerificationResult::Failed(
                crate::verify::Counterexample::empty()
            )),
            VerificationResult::Failed(_)
        ));
    }

    /// The shape flag is slice-scoped: a nested verification (a fresh base
    /// recheck, a type-invariant precheck) neither inherits nor clobbers the
    /// enclosing slice's shape.
    #[test]
    fn the_shape_flag_is_slice_scoped_and_nest_safe() {
        let _outer = SliceRefutationShapeScope::enter();
        assert!(structural_refutation_hint("result-contradicts-return-expr"));
        assert_eq!(
            slice_refutation_shape(),
            Some("result-contradicts-return-expr")
        );
        {
            let _inner = SliceRefutationShapeScope::enter();
            assert_eq!(
                slice_refutation_shape(),
                None,
                "a nested slice must not inherit the outer slice's shape"
            );
            assert!(structural_refutation_hint(
                "result-match-over-option-ite-directly-invalid"
            ));
        }
        assert_eq!(
            slice_refutation_shape(),
            Some("result-contradicts-return-expr"),
            "the outer slice's shape must survive a nested slice"
        );
    }

    /// The vacuity demotions the fall-through solve can report are recognised,
    /// so a shape-refuted slice over a contradictory base reports `vacuous`
    /// (exit 2) instead of an uncounted `refutation withheld`.
    #[test]
    fn the_two_vacuity_demotions_are_recognised() {
        for message in [
            crate::verify::solver_tail::VACUOUS_PROOF_MESSAGE,
            crate::verify::solver_tail::VACUOUS_WITH_ENCODER_AXIOMS_MESSAGE,
        ] {
            assert!(
                message.contains("vacuous proof"),
                "the driver counts on this prefix: {message}"
            );
            assert!(unknown_reason_is_vacuous(&UnknownReason::SolverMessage(
                message.to_string()
            )));
        }
        assert!(!unknown_reason_is_vacuous(&UnknownReason::Timeout));
        assert!(!unknown_reason_is_vacuous(&UnknownReason::SolverMessage(
            "refutation withheld".to_string()
        )));
    }

    /// A slice a structural shape refuted and the solver proved is withheld,
    /// never accepted (D-28: the shapes fall through to the solver for the
    /// model; a disagreement fails closed like the function lane's
    /// `reconcile_precheck_refutation`).
    #[test]
    fn structural_slice_refutation_disagreeing_with_a_proof_is_withheld() {
        match structural_refutation_disagrees_with_proof() {
            VerificationResult::Unknown(UnknownReason::SolverMessage(message)) => {
                assert!(message.contains("verdict withheld"), "{message}");
            }
            other => panic!("a disagreement must fail closed, got {other:?}"),
        }
    }

    fn ok(payload: PureExpr) -> PureExpr {
        PureExpr::LogicFnCall {
            name: "OwnResult::Ok".to_string(),
            args: vec![payload],
        }
    }

    fn err(payload: PureExpr) -> PureExpr {
        PureExpr::LogicFnCall {
            name: "OwnResult::Err".to_string(),
            args: vec![payload],
        }
    }

    fn tuple_match(ok_body: PureExpr) -> PureExpr {
        PureExpr::Match {
            scrutinee: Arc::new(PureExpr::LogicFnCall {
                name: "__trust_wp_tuple2".to_string(),
                args: vec![var("self"), var("result")],
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Tuple(vec![
                        Pattern::Constructor {
                            name: "OwnResult::Ok".to_string(),
                            inner: Some(Box::new(Pattern::Binding("s".to_string()))),
                        },
                        Pattern::Constructor {
                            name: "OwnResult::Ok".to_string(),
                            inner: Some(Box::new(Pattern::Binding("r".to_string()))),
                        },
                    ]),
                    body: ok_body,
                },
                MatchArm {
                    pattern: Pattern::Tuple(vec![
                        Pattern::Constructor {
                            name: "OwnResult::Err".to_string(),
                            inner: Some(Box::new(Pattern::Binding("s".to_string()))),
                        },
                        Pattern::Constructor {
                            name: "OwnResult::Err".to_string(),
                            inner: Some(Box::new(Pattern::Binding("r".to_string()))),
                        },
                    ]),
                    body: PureExpr::BinOp(Arc::new(var("s")), BinOp::Eq, Arc::new(var("r"))),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    body: PureExpr::Bool(false),
                },
            ],
        }
    }

    fn logic(name: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::LogicFnCall {
            name: name.to_string(),
            args,
        }
    }

    fn some(payload: PureExpr) -> PureExpr {
        logic("Some", vec![payload])
    }

    fn none() -> PureExpr {
        logic("None", vec![])
    }

    fn seq_empty() -> PureExpr {
        logic("Seq::empty", vec![])
    }

    fn bin(left: PureExpr, op: BinOp, right: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(left), op, Arc::new(right))
    }

    fn eq(left: PureExpr, right: PureExpr) -> PureExpr {
        bin(left, BinOp::Eq, right)
    }

    fn gt(left: PureExpr, right: PureExpr) -> PureExpr {
        bin(left, BinOp::Gt, right)
    }

    fn and_all(mut exprs: Vec<PureExpr>) -> PureExpr {
        let first = exprs.remove(0);
        exprs
            .into_iter()
            .fold(first, |acc, expr| bin(acc, BinOp::And, expr))
    }

    fn method(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: method.to_string(),
            args,
        }
    }

    fn seq_var(name: &str) -> PureExpr {
        PureExpr::Var(
            name.to_string(),
            Some(trust_wp_core::formula::ExprSort::Seq),
        )
    }

    fn view(expr: PureExpr) -> PureExpr {
        PureExpr::View(Arc::new(expr))
    }

    fn seq_len(expr: PureExpr) -> PureExpr {
        method(expr, "len", vec![])
    }

    fn seq_ext_eq_concat_requirement(seq: PureExpr, left: PureExpr, right: PureExpr) -> PureExpr {
        method(seq, "ext_eq", vec![method(left, "concat", vec![right])])
    }

    #[test]
    fn explicit_seq_ext_eq_concat_discharges_exact_length_conservation() {
        let seq = view(seq_var("original"));
        let left = view(seq_var("produced"));
        let right = view(seq_var("remaining"));
        let requires = [seq_ext_eq_concat_requirement(
            seq.clone(),
            left.clone(),
            right.clone(),
        )];
        let ensure = eq(seq_len(seq), bin(seq_len(left), BinOp::Add, seq_len(right)));

        assert!(
            seq_ext_eq_concat_length_conservation_follows_requires(&ensure, &requires),
            "the exact explicitly typed Seq conservation law should discharge"
        );
    }

    #[test]
    fn explicit_seq_ext_eq_concat_discharges_exact_left_length_bound_only() {
        let seq = view(seq_var("original"));
        let left = view(seq_var("produced"));
        let right = view(seq_var("remaining"));
        let requires = [seq_ext_eq_concat_requirement(
            seq.clone(),
            left.clone(),
            right,
        )];
        let ensure = bin(seq_len(left.clone()), BinOp::Le, seq_len(seq));
        assert!(
            seq_ext_eq_concat_left_length_bound_follows_requires(&ensure, &requires),
            "the exact left-concat length bound should discharge"
        );

        let wrong_side = bin(
            seq_len(view(seq_var("different"))),
            BinOp::Le,
            seq_len(left),
        );
        assert!(
            !seq_ext_eq_concat_left_length_bound_follows_requires(&wrong_side, &requires),
            "a noncongruent bound must stay on the solver path"
        );
    }

    #[test]
    fn seq_ext_eq_concat_length_discharge_rejects_mismatch_and_non_seq_operands() {
        let seq = view(seq_var("original"));
        let left = view(seq_var("produced"));
        let right = view(seq_var("remaining"));
        let requires = [seq_ext_eq_concat_requirement(
            seq.clone(),
            left.clone(),
            right.clone(),
        )];
        let mismatched = eq(
            seq_len(seq),
            bin(
                seq_len(left),
                BinOp::Add,
                seq_len(view(seq_var("different"))),
            ),
        );
        assert!(
            !seq_ext_eq_concat_length_conservation_follows_requires(&mismatched, &requires),
            "a noncongruent remainder must stay on the solver path"
        );

        let untyped_seq = view(var("original"));
        let untyped_left = view(var("produced"));
        let untyped_right = view(var("remaining"));
        let untyped_requires = [seq_ext_eq_concat_requirement(
            untyped_seq.clone(),
            untyped_left.clone(),
            untyped_right.clone(),
        )];
        let untyped_ensure = eq(
            seq_len(untyped_seq),
            bin(seq_len(untyped_left), BinOp::Add, seq_len(untyped_right)),
        );
        assert!(
            !seq_ext_eq_concat_length_conservation_follows_requires(
                &untyped_ensure,
                &untyped_requires,
            ),
            "untyped ext_eq methods must not acquire Seq semantics"
        );
    }

    #[test]
    fn take_first_mut_result_match_follows_split_first_source_fact() {
        let source = var("call_2");
        let split_payload = tuple_get_expr(0, source.clone());
        let return_expr = PureExpr::Ite(
            Arc::new(eq(
                method(source.clone(), "discriminant", vec![]),
                PureExpr::Int(0),
            )),
            Arc::new(none()),
            Arc::new(PureExpr::LetAssume {
                assumption: Arc::new(eq(var("self_"), tuple_get_expr(1, split_payload.clone()))),
                body: Arc::new(some(tuple_get_expr(0, split_payload.clone()))),
            }),
        );

        let split_first_fact = PureExpr::Match {
            scrutinee: Arc::new(source),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Tuple(vec![
                            Pattern::Binding("first".to_string()),
                            Pattern::Binding("rem".to_string()),
                        ]))),
                    },
                    body: and_all(vec![
                        eq(
                            deref_expr(var("first")),
                            method(
                                source_current_seq_expr(),
                                "index_logic",
                                vec![PureExpr::Int(0)],
                            ),
                        ),
                        eq(
                            final_expr(var("first")),
                            method(
                                source_final_seq_expr(),
                                "index_logic",
                                vec![PureExpr::Int(0)],
                            ),
                        ),
                        gt(
                            method(source_current_seq_expr(), "len", vec![]),
                            PureExpr::Int(0),
                        ),
                        gt(
                            method(source_final_seq_expr(), "len", vec![]),
                            PureExpr::Int(0),
                        ),
                        eq(
                            view_expr(deref_expr(var("rem"))),
                            method(source_current_seq_expr(), "tail", vec![]),
                        ),
                        eq(
                            view_expr(final_expr(var("rem"))),
                            method(source_final_seq_expr(), "tail", vec![]),
                        ),
                    ]),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    body: and_all(vec![
                        eq(
                            method(source_current_seq_expr(), "len", vec![]),
                            PureExpr::Int(0),
                        ),
                        eq(source_final_seq_expr(), source_current_seq_expr()),
                        eq(source_current_seq_expr(), seq_empty()),
                    ]),
                },
            ],
        };

        let mem_take_empty = eq(view_expr(final_expr(var("self_"))), seq_empty());
        let ensure = PureExpr::Match {
            scrutinee: Arc::new(var("result")),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("r".to_string()))),
                    },
                    body: and_all(vec![
                        eq(
                            deref_expr(var("r")),
                            method(
                                current_self_ref_expr(),
                                "index_logic",
                                vec![PureExpr::Int(0)],
                            ),
                        ),
                        eq(
                            final_expr(var("r")),
                            method(final_self_ref_expr(), "index_logic", vec![PureExpr::Int(0)]),
                        ),
                        gt(
                            method(current_self_seq_expr(), "len", vec![]),
                            PureExpr::Int(0),
                        ),
                        gt(
                            method(final_self_seq_expr(), "len", vec![]),
                            PureExpr::Int(0),
                        ),
                        eq(
                            view_expr(deref_expr(final_expr(var("self_")))),
                            method(current_self_seq_expr(), "tail", vec![]),
                        ),
                        eq(
                            view_expr(final_expr(final_expr(var("self_")))),
                            method(final_self_seq_expr(), "tail", vec![]),
                        ),
                    ]),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    body: and_all(vec![
                        eq(view_expr(deref_expr(final_expr(var("self_")))), seq_empty()),
                        eq(current_self_seq_expr(), seq_empty()),
                        eq(final_self_seq_expr(), seq_empty()),
                        eq(view_expr(final_expr(final_expr(var("self_")))), seq_empty()),
                    ]),
                },
            ],
        };

        assert!(take_first_mut_result_match_follows_split_first_source(
            &ensure,
            Some(&return_expr),
            &[split_first_fact.clone(), mem_take_empty.clone()],
        ));
        assert!(!take_first_mut_result_match_follows_split_first_source(
            &ensure,
            Some(&return_expr),
            &[mem_take_empty],
        ));
    }

    #[test]
    fn result_equality_follows_direct_context_fact() {
        let double_x = logic("double", vec![var("x")]);
        let ensure = eq(var("result"), double_x.clone());
        let facts = vec![eq(double_x, PureExpr::Int(42))];

        assert!(result_equality_follows_from_context_fact(
            &ensure,
            Some(&PureExpr::Int(42)),
            &facts,
        ));
        assert!(!result_equality_follows_from_context_fact(
            &ensure,
            Some(&PureExpr::Int(41)),
            &facts,
        ));
    }

    #[test]
    fn result_equality_follows_nested_context_fact() {
        let double_x = logic("double", vec![var("x")]);
        let ensure = eq(var("result"), double_x.clone());
        let fact = bin(
            PureExpr::Bool(true),
            BinOp::Implies,
            eq(PureExpr::Int(42), double_x),
        );

        assert!(result_equality_follows_from_context_fact(
            &ensure,
            Some(&PureExpr::Int(42)),
            &[fact],
        ));
    }

    #[test]
    fn copied_result_match_follows_return_branches() {
        let return_expr = PureExpr::Ite(
            Arc::new(PureExpr::Bool(true)),
            Arc::new(ok(PureExpr::Deref(Arc::new(var("self.0"))))),
            Arc::new(err(var("self.0"))),
        );
        let ok_body = PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(var("r")),
                BinOp::Eq,
                Arc::new(PureExpr::Deref(Arc::new(var("s")))),
            )),
            BinOp::And,
            Arc::new(PureExpr::LogicFnCall {
                name: "resolve".to_string(),
                args: vec![var("s")],
            }),
        );

        assert!(result_match_postcondition_follows_return_branches(
            &tuple_match(ok_body),
            Some(&return_expr),
            &[],
        ));
    }

    #[test]
    fn cloned_result_match_follows_required_postcondition() {
        let return_expr = PureExpr::Ite(
            Arc::new(PureExpr::Bool(true)),
            Arc::new(ok(var("call_4"))),
            Arc::new(err(var("self.0"))),
        );
        let ok_body = PureExpr::MethodCall {
            receiver: Arc::new(var("T::clone")),
            method: "postcondition".to_string(),
            args: vec![var("s"), var("r")],
        };
        let requires = vec![PureExpr::MethodCall {
            receiver: Arc::new(var("T::clone")),
            method: "postcondition".to_string(),
            args: vec![var("self.0"), var("call_4")],
        }];

        assert!(result_match_postcondition_follows_return_branches(
            &tuple_match(ok_body),
            Some(&return_expr),
            &requires,
        ));
    }

    #[test]
    fn cloned_constructor_match_is_certified_only_with_exact_payload_authority() {
        let return_expr = PureExpr::Match {
            scrutinee: Arc::new(var("self")),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "OwnResult::Ok".to_string(),
                        inner: Some(Box::new(Pattern::Binding("t".to_string()))),
                    },
                    body: ok(var("call_4")),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "OwnResult::Err".to_string(),
                        inner: Some(Box::new(Pattern::Binding("e".to_string()))),
                    },
                    body: err(var("e")),
                },
            ],
        };
        let ok_body = PureExpr::LogicFnCall {
            name: "T::clone.postcondition".to_string(),
            args: vec![var("s"), var("r")],
        };
        let ensure = tuple_match(ok_body);
        let required = PureExpr::LogicFnCall {
            name: "T::clone.postcondition".to_string(),
            args: vec![var("self.0"), var("call_4")],
        };

        assert!(
            result_constructor_match_postcondition_follows_return_branches(
                &ensure,
                Some(&return_expr),
                std::slice::from_ref(&required),
            )
        );

        let wrong_authority = PureExpr::LogicFnCall {
            name: "T::clone.postcondition".to_string(),
            args: vec![var("self.0"), var("different_result")],
        };
        assert!(
            !result_constructor_match_postcondition_follows_return_branches(
                &ensure,
                Some(&return_expr),
                &[wrong_authority],
            ),
            "a mismatched clone certificate must not authorize the structural discharge"
        );

        let mut wrong_constructor_family = return_expr.clone();
        let PureExpr::Match { arms, .. } = &mut wrong_constructor_family else {
            unreachable!();
        };
        arms[1].body = logic("OtherResult::Err", vec![var("e")]);
        assert!(
            !result_constructor_match_postcondition_follows_return_branches(
                &ensure,
                Some(&wrong_constructor_family),
                std::slice::from_ref(&required),
            ),
            "a same-named constructor from another datatype family must fail closed"
        );

        let mut mixed_ensure = ensure.clone();
        let PureExpr::Match { arms, .. } = &mut mixed_ensure else {
            unreachable!();
        };
        let Pattern::Tuple(patterns) = &mut arms[1].pattern else {
            unreachable!();
        };
        for pattern in patterns {
            let Pattern::Constructor { name, .. } = pattern else {
                unreachable!();
            };
            *name = "OtherResult::Err".to_string();
        }
        let mut mixed_return = return_expr.clone();
        let PureExpr::Match { arms, .. } = &mut mixed_return else {
            unreachable!();
        };
        let Pattern::Constructor { name, .. } = &mut arms[1].pattern else {
            unreachable!();
        };
        *name = "OtherResult::Err".to_string();
        arms[1].body = logic("OtherResult::Err", vec![var("e")]);
        assert!(
            !result_constructor_match_postcondition_follows_return_branches(
                &mixed_ensure,
                Some(&mixed_return),
                std::slice::from_ref(&required),
            ),
            "Ok and Err must belong to one exact datatype family"
        );

        let mut fake_tuple_ensure = ensure.clone();
        let PureExpr::Match { scrutinee, .. } = &mut fake_tuple_ensure else {
            unreachable!();
        };
        let PureExpr::LogicFnCall { name, .. } = Arc::make_mut(scrutinee) else {
            unreachable!();
        };
        *name = "attacker_tuple2".to_string();
        assert!(
            !result_constructor_match_postcondition_follows_return_branches(
                &fake_tuple_ensure,
                Some(&return_expr),
                std::slice::from_ref(&required),
            ),
            "only the canonical tuple2 lowering may authorize the discharge"
        );

        let mut wrong_err_payload = return_expr;
        let PureExpr::Match { arms, .. } = &mut wrong_err_payload else {
            unreachable!();
        };
        arms[1].body = err(var("call_4"));
        assert!(
            !result_constructor_match_postcondition_follows_return_branches(
                &ensure,
                Some(&wrong_err_payload),
                &[required],
            ),
            "an Err branch that does not preserve its authenticated payload must fail closed"
        );
    }

    fn implies(antecedent: PureExpr, consequent: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(antecedent), BinOp::Implies, Arc::new(consequent))
    }

    /// A premise an arm's edge scopes, `(x == 0) ==> (r == 5)`, sends every equality
    /// query back through its own antecedent; the walk must end with an answer.
    #[test]
    fn edge_scoped_equality_fact_ends_the_truth_walk() {
        let scoped = implies(
            eq(var("x"), PureExpr::Int(0)),
            eq(var("r"), PureExpr::Int(5)),
        );
        let facts = [&scoped];
        assert!(!expr_follows_from_facts(
            &eq(var("r"), PureExpr::Int(7)),
            &facts
        ));
        assert!(!expr_follows_from_facts(
            &eq(var("r"), PureExpr::Int(5)),
            &facts
        ));
        assert_eq!(
            expr_truth_from_facts(&eq(var("x"), PureExpr::Int(0)), &facts),
            None
        );

        let unit_increment = eq(var("r"), PureExpr::Int(1));
        assert!(!increment_by_one_postcondition_follows_from_facts(
            &unit_increment,
            std::slice::from_ref(&scoped),
        ));
    }

    #[test]
    fn edge_scoped_equality_fact_holds_where_its_edge_does() {
        let edge = eq(var("x"), PureExpr::Int(0));
        let scoped = implies(edge.clone(), eq(var("r"), PureExpr::Int(5)));
        let facts = [&edge, &scoped];
        assert!(expr_follows_from_facts(
            &eq(var("r"), PureExpr::Int(5)),
            &facts
        ));
        assert!(!expr_follows_from_facts(
            &eq(var("r"), PureExpr::Int(7)),
            &facts
        ));
    }
}

/// Trace-only marker for a structural shape that refutes the obligation. The
/// verdict itself comes from the solver (see the comment at the first use).
fn structural_refutation_hint(shape: &'static str) -> bool {
    crate::verify::authority_trace(|| {
        format!("structural refutation shape `{shape}`: falling through to the solver")
    });
    // Record it for the whole slice BEFORE any caller can take an early
    // return: a structural accept reached after this point is refused by
    // `withhold_structural_accept_after_shape` even if a future edit to the
    // lane ordering makes it reachable again.
    SLICE_REFUTATION_SHAPE.with(|cell| {
        if cell.get().is_none() {
            cell.set(Some(shape));
        }
    });
    true
}
