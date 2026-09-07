// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Encoder creation and shared helpers for loop verification.
//!
//! Provides:
//! - [`setup_loop_encoder`]: Full encoder setup via shared bootstrap (#2195)
//! - [`LoopSortPlan`] / [`collect_loop_sort_plan`]: Sort planning for modified vars (#2020)
//! - [`propagate_bool_and_predeclare`]: Legacy wrapper (test-only)
//! - [`encode_and_assert_requires`]: Precondition assertion with existential Skolemization
//! - [`encode_and_assert_condition`]: Loop condition assertion
//! - [`resolve_sat_result_lightweight`]: SAT/UNSAT resolution without model extraction
//! - [`assert_loop_current_chain_alias_constraints`]: `_current`-chain alias linking
//!
//! Prime variable construction lives in [`super::prime_substitutions`].

use std::{collections::HashMap, time::Instant};

use ay_dpll::api::Sort;
use trust_wp_core::{formula::PureExpr, TrackLevel};

use super::{
    super::{Counterexample, VerificationOutcome, VerificationResult},
    LoopEncoderConfig,
};
use crate::{
    encoder::{extract_base_var_name, AYEncoder, AssertionPhase},
    error::EncodingError,
};

/// Encode and assert preconditions with existential Skolemization.
///
/// Delegates to the shared `encode_and_assert_requires` in `setup.rs`.
/// Existentials containing `postcondition_mut` are Skolemized rather than
/// encoded as ay existential quantifiers, which ay-dpll cannot handle
/// (#970, #1364).
pub(in crate::verify::loops) fn encode_and_assert_requires(
    encoder: &mut AYEncoder,
    requires: &[PureExpr],
) -> Result<(), EncodingError> {
    crate::verify::setup::encode_and_assert_requires(encoder, requires)
}

const LOOP_NEGATED_GOAL_LABEL_PREFIX: &str = "__trust_wp_loop_negated_goal";

/// Resolve SAT/UNSAT/UNKNOWN without model extraction.
///
/// Loop variant checks only need the verdict, not a full counterexample model.
/// Avoiding model extraction prevents SAT-shaped variant VCs from spending most
/// of their time enumerating large models in dirty-tree test runs (#1573).
pub(in crate::verify::loops) fn resolve_sat_result_lightweight(
    encoder: &mut AYEncoder,
) -> VerificationResult {
    // Fast axiom-free probe (#2674): many loop VCs (initialization, variant
    // non-negative, simple preservation) are provable from declarations +
    // negated goal alone without ground instances or axioms. Try a short
    // 500ms probe before committing to the full axiom + ground pool path.
    // This mirrors the function pipeline's two-phase approach and saves
    // significant wall-clock time for multi-phase loop verification where
    // 3-6 sub-checks each go through the solver.
    //
    // The probe uses the existing solver state (all assertions from the
    // caller's build_goal closure). If UNSAT, the obligation is proved
    // without needing ground instances or the tiered solve path.
    {
        use std::time::Duration;
        let original_timeout = encoder.solver().timeout();
        let probe_timeout = Duration::from_millis(500);
        let effective_probe = match original_timeout {
            Some(orig) if orig <= probe_timeout => orig,
            _ => probe_timeout,
        };
        encoder.set_timeout(Some(effective_probe));
        let probe_result = encoder.with_negated_goal_label_prefix(
            LOOP_NEGATED_GOAL_LABEL_PREFIX.to_string(),
            |encoder| encoder.check_sat(),
        );
        encoder.set_timeout(original_timeout);
        if matches!(probe_result, ay_dpll::api::SolveResult::Unsat(_))
            && has_accepted_unsat_evidence(encoder)
        {
            return verified_with_exact_strict_replay(encoder);
        }
    }

    // Assert ground instances (gated by LogicGroundInstantiationMode, #1925).
    let _ = encoder.maybe_assert_logic_ground_instances();

    // Use tiered_check_sat (#2674): the loop path previously used
    // check_sat_with_retry, which commits to the full solver timeout (60s)
    // before trying the retry (30s). The tiered approach probes with 10s
    // first — most loop VCs (initialization, preservation, variant) resolve
    // quickly once ground instances are asserted. When the probe returns
    // Unknown and the full solve also returns Unknown, the retry is skipped
    // (the solver had probe + full solve time, retry is unlikely to help).
    // For timeout tests with multiple loop VCs, saving 30s+ per VC is the
    // difference between fitting in the 120s harness limit and timing out.
    let result = encoder.with_negated_goal_label_prefix(
        LOOP_NEGATED_GOAL_LABEL_PREFIX.to_string(),
        crate::verify::solver_tail::tiered_check_sat,
    );
    match result {
        ay_dpll::api::SolveResult::Unsat(_) if has_accepted_unsat_evidence(encoder) => {
            verified_with_exact_strict_replay(encoder)
        }
        ay_dpll::api::SolveResult::Unsat(_) => {
            VerificationResult::Unknown(rejected_unsat_evidence_reason(encoder))
        }
        ay_dpll::api::SolveResult::Sat => VerificationResult::Failed(Counterexample {
            values: Vec::new(),
            violated_postcondition: None,
        }),
        _ => {
            // Reactive batch re-solve (#custom_variant): the INCREMENTAL combiner
            // can churn a small pure-ground datatype+LIA loop VC into
            // `LRA simplex=Sat but unsupported → Unknown` (then the hard-timeout
            // kills it), even though a FRESH non-incremental parse of the
            // IDENTICAL stack closes it UNSAT in well under 20ms. Only after the
            // tiered incremental solve has already given up (this arm) do we pay
            // for one fresh batch solve; a genuine UNSAT there is a valid proof of
            // the same closed query (SOUND — accept only UNSAT; a SAT/uncertain
            // stack falls through to Unknown unchanged). Without this, the loop
            // induction proof spuriously fails, the loop-exit invariant premises
            // are soundly withheld from the function-level path, and the
            // resulting under-premised goal slice is genuinely SAT — a latent
            // false-reject the stronger incremental combiner now surfaces.
            if let Some(summary) = encoder.batch_current_stack_unsat_reactive() {
                // The fresh replay installed its exact checked UNSAT evidence and
                // returned the matching certificate. Vacuity is already ruled out
                // for the loop phases by the #2440 early base-vacuity guard, which
                // runs BEFORE this solve — identical to the incremental UNSAT
                // acceptance path above (neither re-checks vacuity here).
                return VerificationResult::Verified(Some(summary));
            }
            crate::verify::unknown_result_from_encoder(encoder)
        }
    }
}

/// Attach proof authority to an already-established loop UNSAT by replaying
/// the identical live assertion stack through AY's strict proof checker.
///
/// This helper cannot manufacture a verdict: both call sites first require an
/// accepted ordinary UNSAT for the current scoped obligation. The replay adds
/// or drops no declarations or assertions and returns `Some` only when the
/// exact stack is again UNSAT with every proof step independently checked,
/// zero trust/hole fallbacks, and a fully verified summary. Replay failure
/// deliberately leaves `Verified(None)`, which the mandatory public boundary
/// downgrades to `Unknown(ProofTrusted)`.
fn verified_with_exact_strict_replay(encoder: &mut AYEncoder) -> VerificationResult {
    encoder
        .authorize_current_stack_unsat_with_strict_proof()
        .map_or_else(
            VerificationResult::verified,
            VerificationResult::verified_with_proof,
        )
}

fn has_accepted_unsat_evidence(encoder: &AYEncoder) -> bool {
    encoder.last_solve_evidence().is_some_and(|evidence| {
        evidence.accepted_for_consumer && solve_evidence_result_is_unsat(&evidence.result)
    })
}

fn solve_evidence_result_is_unsat(result: &str) -> bool {
    result.eq_ignore_ascii_case("unsat")
        || result
            .strip_prefix("Unsat")
            .is_some_and(|suffix| suffix.is_empty() || suffix.starts_with('('))
}

fn rejected_unsat_evidence_reason(encoder: &AYEncoder) -> crate::verify::UnknownReason {
    let detail = encoder.last_solve_evidence().map_or_else(
        || "missing solver evidence".to_string(),
        |evidence| {
            evidence
                .consumer_rejection
                .clone()
                .unwrap_or_else(|| "solver evidence was not accepted for consumers".to_string())
        },
    );
    crate::verify::UnknownReason::SolverMessage(format!(
        "loop UNSAT result lacks accepted solver evidence: {detail}"
    ))
}

/// Separate-encoder vacuity check for loop verification (#2440).
///
/// Creates a fresh encoder, encodes and asserts the given base expressions,
/// and checks whether they are already contradictory (UNSAT). If so, any
/// proof built on top of these expressions is vacuous.
///
/// Uses a disposable encoder to avoid corrupting the main encoder's state.
/// ay-dpll's incremental solving leaks learned clauses through push/pop,
/// making a two-phase re-solve on the main encoder unreliable for loop VCs
/// with complex axiom bases.
pub(in crate::verify::loops) fn is_base_vacuous(base_exprs: &[PureExpr]) -> bool {
    if base_exprs.is_empty() {
        return false;
    }
    // Skip vacuity check for expressions that require full encoder context
    // (logic function declarations, method dispatch, sort context). The bare
    // bootstrap_encoder can misclassify these as UNSAT due to missing
    // declarations, producing false vacuity verdicts. (#2440)
    if base_exprs.iter().any(expr_needs_full_context) {
        return false;
    }
    let expr_slices = [super::super::setup::ExprSlice::formula(base_exprs)];
    let Ok(mut encoder) =
        super::super::setup::bootstrap_encoder(super::super::setup::BootstrapRequest {
            expr_slices: &expr_slices,
            result_postconditions: None,
            result_expr: None,
            logic_fns: None,
            mode_overrides: None,
            type_invariants: None,
            track: TrackLevel::default(),
            // Bound the quantified vacuity probe so it cannot run unbounded
            // (the check_sat timeout floor also covers this, but a tight
            // explicit probe is clearer). A timeout here conservatively yields
            // a non-Unsat result, i.e. "not vacuous" — verification then
            // proceeds normally rather than skipping.
            timeout: Some(std::time::Duration::from_millis(500)),
            type_constants: None,
            closure_captures: None,
            adt_decls: None,
            adt_field_ranges: None,
        })
    else {
        return false;
    };
    for expr in base_exprs {
        let Ok(term) = encoder.encode_pure(expr) else {
            return false;
        };
        encoder.assert_term(term);
    }
    matches!(encoder.check_sat(), ay_dpll::api::SolveResult::Unsat(_))
}

/// Returns true if the expression contains nodes that require full encoder
/// context (logic function declarations, method dispatch, deref chains, etc.)
/// and therefore cannot be reliably checked in a bare bootstrap encoder.
fn expr_needs_full_context(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| {
        #[allow(unreachable_patterns)]
        match node {
            PureExpr::Var(_, _) | PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_) => {
                false
            }
            PureExpr::BinOp(_, _, _)
            | PureExpr::UnOp(_, _)
            | PureExpr::Ite(_, _, _)
            | PureExpr::Forall { .. }
            | PureExpr::Exists { .. }
            | PureExpr::Match { .. } => false,
            // Tuple/Constructor/Absurd and any newly-added variants stay
            // conservative: they require the full encoder context.
            _ => true,
        }
    })
}

/// Create a fresh encoder with sort hints registered for the given expressions.
///
/// Delegates to [`bootstrap_encoder`] for encoder creation, logic selection,
/// sort hint registration, logic function prescan, type invariant registration,
/// datatype predeclaration, domain hint propagation, and variable predeclaration.
/// This eliminates the manual parity maintenance previously needed between
/// this function and `setup_verification_encoder`. (#2195)
///
/// Uses `Prefiltered` for logic fns and type invariants because the loop path
/// pre-filters once in `verify_loop_invariant_inner` against all loop
/// expressions. Sub-checks (preservation, variant) reuse the pre-filtered set
/// without re-filtering against their specific expression subset.
pub(in crate::verify::loops) fn setup_loop_encoder(
    invariants: &[PureExpr],
    loop_condition: Option<&PureExpr>,
    extra_exprs: &[&[PureExpr]],
    config: &LoopEncoderConfig<'_>,
) -> Result<AYEncoder, EncodingError> {
    use crate::verify::setup::{
        bootstrap_encoder, BootstrapRequest, ExprSlice, LogicFnInput, TypeInvariantInput,
    };

    // Invariants and loop condition are formula-level (need Bool hints).
    // Extra expressions (body effects, variant) are value-level.
    let cond_vec: Vec<PureExpr> = loop_condition.into_iter().cloned().collect();
    let mut expr_slices: Vec<ExprSlice<'_>> = vec![ExprSlice::formula(invariants)];
    if !cond_vec.is_empty() {
        expr_slices.push(ExprSlice::formula(&cond_vec));
    }
    for exprs in extra_exprs {
        expr_slices.push(ExprSlice::value(exprs));
    }

    bootstrap_encoder(BootstrapRequest {
        expr_slices: &expr_slices,
        result_postconditions: None,
        result_expr: None,
        logic_fns: config.logic_fns.map(LogicFnInput::PrefilteredGroundOnly),
        mode_overrides: config.mode_overrides,
        type_invariants: config.type_invariants.map(TypeInvariantInput::Prefiltered),
        track: config.track.unwrap_or_default(),
        timeout: config.timeout,
        type_constants: config.type_constants,
        closure_captures: None,
        adt_decls: config.adt_decls,
        adt_field_ranges: config.adt_field_ranges,
    })
}

/// Pure sort-decision plan for loop-modified variables. (#2020 Slice 2)
///
/// Separates "what sort should each modified variable get?" from the encoder
/// mutation that declares them. This mirrors the `SortPlan` pattern from
/// Slice 1 at the loop-verification level.
///
/// Built by [`collect_loop_sort_plan`], applied by [`LoopSortPlan::apply`].
#[derive(Debug)]
pub(in crate::verify::loops) struct LoopSortPlan {
    /// Planned sorts for modified variables, in declaration order.
    modified_var_sorts: Vec<(String, Sort)>,
}

impl LoopSortPlan {
    /// Apply the planned modified-variable declarations to the encoder. (#2020)
    ///
    /// Pre-declaration ensures later `encode_pure` calls get correctly-typed
    /// variables from the cache (#546, mirrors #543 fix for _final vars).
    pub(in crate::verify::loops) fn apply(
        &self,
        encoder: &mut AYEncoder,
    ) -> Result<(), EncodingError> {
        for (name, sort) in &self.modified_var_sorts {
            encoder.get_or_declare_var(name, sort.clone())?;
        }
        Ok(())
    }

    pub(in crate::verify::loops) fn sort_for(&self, name: &str) -> Option<&Sort> {
        self.modified_var_sorts
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, s)| s)
    }
}

/// Collect loop sort decisions without declaring variables. (#2020 Slice 2)
///
/// Phase 1: Propagate Bool marks from modified variables to body effect
/// target names. If `done` is Bool and effect is `Var("flag")`, then `flag`
/// is marked Bool too. (#544, #849)
///
/// Phase 2: Determine the sort each modified variable should be declared
/// with, using Bool state (from phase 1), context-aware inference for effect
/// expressions, and havoc-resolution for unconstrained variables.
///
/// The returned [`LoopSortPlan`] can be applied later via
/// [`LoopSortPlan::apply`]. Bool propagation is applied during collection
/// (lightweight mutation) because sort inference depends on it.
pub(in crate::verify::loops) fn collect_loop_sort_plan(
    encoder: &mut AYEncoder,
    modified_vars: &[&str],
    body_effect: &HashMap<String, PureExpr>,
) -> LoopSortPlan {
    // Phase 1: Propagate Bool marks.
    for var in modified_vars {
        if encoder.is_bool_var(var) {
            if let Some(effect_expr) = body_effect.get(*var) {
                if let Some(name) = extract_base_var_name(effect_expr) {
                    encoder.mark_bool_var(name);
                } else if let PureExpr::LogicFnCall { name, .. } = effect_expr {
                    // LogicFnCall effects need Bool hint via SMT name (#849).
                    let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
                    encoder.mark_bool_var(&smt_name);
                }
            }
        }
    }

    // Phase 2: Determine sorts (reads encoder state, may record unsoundness).
    let modified_var_sorts = modified_vars
        .iter()
        .map(|var| {
            let sort = if encoder.is_bool_var(var) {
                Sort::Bool
            } else if let Some(effect_expr) = body_effect.get(*var) {
                // Context-aware inference so LogicFnCall effects returning
                // Bool/Seq are not misclassified as Int. (#1965)
                let effect_sort = encoder.infer_expr_sort_with_context(effect_expr, None);
                if effect_sort == Sort::Int {
                    encoder
                        .resolve_var_sort(var)
                        .filter(|sort| *sort != Sort::Int)
                        .unwrap_or(effect_sort)
                } else {
                    effect_sort
                }
            } else {
                // Havoc: consult declared sorts, sort hints, and suffix-derived
                // base sorts so Seq/Bool/Datatype vars get the correct sort
                // instead of defaulting to Int. (#1319, #740, #1608)
                encoder.resolve_var_sort_or_int(var)
            };
            ((*var).to_string(), sort)
        })
        .collect();

    LoopSortPlan { modified_var_sorts }
}

/// Legacy wrapper: collect sort plan and apply immediately. (#2020)
///
/// All production callers migrated to `collect_loop_sort_plan` + `apply`.
/// Retained for existing tests that validate the combined behavior.
#[cfg(test)]
pub(in crate::verify::loops) fn propagate_bool_and_predeclare(
    encoder: &mut AYEncoder,
    modified_vars: &[&str],
    body_effect: &HashMap<String, PureExpr>,
) -> Result<(), EncodingError> {
    let plan = collect_loop_sort_plan(encoder, modified_vars, body_effect);
    plan.apply(encoder)
}

/// Encode and assert the loop condition.
pub(in crate::verify::loops) fn encode_and_assert_condition(
    encoder: &mut AYEncoder,
    cond: &PureExpr,
) -> Result<(), EncodingError> {
    let cond_term = encoder.encode_pure(cond)?;
    let cond_term = split_int_disequality_hypothesis(encoder, cond_term);
    encoder.assert_term(cond_term);
    Ok(())
}

/// Re-spell a top-level INTEGER disequality HYPOTHESIS as its two-sided
/// integer split: `a != b` becomes `a + 1 <= b \/ b + 1 <= a`.
///
/// Equivalence, not strengthening. Over `Int` the two formulas have exactly the
/// same models: `a != b` iff `a < b` or `b < a`, and over the integers `a < b`
/// iff `a + 1 <= b`. Nothing is added to or removed from the hypothesis.
///
/// Why it is needed. `a != b` is the ONE arithmetic literal Farkas' lemma
/// cannot use: ay's certificate checker case-splits a weighted disequality into
/// its two STRICT branches and, unlike an ordinary strict row, those branches
/// carry no integer strengthening. So a conflict whose refutation needs
/// `a <= b` plus `a != b` to yield `a + 1 <= b` has no Farkas certificate at
/// all — over the rationals the negation is genuinely satisfiable (`a = 0`,
/// `b = 1/2`). The theory solver still closes it correctly, but can only record
/// the closure as a `TheoryLemmaKind::Generic` trust lemma, and the mandatory
/// strict certification then refuses the UNSAT
/// (`step tN uses unsupported theory lemma kind Generic in strict mode`), which
/// trust-wp reports as `Unknown(ProofTrusted)` for a genuinely valid
/// obligation. Presented as the split, each branch is an ordinary integer bound
/// and the SAME refutation comes back with a hole-free `la_generic` proof.
///
/// The strengthening must be in the FORMULA: the weaker split `a < b \/ b < a`
/// does not help, because it hands the checker exactly the two unstrengthened
/// strict rows the disequality already produced.
///
/// Scope and fail-closed conditions. This fires ONLY on a loop condition
/// asserted as a hypothesis (`invariant /\ condition => ...`, and the
/// entry-may-execute probe), only on the exact `(not (= a b))` shape, and only
/// when the solver reports BOTH sides as `Sort::Int`. The `Int` test is
/// load-bearing and is taken from ay's own term store rather than from
/// trust-wp's sort inference: over `Real` the rewrite would be a genuine
/// STRENGTHENING of the hypothesis (it excludes `a = b + 1/2`) and therefore
/// unsound. Any other shape, sort, or an inconclusive sort is returned
/// unchanged.
fn split_int_disequality_hypothesis(
    encoder: &mut AYEncoder,
    cond_term: ay_dpll::api::Term,
) -> ay_dpll::api::Term {
    use ay_dpll::api::TermKind;

    if !matches!(encoder.solver().term_kind(cond_term), TermKind::Not) {
        return cond_term;
    }
    let [equality] = encoder.solver().term_children(cond_term)[..] else {
        return cond_term;
    };
    if !matches!(
        encoder.solver().term_kind(equality),
        TermKind::App { ref name, num_args } if name == "=" && num_args == 2
    ) {
        return cond_term;
    }
    let [lhs, rhs] = encoder.solver().term_children(equality)[..] else {
        return cond_term;
    };
    if encoder.solver().term_sort(lhs) != Sort::Int || encoder.solver().term_sort(rhs) != Sort::Int
    {
        return cond_term;
    }

    let solver = encoder.solver_mut();
    let one = solver.int_const(1);
    let lhs_next = solver.add(lhs, one);
    let rhs_next = solver.add(rhs, one);
    let lhs_below = solver.le(lhs_next, rhs);
    let rhs_below = solver.le(rhs_next, lhs);
    solver.or(lhs_below, rhs_below)
}

/// Assert `_current`-chain aliases needed by loop obligations.
///
/// Loop invariants and loop conditions can contain nested dereference/final
/// projections (`*x`, `**x`, `^(*x)`), which encode to names like
/// `x_current_current`. We only connect `_current` chains (for example
/// `x_current_current = x_current`) via the shared function-level helper, so
/// deep chains stay linked without forcing
/// base identities (`x_current = x`) that can over-constrain mut refs.
pub(in crate::verify::loops) fn assert_loop_current_chain_alias_constraints(
    encoder: &mut AYEncoder,
) -> Result<(), EncodingError> {
    super::super::shared_constraints::assert_current_chain_alias_constraints(encoder)
}

/// Timed version of [`resolve_sat_result_lightweight`].
///
/// Wraps the solve in [`run_with_hard_timeout`] to guard against ay-dpll
/// solver hangs on loop VCs. Returns [`ResolveContinuation::Continue`] on
/// normal completion and [`ResolveContinuation::Abort`] when the hard-timeout
/// deadline expires. (#2457)
pub(in crate::verify::loops) fn resolve_sat_result_lightweight_timed(
    encoder: &mut AYEncoder,
) -> crate::verify::hard_timeout::ResolveContinuation {
    crate::verify::hard_timeout::run_with_hard_timeout(encoder, resolve_sat_result_lightweight)
}

const LOOP_INITIALIZATION_NEGATED_GOAL_LABEL_PREFIX: &str =
    "__trust_wp_loop_initialization_negated_goal";
const LOOP_EMPTY_INITIALIZATION_NEGATED_GOAL_LABEL_PREFIX: &str =
    "__trust_wp_loop_empty_initialization_negated_goal";
const LOOP_EMPTY_POSTCONDITION_NEGATED_GOAL_LABEL_PREFIX: &str =
    "__trust_wp_loop_empty_postcondition_negated_goal";
const LOOP_EMPTY_PRESERVATION_NEGATED_GOAL_LABEL_PREFIX: &str =
    "__trust_wp_loop_empty_preservation_negated_goal";

/// Loop-initialization resolver that disables UNSAT shortcuts.
///
/// Initialization VCs are negated-goal solves, so they need real ay solve
/// details/proof evidence for `Verified` results. Setting a negated-goal label
/// prefix uses the solver's existing shortcut gate to send direct Bool
/// conflicts through ay instead of accepting shortcut UNSAT provenance.
pub(in crate::verify::loops) fn resolve_loop_initialization_sat_result_lightweight(
    encoder: &mut AYEncoder,
) -> VerificationResult {
    encoder.with_negated_goal_label_prefix(
        LOOP_INITIALIZATION_NEGATED_GOAL_LABEL_PREFIX.to_string(),
        resolve_sat_result_lightweight,
    )
}

/// Timed version of [`resolve_loop_initialization_sat_result_lightweight`].
pub(in crate::verify::loops) fn resolve_loop_initialization_sat_result_lightweight_timed(
    encoder: &mut AYEncoder,
) -> crate::verify::hard_timeout::ResolveContinuation {
    crate::verify::hard_timeout::run_with_hard_timeout(
        encoder,
        resolve_loop_initialization_sat_result_lightweight,
    )
}

/// Prove the empty loop postcondition with real solver evidence.
///
/// Empty `ensures` is the identity element of conjunction, so its negated goal
/// is `false`. We still run that tiny query through ay with UNSAT shortcuts
/// disabled so evidence consumers do not see a `Verified(None)` phase gap.
pub(in crate::verify::loops) fn prove_empty_postcondition_outcome(
    config: &LoopEncoderConfig<'_>,
) -> Result<VerificationOutcome, EncodingError> {
    prove_false_loop_goal_outcome(config, LOOP_EMPTY_POSTCONDITION_NEGATED_GOAL_LABEL_PREFIX)
}

/// Prove an empty initialization VC with real solver evidence.
pub(in crate::verify::loops) fn prove_empty_initialization_outcome(
    config: &LoopEncoderConfig<'_>,
) -> Result<VerificationOutcome, EncodingError> {
    prove_false_loop_goal_outcome(config, LOOP_EMPTY_INITIALIZATION_NEGATED_GOAL_LABEL_PREFIX)
}

/// Prove an empty preservation VC with real solver evidence.
pub(in crate::verify::loops) fn prove_empty_preservation_outcome(
    config: &LoopEncoderConfig<'_>,
) -> Result<VerificationOutcome, EncodingError> {
    prove_false_loop_goal_outcome(config, LOOP_EMPTY_PRESERVATION_NEGATED_GOAL_LABEL_PREFIX)
}

/// Prove a structurally-discharged loop VC with real solver evidence.
///
/// Structural loop checks have already established that the negated VC is
/// equivalent to `false`; this helper records that tiny UNSAT proof so legacy
/// callers that require accepted evidence do not demote the phase to Unknown.
pub(in crate::verify::loops) fn prove_structural_loop_goal_outcome(
    config: &LoopEncoderConfig<'_>,
    negated_goal_label_prefix: &str,
) -> Result<VerificationOutcome, EncodingError> {
    prove_false_loop_goal_outcome(config, negated_goal_label_prefix)
}

fn prove_false_loop_goal_outcome(
    config: &LoopEncoderConfig<'_>,
    negated_goal_label_prefix: &str,
) -> Result<VerificationOutcome, EncodingError> {
    use crate::verify::setup::{
        bootstrap_encoder, BootstrapRequest, ExprSlice, LogicFnInput, TypeInvariantInput,
    };

    let expr_slices: [ExprSlice<'_>; 0] = [];
    let before_bootstrap = crate::encoder::unsoundness::snapshot();
    let mut encoder = bootstrap_encoder(BootstrapRequest {
        expr_slices: &expr_slices,
        result_postconditions: None,
        result_expr: None,
        logic_fns: config.logic_fns.map(LogicFnInput::PrefilteredGroundOnly),
        mode_overrides: config.mode_overrides,
        type_invariants: config.type_invariants.map(TypeInvariantInput::Prefiltered),
        track: config.track.unwrap_or_default(),
        timeout: config.timeout,
        type_constants: config.type_constants,
        closure_captures: None,
        adt_decls: config.adt_decls,
        adt_field_ranges: config.adt_field_ranges,
    })?;
    let post_bootstrap = crate::encoder::unsoundness::snapshot();
    // This is a secondary evidence encoder created after the caller's
    // demotion baseline. Its declaration scan replays the same analytical
    // logic-function sort fallbacks that the primary loop encoder absorbs in
    // its post-bootstrap snapshot. Remove exactly that bootstrap-only delta;
    // any approximation fired while constructing or solving the false goal
    // below remains visible and demoting.
    crate::encoder::unsoundness::absorb_secondary_bootstrap_false_positives(
        &before_bootstrap,
        &post_bootstrap,
    );

    Ok(
        encoder.with_negated_goal_label_prefix(negated_goal_label_prefix.to_string(), |encoder| {
            encoder.with_assertion_phase(AssertionPhase::NegatedPostcondition, |encoder| {
                let false_term = encoder.solver_mut().bool_const(false);
                encoder.assert_term(false_term);
            });
            resolve_sat_result_lightweight_outcome_timed(encoder)
        }),
    )
}

/// Timed loop-initialization solve that captures provenance on completion.
pub(in crate::verify::loops) fn resolve_loop_initialization_sat_result_lightweight_outcome_timed(
    encoder: &mut AYEncoder,
) -> VerificationOutcome {
    let solve_start = Instant::now();
    match resolve_loop_initialization_sat_result_lightweight_timed(encoder) {
        crate::verify::hard_timeout::ResolveContinuation::Continue(result) => {
            outcome_from_continue(result, encoder, solve_start.elapsed())
        }
        crate::verify::hard_timeout::ResolveContinuation::Abort(result) => {
            VerificationOutcome::without_provenance(result)
        }
    }
}

pub(in crate::verify::loops) enum OutcomeContinuation {
    Continue(VerificationOutcome),
    Abort(VerificationOutcome),
}

/// Timed lightweight solve that captures provenance on normal completion.
///
/// Hard-timeout aborts intentionally return without provenance because the live
/// encoder remains owned by the abandoned worker thread.
pub(in crate::verify::loops) fn resolve_sat_result_lightweight_outcome_timed(
    encoder: &mut AYEncoder,
) -> VerificationOutcome {
    let solve_start = Instant::now();
    match resolve_sat_result_lightweight_timed(encoder) {
        crate::verify::hard_timeout::ResolveContinuation::Continue(result) => {
            outcome_from_continue(result, encoder, solve_start.elapsed())
        }
        crate::verify::hard_timeout::ResolveContinuation::Abort(result) => {
            VerificationOutcome::without_provenance(result)
        }
    }
}

fn outcome_from_continue(
    result: VerificationResult,
    encoder: &mut AYEncoder,
    elapsed: std::time::Duration,
) -> VerificationOutcome {
    if continue_result_without_solver_run(&result) {
        VerificationOutcome::without_provenance(result)
    } else {
        VerificationOutcome::new(result, Some(encoder.capture_provenance(elapsed)))
    }
}

fn continue_result_without_solver_run(result: &VerificationResult) -> bool {
    match result {
        VerificationResult::Unknown(crate::verify::UnknownReason::ResourceOut) => true,
        VerificationResult::Unknown(crate::verify::UnknownReason::SolverMessage(message)) => {
            message.starts_with("failed to spawn hard-timeout worker:")
        }
        _ => false,
    }
}

/// Run a loop obligation inside a push/pop scope with hard timeout (#2457).
///
/// Lifecycle:
/// 1. `push_scope()`
/// 2. `build_goal(encoder)` — encode negated goal, axioms, ground pool, etc.
/// 3. Timed solve via [`resolve_sat_result_lightweight_timed`]
/// 4. On `Continue(result)`: `pop_scope()` and return `Continue(result)`
/// 5. On `Abort(result)`: return `Abort(result)` without `pop_scope()`
/// 6. On `Err` from `build_goal`: `pop_scope()` and bubble the error
///
/// The "never pop on Abort" rule matches the shared pipeline's behavior in
/// [`crate::verify::pipeline`]: when the hard timeout fires, the live encoder
/// is owned by the worker thread and `pop_scope()` on the placeholder would
/// corrupt state.
pub(in crate::verify::loops) fn solve_scoped_loop_obligation(
    encoder: &mut AYEncoder,
    build_goal: impl FnOnce(&mut AYEncoder) -> Result<(), EncodingError>,
) -> Result<crate::verify::hard_timeout::ResolveContinuation, EncodingError> {
    encoder.push_scope()?;

    if let Err(err) = build_goal(encoder) {
        encoder.pop_scope()?;
        return Err(err);
    }

    let continuation = resolve_sat_result_lightweight_timed(encoder);
    if let crate::verify::hard_timeout::ResolveContinuation::Continue(_) = &continuation {
        encoder.pop_scope()?;
    }
    Ok(continuation)
}

/// Run a scoped loop obligation and capture provenance before popping the scope.
pub(in crate::verify::loops) fn solve_scoped_loop_obligation_outcome(
    encoder: &mut AYEncoder,
    build_goal: impl FnOnce(&mut AYEncoder) -> Result<(), EncodingError>,
) -> Result<OutcomeContinuation, EncodingError> {
    encoder.push_scope()?;

    if let Err(err) = build_goal(encoder) {
        encoder.pop_scope()?;
        return Err(err);
    }

    let solve_start = Instant::now();
    match resolve_sat_result_lightweight_timed(encoder) {
        crate::verify::hard_timeout::ResolveContinuation::Continue(result) => {
            let outcome = outcome_from_continue(result, encoder, solve_start.elapsed());
            encoder.pop_scope()?;
            Ok(OutcomeContinuation::Continue(outcome))
        }
        crate::verify::hard_timeout::ResolveContinuation::Abort(result) => Ok(
            OutcomeContinuation::Abort(VerificationOutcome::without_provenance(result)),
        ),
    }
}

/// Run a loop-initialization obligation inside a push/pop scope.
///
/// Unlike the generic loop scoped helper, this keeps a negated-goal label
/// prefix active through goal construction and solving so UNSAT shortcuts stay
/// disabled for initialization-specific proof evidence.
pub(in crate::verify::loops) fn solve_scoped_loop_initialization_obligation(
    encoder: &mut AYEncoder,
    build_goal: impl FnOnce(&mut AYEncoder) -> Result<(), EncodingError>,
) -> Result<crate::verify::hard_timeout::ResolveContinuation, EncodingError> {
    encoder.with_negated_goal_label_prefix(
        LOOP_INITIALIZATION_NEGATED_GOAL_LABEL_PREFIX.to_string(),
        |encoder| solve_scoped_loop_obligation(encoder, build_goal),
    )
}

/// Run a scoped loop-initialization obligation and capture provenance.
pub(in crate::verify::loops) fn solve_scoped_loop_initialization_obligation_outcome(
    encoder: &mut AYEncoder,
    build_goal: impl FnOnce(&mut AYEncoder) -> Result<(), EncodingError>,
) -> Result<OutcomeContinuation, EncodingError> {
    encoder.with_negated_goal_label_prefix(
        LOOP_INITIALIZATION_NEGATED_GOAL_LABEL_PREFIX.to_string(),
        |encoder| solve_scoped_loop_obligation_outcome(encoder, build_goal),
    )
}

/// Run a loop obligation inside a scoped solve and recheck the popped live base.
///
/// This wrapper preserves [`solve_scoped_loop_obligation`] semantics, but when
/// the scoped negated-goal solve returns `Continue(Verified)`, it immediately
/// re-solves the popped base with inverted vacuity semantics. This matches the
/// shared function pipeline and prevents vacuous loop postcondition proofs from
/// reporting `Verified`. (#2622)
pub(in crate::verify::loops) fn solve_scoped_loop_obligation_with_base_recheck(
    encoder: &mut AYEncoder,
    build_goal: impl FnOnce(&mut AYEncoder) -> Result<(), EncodingError>,
) -> Result<crate::verify::hard_timeout::ResolveContinuation, EncodingError> {
    let continuation = solve_scoped_loop_obligation(encoder, build_goal)?;

    if let crate::verify::hard_timeout::ResolveContinuation::Continue(
        core_verified @ VerificationResult::Verified(_),
    ) = continuation
    {
        let base_result = crate::verify::solver_tail::run_base_recheck_with_tight_timeout(encoder);
        // When the scoped solve proved UNSAT but the base recheck returns
        // Unknown, surface that as a visible gap rather than a clean proof.
        return Ok(
            crate::verify::solver_tail::prefer_non_vacuous_core_on_incomplete_base(
                core_verified,
                base_result,
            ),
        );
    }

    Ok(continuation)
}

/// Run a scoped loop obligation with base recheck and provenance.
///
/// A successful core proof keeps the scoped obligation provenance. If the base
/// recheck changes the result to vacuous/unknown/failed, the returned outcome
/// carries base-recheck provenance instead.
pub(in crate::verify::loops) fn solve_scoped_loop_obligation_with_base_recheck_outcome(
    encoder: &mut AYEncoder,
    build_goal: impl FnOnce(&mut AYEncoder) -> Result<(), EncodingError>,
) -> Result<OutcomeContinuation, EncodingError> {
    let core_outcome = match solve_scoped_loop_obligation_outcome(encoder, build_goal)? {
        OutcomeContinuation::Continue(outcome) => outcome,
        abort @ OutcomeContinuation::Abort(_) => return Ok(abort),
    };
    let core_result = core_outcome.result.clone();

    if !matches!(core_result, VerificationResult::Verified(_)) {
        return Ok(OutcomeContinuation::Continue(core_outcome));
    }

    let base_start = Instant::now();
    let base_result = crate::verify::solver_tail::run_base_recheck_with_tight_timeout(encoder);
    let base_elapsed = base_start.elapsed();
    match crate::verify::solver_tail::prefer_non_vacuous_core_on_incomplete_base(
        core_result,
        base_result,
    ) {
        crate::verify::hard_timeout::ResolveContinuation::Continue(
            VerificationResult::Verified(_),
        ) => Ok(OutcomeContinuation::Continue(core_outcome)),
        crate::verify::hard_timeout::ResolveContinuation::Continue(result) => Ok(
            OutcomeContinuation::Continue(outcome_from_continue(result, encoder, base_elapsed)),
        ),
        crate::verify::hard_timeout::ResolveContinuation::Abort(result) => Ok(
            OutcomeContinuation::Abort(VerificationOutcome::without_provenance(result)),
        ),
    }
}
