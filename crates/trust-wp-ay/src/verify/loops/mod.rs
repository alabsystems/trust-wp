// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Loop invariant verification.
//!
//! Implements the inductive proof strategy for verifying loops with invariants:
//!
//! 1. **Initialization**: precondition => invariant
//! 2. **Preservation**: invariant /\ condition => invariant'
//! 3. **Postcondition**: invariant /\ !condition => ensures
//! 4. **Variant non-negative** (optional): invariant /\ condition => variant >= 0
//! 5. **Variant decrease** (optional): invariant /\ condition => variant' < variant

mod context;
mod encoder_setup;
mod expr_helpers;
mod initialization;
mod invariant_transforms;
mod postcondition;
mod preservation;
mod prime_substitutions;
pub(crate) mod recursive_unfolding;
mod variant;

use std::{
    collections::{HashMap, HashSet},
    panic::AssertUnwindSafe,
    sync::Arc,
    time::{Duration, Instant},
};

use tracing::debug;
use trust_wp_core::{
    formula::{BinOp, ExprSort, PureExpr},
    logic::{is_invariant_method_name, LogicFnDef, LogicMode},
};

pub use self::context::{BodyEffects, LoopEncoderConfig, LoopVerificationContext};
pub(crate) use self::context::{LoopVcBase, PostconditionInputs};
// Test-only re-export for crate-level test access.
#[cfg(test)]
pub(crate) use self::preservation::verify_preservation;
use self::{
    expr_helpers::strip_scalar_views,
    initialization::{loop_entry_may_execute_outcome, verify_initialization_outcome},
    postcondition::verify_postcondition_outcome,
    preservation::verify_preservation_with_config_outcome,
    variant::{verify_variant_decrease_outcome, verify_variant_nonneg_outcome},
};
use super::{
    catch_ay_sort_panics_outcome, process_isolation, LoopVerificationOutcome,
    LoopVerificationResult, ProofCertificateSummary, VerificationOutcome, VerificationResult,
};
use crate::{error::EncodingError, logic::filter_logic_fn_indices_for_goal};

/// The proof authority a non-executing loop's vacuously-discharged phases carry.
///
/// `may_execute == false` is decided by exactly ONE obligation: the entry check
/// refuted `requires /\ pre-loop assignments /\ condition`. That refutation is
/// the entire justification for discharging preservation and the variant
/// obligations — the body never runs, so no iteration exists to violate them —
/// so it is also the evidence those phases must present at the mandatory
/// proof-authority boundary (`apply_mandatory_proof_authority`).
///
/// Those phases already report the entry solve as their provenance
/// (`nonexecuting_loop_provenance`, cloned from the same `VerificationOutcome`).
/// Returning `Verified(None)` next to that provenance dropped the certificate
/// minted by the very solve being cited, so the boundary demoted a verdict that
/// IS backed by a strictly checked, hole-free, trust-free proof to
/// `Unknown(ProofTrusted)` — the #1709 short-circuit defeating itself.
///
/// Fail-closed, and it cannot manufacture authority: ONLY a certificate that
/// already satisfies `ProofCertificateSummary::is_fully_verified` is carried
/// over. An entry outcome with no summary, or one carrying any trust/hole step
/// or a failed strict verdict, still yields `Verified(None)` and is demoted
/// exactly as before. The gate's predicate is untouched; this supplies the
/// certificate the gate asks for instead of relaxing what it accepts.
fn nonexecuting_loop_proof_authority(
    entry_outcome: Option<&VerificationOutcome>,
) -> Option<ProofCertificateSummary> {
    match entry_outcome.map(|outcome| &outcome.result) {
        Some(VerificationResult::Verified(Some(summary))) if summary.is_fully_verified() => {
            Some(summary.clone())
        }
        _ => None,
    }
}

const LOOP_PHASE_MIN_TIMEOUT: Duration = Duration::from_secs(3);
const LOOP_CRITICAL_PHASE_MIN_TIMEOUT: Duration = Duration::from_secs(8);

fn loop_phase_timeout(
    total_budget: Option<Duration>,
    elapsed: Duration,
    remaining_phases: u32,
    minimum: Duration,
) -> Option<Duration> {
    match total_budget {
        Some(total) => {
            let remaining = total.saturating_sub(elapsed);
            // Distribute remaining time across remaining phases + 1 headroom.
            let per_phase = remaining / (remaining_phases + 1).max(1);
            let effective_minimum = minimum.min(total);
            Some(per_phase.max(effective_minimum))
        }
        // Unit test default: 5s per phase (unchanged from prior behavior).
        None => Some(Duration::from_secs(5)),
    }
}

/// Verify a loop with invariant using a [`LoopVerificationContext`].
///
/// All five verification conditions (initialization, preservation,
/// postcondition, variant non-negative, variant decrease) are dispatched
/// from here using fields in `ctx`.
///
/// # Errors
/// Returns `EncodingError` if encoding of expressions or formulas fails.
#[tracing::instrument(
    name = "trust_wp::verify_loop_invariant",
    level = "debug",
    skip_all,
    fields(
        invariants = ctx.invariants.len(),
        requires = ctx.requires.len(),
        ensures = ctx.ensures.len(),
        modified_vars = ctx.modified_vars.len(),
        has_variant = ctx.variant.is_some(),
    )
)]
pub fn verify_loop_invariant(
    ctx: &LoopVerificationContext<'_>,
) -> Result<LoopVerificationResult, EncodingError> {
    // Per-sub-check panic isolation (#2273): each sub-check inside
    // verify_loop_invariant_inner is wrapped in its own catch_unwind so
    // a ay panic in one phase does not discard results from other phases.
    Ok(legacy_loop_result_from_outcome(
        verify_loop_invariant_outcome(ctx)?,
    ))
}

fn legacy_loop_result_from_outcome(outcome: LoopVerificationOutcome) -> LoopVerificationResult {
    LoopVerificationResult {
        initialization: legacy_phase_result_from_outcome(outcome.initialization, "initialization"),
        preservation: legacy_phase_result_from_outcome(outcome.preservation, "preservation"),
        postcondition: legacy_phase_result_from_outcome(outcome.postcondition, "postcondition"),
        variant_nonneg: outcome
            .variant_nonneg
            .map(|outcome| legacy_phase_result_from_outcome(outcome, "variant_nonneg")),
        variant_decrease: outcome
            .variant_decrease
            .map(|outcome| legacy_phase_result_from_outcome(outcome, "variant_decrease")),
    }
}

fn legacy_phase_result_from_outcome(
    outcome: VerificationOutcome,
    phase: &str,
) -> VerificationResult {
    if !matches!(outcome.result, VerificationResult::Verified(_)) {
        return outcome.result;
    }
    if verified_outcome_has_accepted_evidence(&outcome) {
        return outcome.result;
    }
    VerificationResult::Unknown(legacy_verified_phase_evidence_gap_reason(&outcome, phase))
}

fn verified_outcome_has_accepted_evidence(outcome: &VerificationOutcome) -> bool {
    outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .is_some_and(|evidence| evidence.accepted_for_consumer)
}

fn legacy_verified_phase_evidence_gap_reason(
    outcome: &VerificationOutcome,
    phase: &str,
) -> super::UnknownReason {
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
    super::UnknownReason::SolverMessage(format!(
        "verified loop {phase} result lacks accepted solver evidence: {detail}"
    ))
}

/// Verify a loop invariant and retain per-phase provenance.
///
/// This is the diagnostics/replay-preserving entry point. The legacy
/// [`verify_loop_invariant`] wrapper drops provenance for existing callers.
pub fn verify_loop_invariant_outcome(
    ctx: &LoopVerificationContext<'_>,
) -> Result<LoopVerificationOutcome, EncodingError> {
    process_isolation::run_loop_outcome_in_child(ctx.config.timeout, || {
        verify_loop_invariant_inner_outcome(ctx)
    })
    .map(LoopVerificationOutcome::apply_mandatory_proof_authority)
}

/// Positional-parameter entry point for loop verification (test-only).
///
/// Constructs a [`LoopVerificationContext`] from individual parameters and
/// delegates to [`verify_loop_invariant`]. Retained for backward compatibility
/// with existing test call sites (#923).
#[cfg(test)]
pub(crate) fn verify_loop_invariant_positional(
    ctx: &LoopVerificationContext<'_>,
) -> Result<LoopVerificationResult, EncodingError> {
    verify_loop_invariant(ctx)
}

#[allow(clippy::too_many_lines)] // Central loop VC dispatcher keeps all obligations aligned.
fn verify_loop_invariant_inner(
    ctx: &LoopVerificationContext<'_>,
) -> Result<LoopVerificationResult, EncodingError> {
    Ok(legacy_loop_result_from_outcome(
        verify_loop_invariant_inner_outcome(ctx)?,
    ))
}

#[allow(clippy::too_many_lines)] // Central loop VC dispatcher keeps all obligations aligned.
fn verify_loop_invariant_inner_outcome(
    ctx: &LoopVerificationContext<'_>,
) -> Result<LoopVerificationOutcome, EncodingError> {
    let debug_timing = std::env::var("TRUST_WP_LOOP_DEBUG_TIMING").is_ok();
    let phase_start = Instant::now();
    let mut last_phase = phase_start;

    // Filter logic functions to those referenced in loop expressions (#739).
    // Also filter corresponding mode overrides when present (#757).
    let (filtered_logic_fns, filtered_modes) = filter_logic_fns_for_loop_ctx(ctx)?;
    // Budget the function-level timeout across loop sub-checks so the total
    // doesn't exceed the caller's wall-clock envelope. Without budgeting,
    // each sub-check consumes the full function timeout (e.g., 60s × 6 = 360s
    // for a loop with variant), far exceeding the per-function budget and
    // causing harness-level timeouts. (#2116)
    //
    // Phases: init, preservation, postcondition (3 base) + entry_may_execute,
    // variant_nonneg, variant_decrease (3 more if variant present).
    //
    // Dynamic budget carryover (#2116): phases that complete early donate
    // their unused time to subsequent phases. This prevents wasting budget
    // when simple phases (e.g., initialization proving `empty == empty`)
    // complete in milliseconds but were allocated 8+ seconds. The total
    // wall-clock stays within the original envelope while giving harder
    // phases (postcondition, preservation) more time to complete.
    let num_phases: u32 = if ctx.variant.is_some() { 6 } else { 3 };
    let total_budget = ctx.config.timeout;
    let phase_budget = |remaining_phases: u32| -> Option<Duration> {
        loop_phase_timeout(
            total_budget,
            phase_start.elapsed(),
            remaining_phases,
            LOOP_PHASE_MIN_TIMEOUT,
        )
    };
    let critical_phase_budget = |remaining_phases: u32| -> Option<Duration> {
        loop_phase_timeout(
            total_budget,
            phase_start.elapsed(),
            remaining_phases,
            LOOP_CRITICAL_PHASE_MIN_TIMEOUT,
        )
    };
    let make_config = |timeout: Option<Duration>| -> LoopEncoderConfig<'_> {
        LoopEncoderConfig {
            type_invariants: ctx.config.type_invariants,
            logic_fns: filtered_logic_fns.as_deref(),
            mode_overrides: filtered_modes.as_deref(),
            type_constants: ctx.config.type_constants,
            track: ctx.config.track,
            timeout,
            transition_facts: ctx.config.transition_facts.clone(),
            bridge_facts: ctx.config.bridge_facts.clone(),
            adt_decls: ctx.config.adt_decls,
            adt_field_ranges: ctx.config.adt_field_ranges,
            loop_element_borrow_vars: ctx.config.loop_element_borrow_vars.clone(),
        }
    };
    // Apply variable-alias substitutions from pre-loop assignments. (#1295)
    // When `let old_v = snapshot!(v)` creates `old_v = v`, substitute
    // `old_v → v` in invariants so that `old_v@.len() == v@.len()` becomes
    // `v@.len() == v@.len()`, avoiding UFLIA incompleteness from distinct
    // Seq-sorted View variables that share a value.
    // Only substitute aliases where NEITHER the alias NOR its target is
    // modified by the loop body — otherwise the substitution would be
    // incorrect for preservation/postcondition checks.
    let modified_set: HashSet<&str> = ctx.modified_vars.iter().copied().collect();
    let body_effects = ctx.body_effects();

    // Hard check: all body_effect keys must be in modified_vars. (#1884, #2626)
    // If a variable has a body effect but is NOT in modified_vars, the
    // postcondition VC would unsoundly constrain it via frame assignments
    // (asserting var == pre_loop_value) while the body modifies it.
    // This was previously `debug_assert!` (#1884) — promoted to hard error
    // because unsound frame constraints in release builds are unacceptable
    // for a verification tool. (#2626)
    for key in body_effects.keys() {
        if !modified_set.contains(key.as_str()) {
            return Err(EncodingError::Unsupported {
                message: format!(
                    "body effect variable `{key}` is not in modified_vars — this would cause \
                     unsound frame constraints in postcondition/preservation VCs. \
                     The driver's modified_vars computation may be incomplete. (#1884)"
                ),
                span: None,
                contract_text: None,
            });
        }
    }

    let alias_subs: HashMap<String, PureExpr> = ctx
        .pre_loop_assignments
        .iter()
        .filter(|(_, binding)| matches!(binding.value, PureExpr::Var(_, _)))
        .filter(|(name, binding)| {
            let target_name = match &binding.value {
                PureExpr::Var(n, _) => n.as_str(),
                _ => return false,
            };
            !modified_set.contains(name.as_str()) && !modified_set.contains(target_name)
        })
        .map(|(k, binding)| (k.clone(), binding.value.clone()))
        .collect();

    // Build snapshot variable set (#2665): variables in pre_loop_assignments
    // that are NOT modified by the loop body. These are immutable snapshot
    // locals where `Deref(Var(name))` is semantically identity and should be
    // stripped to `Var(name)` to avoid creating unlinked `name_current`
    // variables in the SMT encoding.
    let snapshot_vars: HashSet<&str> = ctx
        .pre_loop_assignments
        .keys()
        .filter(|name| !modified_set.contains(name.as_str()))
        .map(String::as_str)
        .collect();

    let normalize_scalar_views = |expr: &PureExpr| {
        let substituted = if alias_subs.is_empty() {
            expr.clone()
        } else {
            expr.substitute(&alias_subs)
        };
        let stripped = strip_scalar_views(&substituted);
        let stripped = expr_helpers::strip_snapshot_derefs(&stripped, &snapshot_vars);
        expr_helpers::strip_transparent_ghost_derefs(&stripped)
    };

    let strip_and_deref = |expr: &PureExpr| {
        let stripped = strip_scalar_views(expr);
        let stripped = expr_helpers::strip_snapshot_derefs(&stripped, &snapshot_vars);
        expr_helpers::strip_transparent_ghost_derefs(&stripped)
    };
    let normalized_requires: Vec<PureExpr> = ctx.requires.iter().map(strip_and_deref).collect();
    let normalized_ensures: Vec<PureExpr> = ctx.ensures.iter().map(strip_and_deref).collect();
    let normalized_init_extra_facts: Vec<PureExpr> =
        ctx.init_extra_facts.iter().map(strip_and_deref).collect();
    let normalized_post_extra_facts: Vec<PureExpr> =
        ctx.post_extra_facts.iter().map(strip_and_deref).collect();
    let normalized_return_expr = ctx.return_expr.map(strip_and_deref);
    let normalized_variant = ctx.variant.map(strip_and_deref);

    let substituted_invariants: Vec<PureExpr> =
        ctx.invariants.iter().map(normalize_scalar_views).collect();

    // Auto-invariants for unchanged variables (#1816).
    //
    // For variables in pre_loop_assignments that are NOT modified by the loop
    // body (and whose pre-loop value does not reference any modified variable),
    // generate `var == pre_loop_value` as an automatic loop invariant. This
    // is sound because:
    //   - Initialization: pre_loop_assignments already establish the equality.
    //   - Preservation: unmodified variables are not primed, so var' == var
    //     and the invariant is trivially preserved.
    //   - Postcondition: the auto-invariant provides the frame information
    //     that postconditions need to reason about unchanged locals.
    //
    // Previously the postcondition had its own frame_assignments for this
    // purpose, but those were not available during initialization or as
    // assumptions for other invariants. Promoting them to full loop invariants
    // makes them uniformly available across all verification phases.
    let auto_frame_invariants: Vec<PureExpr> = ctx
        .pre_loop_assignments
        .iter()
        .filter(|(name, binding)| {
            // Skip variables modified by the loop body.
            if modified_set.contains(name.as_str()) {
                return false;
            }
            // Skip variables whose pre-loop value references a modified
            // variable — those values change across iterations. (#2158)
            if expr_helpers::expr_references_any_var(&binding.value, &modified_set) {
                return false;
            }
            // Skip bindings with sort mismatches: when the variable's
            // declared sort is a non-Int type (Datatype, TypeParam, etc.)
            // but the pre-loop value is a bare Int literal. This happens
            // when lossy ADT translation (e.g., Some(10) → Int(10)) strips
            // the constructor. The resulting `var == Int(N)` equality would
            // trigger sort coercion to a fresh unconstrained constant,
            // making the preservation check trivially fail.
            if let Some(sort) = &binding.sort {
                let value_is_int_literal = matches!(binding.value, PureExpr::Int(_));
                let sort_expects_non_int =
                    !matches!(sort, ExprSort::Int | ExprSort::Bool | ExprSort::Float);
                if value_is_int_literal && sort_expects_non_int {
                    return false;
                }
            }
            // Skip bindings whose value is a Var carrying a `TypeParam` sort.
            // These come from pre-loop call resolution fallbacks where an
            // argument could not be translated and was replaced with a
            // synthetic `arg{N}` placeholder typed by a generic parameter
            // (see `translated_args_for_pre_loop_call` in the driver). The
            // TypeParam sort triggers `is_type_param_coercion` in
            // `sort_coercion.rs`, which injects unconstrained fresh constants
            // — those become spurious counterexamples for any preservation VC
            // that closes over this binding (bug/1743, #5226).
            if let PureExpr::Var(_, Some(ExprSort::TypeParam(_))) = &binding.value {
                return false;
            }
            true
        })
        .map(|(name, binding)| {
            let lhs = binding.lhs_var(name);
            let rhs = normalize_scalar_views(&binding.value);
            PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs))
        })
        .collect();

    // Auto type-invariant maintenance for unchanged variables (#1816).
    //
    // When a precondition asserts a type invariant on a variable (e.g.,
    // `x.invariant()` or `x.__trust_wp_invariant_NonZero()`), and that variable
    // is not modified by the loop body, the type invariant holds across all
    // iterations and can be auto-generated as a loop invariant. This is sound
    // because:
    //   - Initialization: the precondition already asserts the invariant.
    //   - Preservation: the variable is not primed (unmodified), so the
    //     invariant is trivially preserved.
    //   - Postcondition: the auto-invariant provides the type invariant as
    //     an assumption, enabling postconditions that depend on it.
    //
    // We scan `requires` for `MethodCall` expressions whose method is a type
    // invariant (detected by `is_invariant_method_name`) and whose receiver
    // is an unchanged variable (or `*var` for by-reference parameters).
    let auto_type_invariants: Vec<PureExpr> = ctx
        .requires
        .iter()
        .filter(|expr| {
            if let PureExpr::MethodCall {
                receiver, method, ..
            } = expr
            {
                if !is_invariant_method_name(method) {
                    return false;
                }
                // Extract the variable name from the receiver, peeling through
                // Deref, View, Old, and Final wrappers recursively. This handles
                // multi-level deref patterns (`**x.invariant()`) and view-wrapped
                // invariant receivers (`(*x)@.invariant()`). (#1816)
                if let Some(name) = peel_to_var_name(receiver) {
                    !modified_set.contains(name)
                } else {
                    false
                }
            } else {
                false
            }
        })
        .cloned()
        .collect();

    // Auto-promote stable requires as loop invariants (#1816).
    //
    // A requires clause whose free variables are ALL unmodified by the loop
    // body is trivially preserved across iterations: since none of its
    // variables change, its truth value cannot change either. Promoting such
    // clauses to loop invariants makes them available as assumptions during
    // initialization (vacuously — the requires already holds), preservation,
    // and postcondition checks. This is sound because:
    //   - Initialization: the requires is already asserted as a precondition.
    //   - Preservation: no primed variables appear in the clause, so the
    //     primed form is identical to the pre-iteration form.
    //   - Postcondition: the clause provides additional assumptions beyond
    //     what the postcondition already gets from unmodified_requires.
    //
    // The driver-side `infer_stable_loop_invariants` does this before calling
    // the ay layer, but repeating it here ensures correctness for direct ay
    // API usage (tests, standalone verification) and adds no overhead for the
    // driver path since the clauses are already in the invariant list.
    //
    // We skip clauses that are already present in the user-provided or
    // auto-generated invariants to avoid duplicate assertions.
    //
    // Conjunct splitting (#1816): when a requires is `a && b`, we
    // decompose it into individual conjuncts and evaluate each
    // independently. This allows promoting `y > 0` from `x > 0 && y > 0`
    // even when `x` is modified by the loop body. Without splitting, the
    // compound expression would be rejected because it references `x`.
    let auto_stable_requires: Vec<PureExpr> = {
        // Flatten AND-chains into individual conjuncts.
        let mut flat_requires: Vec<&PureExpr> = Vec::new();
        for req in ctx.requires {
            flatten_and_conjuncts(req, &mut flat_requires);
        }
        flat_requires
            .into_iter()
            .filter(|req| {
                // Only promote requires whose variables are all unmodified.
                if expr_helpers::expr_references_any_var(req, &modified_set) {
                    return false;
                }
                // Skip type invariant calls — already handled by auto_type_invariants above.
                if matches!(
                    req,
                    PureExpr::MethodCall { method, .. }
                    if is_invariant_method_name(method)
                ) {
                    return false;
                }
                // Skip trivial `true` literals — they add no information.
                if matches!(req, PureExpr::Bool(true)) {
                    return false;
                }
                // Skip clauses already in user invariants or auto-generated invariants.
                let normalized = normalize_scalar_views(req);
                !substituted_invariants.contains(&normalized)
                    && !auto_frame_invariants.contains(&normalized)
                    && !auto_type_invariants.contains(req)
            })
            .cloned()
            .collect()
    };

    // Auto-synthesize loop condition upper-bound invariants (#3315).
    //
    // When the loop condition is `var < bound` or `var <= bound` (for a
    // modified integer variable), auto-generate `var <= bound` as an
    // invariant. This is sound because:
    //   - Initialization: the loop condition is true at entry (otherwise the
    //     loop would not execute), so `var < bound` implies `var <= bound`.
    //     Even if the loop body never executes, `var <= bound` is still true
    //     at loop entry when the condition holds trivially or vacuously.
    //   - Preservation: if the user-written invariant + condition are strong
    //     enough to prove preservation on their own, this auto-invariant is
    //     redundant. If not, the user must supply a stronger invariant anyway.
    //     But in the common case where `var` is incremented by 1 and the
    //     condition is `var < bound`, `var + 1 <= bound` follows from the
    //     condition (since `var < bound` means `var + 1 <= bound`).
    //   - Postcondition: at loop exit, `NOT(var < bound)` gives `var >= bound`.
    //     Combined with the auto-invariant `var <= bound`, we get `var == bound`,
    //     which is exactly the missing fact for many Creusot compat tests.
    //
    // We only generate this when:
    //   - The bound variable is NOT modified by the loop body (constant bound).
    //   - The modified variable is not already bounded by an existing invariant.
    //   - The loop condition is a simple comparison (Lt or Le).
    // Condition-bound inference depends on loop structure (#2698).
    //
    // Both header-while and body-break store the CONTINUATION condition in
    // `loop_condition` (the driver's `find_body_break_condition` negates the
    // break predicate to produce continuation form).
    //
    // For header conditions (`while i < n`), the continuation `i < n` is
    // RELAXED to `i <= n` because the body may temporarily exceed the bound.
    //
    // For body-break (`loop { body; if i >= n { break } }`), the continuation
    // `i < n` is used DIRECTLY (no relaxation) because the post-body value
    // satisfying continuation IS the next loop-top value. This gives strict
    // bounds critical for postcondition proofs: `i < n AND NOT(i'<n) AND i'=i+1`
    // pins `i' = n`.
    let auto_condition_bound_invariants: Vec<PureExpr> = if ctx.condition_is_body_break {
        // Body-break: continuation condition IS the invariant (no relaxation).
        ctx.loop_condition
            .iter()
            .flat_map(|cond| {
                infer_body_break_condition_bound_invariants(
                    cond,
                    &modified_set,
                    &substituted_invariants,
                    &auto_frame_invariants,
                    &auto_stable_requires,
                    body_effects,
                )
            })
            .collect()
    } else {
        ctx.loop_condition
            .iter()
            .flat_map(|cond| {
                infer_condition_bound_invariants(
                    cond,
                    &modified_set,
                    &substituted_invariants,
                    &auto_frame_invariants,
                    &auto_stable_requires,
                    body_effects,
                )
            })
            .collect()
    };

    // Auto-synthesize lower-bound invariants from body effect monotonicity (#3315).
    //
    // When the body effect for a modified variable is `var + positive_constant`
    // (monotonically increasing) and the pre-loop assignment gives a concrete
    // initial value, auto-generate `var >= initial_value` as an invariant.
    // This is sound because:
    //   - Initialization: `var = initial_value` implies `var >= initial_value`.
    //   - Preservation: `var >= initial_value` and `var' = var + k` (k > 0)
    //     implies `var' >= initial_value + k >= initial_value`.
    //   - Postcondition: the lower bound provides a floor that enables
    //     reasoning about the variable's range at loop exit.
    //
    // Similarly, when the body effect is `var - positive_constant` (monotonically
    // decreasing), the loop condition typically provides the lower bound, so we
    // don't auto-synthesize an upper bound here (the condition bound inference
    // above handles that case).
    let auto_monotonicity_invariants: Vec<PureExpr> = infer_monotonicity_lower_bound_invariants(
        body_effects,
        ctx.pre_loop_assignments,
        &modified_set,
        &substituted_invariants,
        &auto_frame_invariants,
        &auto_condition_bound_invariants,
    );

    // Auto-synthesize counter correlation invariants (#2698).
    //
    // When two modified variables have the same monotone direction and
    // matching step sizes, their difference is constant across iterations.
    // For example, if `i` starts at 0 and `j` starts at 5, both
    // incrementing by 1, then `j == i + 5` is a loop invariant.
    //
    // This is sound because:
    //   - Initialization: `j = j_init` and `i = i_init`, so
    //     `j - i = j_init - i_init` (the offset).
    //   - Preservation: both vars change by the same amount k,
    //     so `j' - i' = (j + k) - (i + k) = j - i` (preserved).
    //   - Postcondition: the correlation provides additional facts
    //     connecting the two variables at loop exit.
    let auto_counter_correlation_invariants: Vec<PureExpr> = infer_counter_correlation_invariants(
        body_effects,
        ctx.pre_loop_assignments,
        &modified_set,
        &substituted_invariants,
        &auto_frame_invariants,
    );

    // Auto-synthesize constant-deref invariants (#2698).
    //
    // When the loop body has a deref effect `*x = expr` where `expr`
    // does not reference any modified variable (i.e., `expr` is constant
    // across iterations), generate `Deref(Var(x)) == expr` as a loop
    // invariant. This is sound because:
    //   - Initialization: the user must supply a matching precondition or
    //     invariant for init to pass. The auto-invariant is checked during
    //     init alongside user invariants.
    //   - Preservation: the body writes `*x = expr` every iteration, so
    //     `Deref(x)' == expr` trivially. Since `expr` is stable (no
    //     modified vars), `expr' == expr`.
    //   - Postcondition: provides the deref value at loop exit for borrow
    //     resolution reasoning (`x_final == x_current == expr`).
    //
    // Only generated when no existing invariant already covers the deref
    // equality. Skips variables whose deref effect references modified
    // variables (those change across iterations, so the equality is
    // not invariant).
    let auto_constant_deref_invariants: Vec<PureExpr> = infer_constant_deref_invariants(
        body_effects,
        &modified_set,
        &substituted_invariants,
        &auto_frame_invariants,
    );

    let combined_invariants: Vec<PureExpr> = substituted_invariants
        .iter()
        .cloned()
        .chain(auto_frame_invariants.iter().cloned())
        .chain(auto_type_invariants.iter().cloned())
        .chain(auto_stable_requires.iter().cloned())
        .chain(auto_condition_bound_invariants.iter().cloned())
        .chain(auto_monotonicity_invariants.iter().cloned())
        .chain(auto_counter_correlation_invariants.iter().cloned())
        .chain(auto_constant_deref_invariants.iter().cloned())
        .collect();
    let invariants = &combined_invariants[..];

    // Initialization-only invariant slice (B3 / while_let).
    //
    // `auto_constant_deref_invariants` synthesizes `*x == E` from the loop
    // body effect `*x = E`. This is sound for **preservation** (every
    // iteration overwrites `*x` to `E`) and **postcondition** (loop exit
    // sees `*x == E`), but it is NOT guaranteed at initialization: at loop
    // entry `*x` still holds the pre-loop value, which may not equal `E`.
    //
    // Example (`tests/should_succeed/lang/while_let.rs`):
    //   let mut a = Some(10);
    //   let b = &mut a;
    //   while let Some(_) = b { *b = None; }   // body effect: *b = None
    // Pre-loop `*b == Some(10)`, body assigns `*b = None`, so the auto
    // deref invariant `*b == None` is FALSE at entry and the
    // initialization VC fails with a counterexample.
    //
    // Excluding these auto deref invariants from initialization is sound:
    // - preservation/postcondition still consume the full `invariants`
    //   slice, so frame information from `auto_constant_deref` is
    //   preserved across iterations and at loop exit.
    // - existing tests for the auto deref pipeline (e.g.,
    //   `auto_constant_deref_invariant_basic`) already require an
    //   explicit `requires(*x == E)` to establish the deref equality
    //   at entry, so they are unaffected.
    let init_invariants: Vec<PureExpr> = combined_invariants
        .iter()
        .filter(|inv| !auto_constant_deref_invariants.contains(inv))
        .cloned()
        .collect();

    // Apply alias substitutions to the loop condition (#2093).
    // Without this, the preservation/postcondition VCs use mismatched variable
    // names: invariants reference the substituted alias (e.g., `n`) while the
    // condition still references the original (e.g., `bound`). This creates
    // unsound VCs where the aliased variable is unconstrained.
    let substituted_condition: Option<PureExpr> = ctx.loop_condition.map(normalize_scalar_views);
    let loop_condition_ref = substituted_condition.as_ref().or(ctx.loop_condition);

    // 1. Verify initialization: requires ∧ pre-loop assignments ∧ init_extra => invariant
    // Per-sub-check panic isolation (#2273): a ay panic here does not affect
    // preservation/postcondition/variant results.
    // Demotion is handled inside verify_initialization using a post-bootstrap
    // snapshot, absorbing SortFallbackToIntFromLogicFn bootstrap noise. (#2062)
    let init_config = make_config(phase_budget(num_phases));
    let init_base = LoopVcBase {
        invariants: &init_invariants,
        loop_condition: loop_condition_ref,
        condition_is_body_break: ctx.condition_is_body_break,
        modified_vars: ctx.modified_vars,
        effects: body_effects,
        config: &init_config,
    };
    let initialization = catch_ay_sort_panics_outcome(AssertUnwindSafe(|| {
        verify_initialization_outcome(
            &init_base,
            &normalized_requires,
            ctx.pre_loop_assignments,
            &normalized_init_extra_facts,
        )
    }))?;
    if debug_timing {
        let now = Instant::now();
        debug!(
            "[loop-timing] initialization: {:?} (total {:?})",
            now.duration_since(last_phase),
            now.duration_since(phase_start)
        );
        last_phase = now;
    }

    // 2. Entry-may-execute guard (#1709): check if the loop condition is
    // satisfiable under preconditions. If UNSAT, the loop body never
    // executes, so preservation is vacuously valid (Verified) and variant
    // obligations are trivially met. Without this early check, the
    // preservation vacuity guard demotes the contradictory base
    // (invariants ∧ condition) to Unknown, even though a non-executing
    // loop is a perfectly valid scenario (e.g., `#[requires(!x)] while x {}`).
    //
    // This check runs unconditionally when a loop condition is present,
    // not only when variants are specified. Postcondition still runs
    // because the loop-exit state (¬condition) is reached immediately.
    let entry_outcome = if loop_condition_ref.is_some() {
        let entry_config = make_config(phase_budget(num_phases));
        super::catch_ay_panics_tightened(
            AssertUnwindSafe(|| {
                loop_entry_may_execute_outcome(
                    &normalized_requires,
                    ctx.pre_loop_assignments,
                    loop_condition_ref,
                    &entry_config,
                )
            }),
            |reason| {
                debug!("trust-wp: ay solver panic in loop_entry_may_execute: {reason}");
                Ok(initialization::LoopEntryOutcome {
                    may_execute: true,
                    outcome: Some(VerificationOutcome::without_provenance(
                        VerificationResult::Unknown(super::UnknownReason::SolverMessage(format!(
                            "ay solver panic in loop_entry_may_execute: {reason}"
                        ))),
                    )),
                })
            },
        )?
    } else {
        initialization::LoopEntryOutcome {
            may_execute: true,
            outcome: None,
        }
    };
    let may_execute = entry_outcome.may_execute;
    let entry_may_execute = entry_outcome.outcome;
    let nonexecuting_loop_provenance = entry_may_execute
        .as_ref()
        .and_then(|outcome| outcome.provenance.clone());
    // Same solve, same evidence: carry the entry refutation's checked
    // certificate alongside its provenance (see
    // `nonexecuting_loop_proof_authority`).
    let nonexecuting_loop_certificate =
        nonexecuting_loop_proof_authority(entry_may_execute.as_ref());
    if debug_timing {
        let now = Instant::now();
        debug!(
            "[loop-timing] loop_entry_may_execute: {:?} (result={may_execute}) (total {:?})",
            now.duration_since(last_phase),
            now.duration_since(phase_start)
        );
        last_phase = now;
    }

    // 3. Verify preservation: invariant ∧ condition => invariant'
    // When the loop cannot execute (!may_execute), preservation is
    // trivially valid — the body never runs, so there is nothing to
    // preserve. Short-circuit to Verified instead of letting the vacuity
    // guard demote to Unknown. (#1709)
    let preservation = if may_execute {
        // Per-sub-check panic isolation (#2273).
        // Demotion handled inside verify_preservation_with_config. (#2062)
        let pres_config = make_config(critical_phase_budget(num_phases.saturating_sub(1)));
        let pres_base = LoopVcBase {
            invariants,
            loop_condition: loop_condition_ref,
            condition_is_body_break: ctx.condition_is_body_break,
            modified_vars: ctx.modified_vars,
            effects: body_effects,
            config: &pres_config,
        };
        catch_ay_sort_panics_outcome(AssertUnwindSafe(|| {
            verify_preservation_with_config_outcome(&pres_base)
        }))?
    } else {
        VerificationOutcome::new(
            VerificationResult::Verified(nonexecuting_loop_certificate.clone()),
            nonexecuting_loop_provenance.clone(),
        )
    };
    if debug_timing {
        let now = Instant::now();
        debug!(
            "[loop-timing] preservation: {:?} (total {:?})",
            now.duration_since(last_phase),
            now.duration_since(phase_start)
        );
        last_phase = now;
    }

    // Loop phase timeout early termination (#2674): track whether any phase
    // hit a timeout. Preservation and variant checks share the same base
    // (invariants + condition), so a preservation timeout strongly predicts
    // variant timeouts. Skip subsequent same-base phases after a timeout
    // to avoid accumulating N × hard_timeout wall-clock seconds.
    let preservation_timed_out = is_timeout_or_incomplete(&preservation.result);

    // Also check total elapsed time against the function budget. If we've
    // already consumed >80% of the total budget on init + entry + preservation,
    // subsequent phases will get starved and likely timeout anyway.
    let budget_exhausted =
        total_budget.is_some_and(|budget| phase_start.elapsed() > budget.mul_f64(0.8));

    // 4. Verify postcondition: requires ∧ invariant ∧ ¬condition ∧ result=return_expr => ensures
    // Postcondition still runs even when !may_execute because the loop-exit
    // state (¬condition) is reached immediately and ensures must still hold.
    // Per-sub-check panic isolation (#2273).
    // Demotion handled inside verify_postcondition. (#2062)
    //
    // Postcondition has a DIFFERENT base than preservation (adds requires,
    // ensures, return_expr), so a preservation timeout does not predict
    // postcondition timeout. Skip only when the overall budget is exhausted.
    let postcondition_effects = ctx.postcondition_body_effects();
    let postcondition = if budget_exhausted {
        if debug_timing {
            debug!(
                "  loop postcondition: skipped (budget exhausted: {:?} elapsed, {:?} budget) (#2674)",
                phase_start.elapsed(),
                total_budget,
            );
        }
        VerificationOutcome::without_provenance(VerificationResult::Unknown(
            super::UnknownReason::Timeout,
        ))
    } else {
        let post_config = make_config(critical_phase_budget(num_phases.saturating_sub(2)));
        let post_base = LoopVcBase {
            invariants,
            loop_condition: loop_condition_ref,
            condition_is_body_break: ctx.condition_is_body_break,
            modified_vars: ctx.modified_vars,
            effects: postcondition_effects,
            config: &post_config,
        };
        catch_ay_sort_panics_outcome(AssertUnwindSafe(|| {
            verify_postcondition_outcome(
                &post_base,
                PostconditionInputs {
                    ensures: &normalized_ensures,
                    return_expr: normalized_return_expr.as_ref(),
                    pre_loop_assignments: ctx.pre_loop_assignments,
                    requires: &normalized_requires,
                    post_extra_facts: &normalized_post_extra_facts,
                },
            )
        }))?
    };
    if debug_timing {
        let now = Instant::now();
        debug!(
            "[loop-timing] postcondition: {:?} (total {:?})",
            now.duration_since(last_phase),
            now.duration_since(phase_start)
        );
        last_phase = now;
    }

    // 5. Verify variant conditions if provided
    let (variant_nonneg, variant_decrease) = if let Some(var) = normalized_variant.as_ref() {
        // When the loop cannot execute, variant obligations are trivially met.
        if !may_execute {
            return Ok(LoopVerificationOutcome {
                initialization,
                preservation,
                postcondition,
                variant_nonneg: Some(VerificationOutcome::new(
                    VerificationResult::Verified(nonexecuting_loop_certificate.clone()),
                    nonexecuting_loop_provenance.clone(),
                )),
                variant_decrease: Some(VerificationOutcome::new(
                    VerificationResult::Verified(nonexecuting_loop_certificate),
                    nonexecuting_loop_provenance,
                )),
                entry_may_execute,
            });
        }

        // Variant early termination (#2674): variant checks share the same
        // base as preservation (invariants + condition). When preservation
        // timed out or the overall budget is exhausted, skip variant checks
        // and record them as Unknown(Timeout). This avoids 2 additional
        // hard-timeout envelopes (each up to 2× solver_timeout + grace) on
        // problems that have already demonstrated solver exhaustion.
        if preservation_timed_out || budget_exhausted {
            if debug_timing {
                debug!(
                    "  loop variant checks: skipped ({}) (#2674)",
                    if preservation_timed_out {
                        "preservation timed out"
                    } else {
                        "budget exhausted"
                    }
                );
            }
            (
                Some(VerificationOutcome::without_provenance(
                    VerificationResult::Unknown(super::UnknownReason::Timeout),
                )),
                Some(VerificationOutcome::without_provenance(
                    VerificationResult::Unknown(super::UnknownReason::Timeout),
                )),
            )
        } else {
            // 5a. Variant non-negative: invariant ∧ condition => variant >= 0
            // Per-sub-check panic isolation (#2273).
            // Demotion handled inside verify_variant_nonneg. (#2062)
            let nonneg_config = make_config(phase_budget(num_phases.saturating_sub(4)));
            let nonneg_base = LoopVcBase {
                invariants,
                loop_condition: loop_condition_ref,
                condition_is_body_break: ctx.condition_is_body_break,
                modified_vars: ctx.modified_vars,
                effects: body_effects,
                config: &nonneg_config,
            };
            let nonneg = catch_ay_sort_panics_outcome(AssertUnwindSafe(|| {
                verify_variant_nonneg_outcome(&nonneg_base, var)
            }))?;
            if debug_timing {
                let now = Instant::now();
                debug!(
                    "[loop-timing] variant_nonneg: {:?} (total {:?})",
                    now.duration_since(last_phase),
                    now.duration_since(phase_start)
                );
                last_phase = now;
            }

            // Check if variant_nonneg also timed out — if so, skip decrease.
            let nonneg_timed_out = is_timeout_or_incomplete(&nonneg.result);

            // 5b. Variant decrease: invariant ∧ condition => variant' < variant
            // Per-sub-check panic isolation (#2273).
            // Demotion handled inside verify_variant_decrease. (#2062)
            let decrease = if nonneg_timed_out {
                if debug_timing {
                    debug!("  loop variant_decrease: skipped (variant_nonneg timed out) (#2674)");
                }
                VerificationOutcome::without_provenance(VerificationResult::Unknown(
                    super::UnknownReason::Timeout,
                ))
            } else {
                let dec_config = make_config(phase_budget(num_phases.saturating_sub(5)));
                let dec_base = LoopVcBase {
                    invariants,
                    loop_condition: loop_condition_ref,
                    condition_is_body_break: ctx.condition_is_body_break,
                    modified_vars: ctx.modified_vars,
                    effects: body_effects,
                    config: &dec_config,
                };
                catch_ay_sort_panics_outcome(AssertUnwindSafe(|| {
                    verify_variant_decrease_outcome(&dec_base, var)
                }))?
            };
            if debug_timing {
                let now = Instant::now();
                debug!(
                    "[loop-timing] variant_decrease: {:?} (total {:?})",
                    now.duration_since(last_phase),
                    now.duration_since(phase_start)
                );
            }
            (Some(nonneg), Some(decrease))
        }
    } else {
        (None, None)
    };

    Ok(LoopVerificationOutcome {
        initialization,
        preservation,
        postcondition,
        variant_nonneg,
        variant_decrease,
        entry_may_execute,
    })
}

/// Returns `true` if the verification result indicates a timeout or solver
/// incompleteness that suggests subsequent same-base phases will also fail.
///
/// Used by the loop phase early termination logic (#2674) to skip variant
/// checks when preservation has already demonstrated solver exhaustion.
/// Both `Timeout` and `Incomplete` are included because an incomplete
/// result on the invariant+condition base means the solver cannot handle
/// the quantifier structure, making variant checks (same base + additional
/// negated goal) equally unlikely to succeed.
fn is_timeout_or_incomplete(result: &VerificationResult) -> bool {
    matches!(
        result,
        VerificationResult::Unknown(super::UnknownReason::Timeout)
            | VerificationResult::Unknown(super::UnknownReason::Incomplete)
    )
}

/// Filter logic functions and mode overrides to those referenced by loop
/// expressions, using a [`LoopVerificationContext`] (#791).
///
/// Collects logic function names used in requires, ensures, invariants,
/// loop condition, body effects, variant, pre-loop assignments, and
/// return_expr (#834), then returns only matching definitions and their
/// corresponding mode overrides.
///
/// Returns `(None, None)` when `logic_fns` is `None` or when no functions
/// are referenced. When `mode_overrides` is `Some`, the returned modes
/// are filtered to the same indices as the logic functions (#757).
#[allow(clippy::type_complexity)] // Wrapping in Result adds one layer to an already-complex tuple.
fn filter_logic_fns_for_loop_ctx(
    ctx: &LoopVerificationContext<'_>,
) -> Result<(Option<Vec<LogicFnDef>>, Option<Vec<LogicMode>>), EncodingError> {
    let fns = match ctx.config.logic_fns {
        Some(fns) if !fns.is_empty() => fns,
        _ => return Ok((None, None)),
    };
    // Silently drop mode_overrides when lengths don't match (#2316, #2700).
    let effective_modes = match ctx.config.mode_overrides {
        Some(m) if m.len() != fns.len() => {
            tracing::debug!(
                modes_len = m.len(),
                fns_len = fns.len(),
                "mode_overrides length mismatch in loop verify — dropping overrides (#2316)"
            );
            None
        }
        other => other,
    };
    let body_effects = ctx.body_effects();

    let mut formula_exprs = Vec::new();
    formula_exprs.extend(ctx.requires.iter().cloned());
    formula_exprs.extend(ctx.ensures.iter().cloned());
    formula_exprs.extend(ctx.invariants.iter().cloned());
    formula_exprs.extend(ctx.init_extra_facts.iter().cloned());
    formula_exprs.extend(ctx.post_extra_facts.iter().cloned());
    if let Some(cond) = ctx.loop_condition {
        formula_exprs.push(cond.clone());
    }

    let mut value_exprs: Vec<&PureExpr> = body_effects
        .values()
        .chain(ctx.pre_loop_assignments.values().map(|b| &b.value))
        .collect();
    if let Some(var) = ctx.variant {
        value_exprs.push(var);
    }
    if let Some(ret) = ctx.return_expr {
        value_exprs.push(ret);
    }

    let selected_type_invariants = super::setup::filter_type_invariants_for_goal(
        ctx.config.type_invariants,
        &formula_exprs,
        &[],
        &value_exprs,
    );
    let logic_formula_exprs = super::setup::formula_exprs_with_type_invariant_bodies(
        &formula_exprs,
        selected_type_invariants.as_deref(),
    );

    let mut names = HashSet::new();
    for expr in &logic_formula_exprs {
        crate::expr::collect_logic_fn_names(expr, &mut names);
    }
    for expr in &value_exprs {
        crate::expr::collect_logic_fn_names(expr, &mut names);
    }
    let indices = filter_logic_fn_indices_for_goal(fns, &names);
    if indices.is_empty() {
        return Ok((None, None));
    }
    let filtered_fns: Vec<_> = indices.iter().map(|&i| fns[i].clone()).collect();
    let filtered_modes: Option<Vec<_>> =
        effective_modes.map(|m| indices.iter().map(|&i| m[i]).collect());
    Ok((Some(filtered_fns), filtered_modes))
}

/// Infer bound invariants from the loop condition (#3315, #1709, #2698).
///
/// Generates bound invariants from comparisons in the loop condition:
///
/// **Strict comparisons** (unconditional):
/// - `var < bound`  => `var <= bound`  (upper bound)
/// - `bound > var`  => `var <= bound`  (symmetric)
/// - `var > bound`  => `var >= bound`  (lower bound)
/// - `bound < var`  => `var >= bound`  (symmetric)
///
/// **Non-strict comparisons** (direction-gated, #2698):
/// - `var <= bound` + decreasing body effect => `var <= bound`
///   (preserved: `var - k <= var <= bound`)
/// - `bound <= var` + increasing body effect => `var >= bound`
///   (preserved: `var + k >= var >= bound`)
/// - `var >= bound` + increasing body effect => `var >= bound`
///   (preserved: `var + k >= var >= bound`)
/// - `bound >= var` + decreasing body effect => `var <= bound`
///   (preserved: `var - k <= var <= bound`)
///
/// Non-strict comparisons are NOT generated unconditionally because
/// the invariant is not preserved with opposing body effects (e.g.,
/// `i <= n` is not preserved under `i += 1` when `i == n`). Only
/// when the body effect direction is compatible (decreasing preserves
/// upper bounds, increasing preserves lower bounds) is the invariant
/// sound.
///
/// **Ne comparisons** (direction-gated):
/// - `var != bound` + increasing => `var <= bound`
/// - `var != bound` + decreasing => `var >= bound`
fn infer_condition_bound_invariants(
    condition: &PureExpr,
    modified_set: &HashSet<&str>,
    user_invariants: &[PureExpr],
    auto_frame_invariants: &[PureExpr],
    auto_stable_requires: &[PureExpr],
    body_effects: context::BodyEffects<'_>,
) -> Vec<PureExpr> {
    let mut result = Vec::new();

    // Extract comparisons from the condition (handle AND-chains too).
    let mut comparisons = Vec::new();
    collect_comparisons(condition, &mut comparisons);

    for (lhs, op, rhs) in &comparisons {
        match op {
            BinOp::Lt => {
                // var < bound  =>  auto-invariant: var <= bound  (upper bound)
                if is_modified_var(lhs, modified_set) && !references_modified(rhs, modified_set) {
                    let inv =
                        PureExpr::BinOp(Arc::new(lhs.clone()), BinOp::Le, Arc::new(rhs.clone()));
                    if !contains_invariant(
                        &inv,
                        user_invariants,
                        auto_frame_invariants,
                        auto_stable_requires,
                    ) && !result.contains(&inv)
                    {
                        result.push(inv);
                    }
                }
                // bound < var  =>  auto-invariant: var >= bound  (lower bound)
                //
                // Symmetric to `var > bound`. When the loop condition is
                // `0 < i` (equivalently `i > 0`), and `i` is modified with
                // a decrementing effect, `i >= 0` is a sound invariant. (#1709)
                if is_modified_var(rhs, modified_set) && !references_modified(lhs, modified_set) {
                    let inv =
                        PureExpr::BinOp(Arc::new(rhs.clone()), BinOp::Ge, Arc::new(lhs.clone()));
                    if !contains_invariant(
                        &inv,
                        user_invariants,
                        auto_frame_invariants,
                        auto_stable_requires,
                    ) && !result.contains(&inv)
                    {
                        result.push(inv);
                    }
                }
            }
            // var <= bound / bound <= var: Auto-invariant only with compatible
            // monotone body effect direction (#2698).
            //
            // In the general case, `var <= bound` is NOT preserved by an
            // incrementing body effect: `i = n`, condition `i <= n` is true,
            // body does `i += 1`, now `i = n + 1 > n`. So the user must
            // provide a correct bound.
            //
            // HOWEVER, when the body effect DECREASES the variable, `var <= bound`
            // IS preserved: `var - k <= var <= bound`. Similarly, `bound <= var`
            // with an INCREASING effect gives `var >= bound` preserved.
            BinOp::Le => {
                // var <= bound with DECREASING body effect => auto `var <= bound`
                // Preserved because var - k <= var <= bound.
                if is_modified_var(lhs, modified_set) && !references_modified(rhs, modified_set) {
                    let var_name = extract_modified_var_name(lhs);
                    if let Some(MonotoneDirection::Decreasing) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = PureExpr::BinOp(
                            Arc::new(lhs.clone()),
                            BinOp::Le,
                            Arc::new(rhs.clone()),
                        );
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
                // bound <= var with INCREASING body effect => auto `var >= bound`
                // Preserved because var + k >= var >= bound.
                if is_modified_var(rhs, modified_set) && !references_modified(lhs, modified_set) {
                    let var_name = extract_modified_var_name(rhs);
                    if let Some(MonotoneDirection::Increasing) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = PureExpr::BinOp(
                            Arc::new(rhs.clone()),
                            BinOp::Ge,
                            Arc::new(lhs.clone()),
                        );
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
            }
            BinOp::Gt => {
                // bound > var  =>  auto-invariant: var <= bound  (upper bound)
                if is_modified_var(rhs, modified_set) && !references_modified(lhs, modified_set) {
                    let inv =
                        PureExpr::BinOp(Arc::new(rhs.clone()), BinOp::Le, Arc::new(lhs.clone()));
                    if !contains_invariant(
                        &inv,
                        user_invariants,
                        auto_frame_invariants,
                        auto_stable_requires,
                    ) && !result.contains(&inv)
                    {
                        result.push(inv);
                    }
                }
                // var > bound  =>  auto-invariant: var >= bound  (lower bound)
                //
                // For decreasing counter loops like `while i > 0 { i -= 1 }`,
                // the condition `i > 0` means lhs=i (modified), rhs=0 (unmodified).
                // Generates `i >= 0`, which is sound:
                //   - Init: `i > 0` implies `i >= 0` (always true).
                //   - Preservation: `i >= 0 && i > 0` gives `i >= 1`, after
                //     `i -= 1` gives `i >= 0` (preserved for unit decrement).
                //   - Post: at exit, NOT(i > 0) gives `i <= 0`, combined with
                //     `i >= 0` yields `i == 0`.
                //
                // Note: soundness requires that the loop body decrements by at
                // most the gap between `var` and `bound`. For unit decrements
                // (`i -= 1`), `var > bound` ensures `var >= bound + 1`, so
                // `var - 1 >= bound`. For larger decrements, the user must
                // supply a stronger invariant. (#1709)
                if is_modified_var(lhs, modified_set) && !references_modified(rhs, modified_set) {
                    let inv =
                        PureExpr::BinOp(Arc::new(lhs.clone()), BinOp::Ge, Arc::new(rhs.clone()));
                    if !contains_invariant(
                        &inv,
                        user_invariants,
                        auto_frame_invariants,
                        auto_stable_requires,
                    ) && !result.contains(&inv)
                    {
                        result.push(inv);
                    }
                }
            }
            // bound >= var / var >= bound: Auto-invariant only with compatible
            // monotone body effect direction (#2698).
            //
            // Same reasoning as Le above but symmetric:
            // `var >= bound` with INCREASING effect is preserved (var + k >= var >= bound).
            // `bound >= var` with DECREASING effect gives `var <= bound` preserved.
            BinOp::Ge => {
                // var >= bound with INCREASING body effect => auto `var >= bound`
                // Preserved because var + k >= var >= bound.
                if is_modified_var(lhs, modified_set) && !references_modified(rhs, modified_set) {
                    let var_name = extract_modified_var_name(lhs);
                    if let Some(MonotoneDirection::Increasing) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = PureExpr::BinOp(
                            Arc::new(lhs.clone()),
                            BinOp::Ge,
                            Arc::new(rhs.clone()),
                        );
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
                // bound >= var with DECREASING body effect => auto `var <= bound`
                // Preserved because var - k <= var <= bound.
                if is_modified_var(rhs, modified_set) && !references_modified(lhs, modified_set) {
                    let var_name = extract_modified_var_name(rhs);
                    if let Some(MonotoneDirection::Decreasing) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = PureExpr::BinOp(
                            Arc::new(rhs.clone()),
                            BinOp::Le,
                            Arc::new(lhs.clone()),
                        );
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
            }
            BinOp::Ne => {
                // var != bound with monotone body effect (#1816).
                //
                // When the loop condition is `var != bound` and the body has a
                // detectable monotone direction for `var`, we generate the
                // appropriate bound:
                //
                // - Increasing (`var += k`): `var <= bound` (upper bound).
                //   Preserved because `var != bound && var <= bound` implies
                //   `var < bound`, so `var + k <= bound` when k == 1.
                //   At exit: NOT(var != bound) => var == bound.
                //
                // - Decreasing (`var -= k`): `var >= bound` (lower bound).
                //   Symmetric reasoning.
                //
                // Without a known direction, no bound is generated — generating
                // both would cause initialization to fail (one direction is
                // always wrong at init).
                if is_modified_var(lhs, modified_set) && !references_modified(rhs, modified_set) {
                    let var_name = extract_modified_var_name(lhs);
                    if let Some(dir) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = match dir {
                            MonotoneDirection::Increasing => PureExpr::BinOp(
                                Arc::new(lhs.clone()),
                                BinOp::Le,
                                Arc::new(rhs.clone()),
                            ),
                            MonotoneDirection::Decreasing => PureExpr::BinOp(
                                Arc::new(lhs.clone()),
                                BinOp::Ge,
                                Arc::new(rhs.clone()),
                            ),
                        };
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
                // Symmetric: bound != var
                if is_modified_var(rhs, modified_set) && !references_modified(lhs, modified_set) {
                    let var_name = extract_modified_var_name(rhs);
                    if let Some(dir) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = match dir {
                            MonotoneDirection::Increasing => PureExpr::BinOp(
                                Arc::new(rhs.clone()),
                                BinOp::Le,
                                Arc::new(lhs.clone()),
                            ),
                            MonotoneDirection::Decreasing => PureExpr::BinOp(
                                Arc::new(rhs.clone()),
                                BinOp::Ge,
                                Arc::new(lhs.clone()),
                            ),
                        };
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
            }
            // var == bound: Both `var <= bound` and `var >= bound` hold at
            // initialization. However, preservation depends on direction:
            //
            // - With INCREASING body effect: `var >= bound` is preserved
            //   (var + k >= var >= bound) but `var <= bound` is NOT (var + k > bound).
            // - With DECREASING body effect: `var <= bound` is preserved
            //   (var - k <= var <= bound) but `var >= bound` is NOT.
            // - Without a known direction: both bounds hold at init, but
            //   generating both would fail preservation. Generate nothing.
            //
            // This handles patterns like `while i == n { ... }` where the
            // loop condition requires equality, and the body modifies `i`.
            // At exit, NOT(i == n) gives `i != n`, combined with the
            // direction-aware bound gives a useful constraint. (#2698)
            BinOp::Eq => {
                if is_modified_var(lhs, modified_set) && !references_modified(rhs, modified_set) {
                    let var_name = extract_modified_var_name(lhs);
                    if let Some(dir) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = match dir {
                            MonotoneDirection::Increasing => PureExpr::BinOp(
                                Arc::new(lhs.clone()),
                                BinOp::Ge,
                                Arc::new(rhs.clone()),
                            ),
                            MonotoneDirection::Decreasing => PureExpr::BinOp(
                                Arc::new(lhs.clone()),
                                BinOp::Le,
                                Arc::new(rhs.clone()),
                            ),
                        };
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
                // Symmetric: bound == var
                if is_modified_var(rhs, modified_set) && !references_modified(lhs, modified_set) {
                    let var_name = extract_modified_var_name(rhs);
                    if let Some(dir) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = match dir {
                            MonotoneDirection::Increasing => PureExpr::BinOp(
                                Arc::new(rhs.clone()),
                                BinOp::Ge,
                                Arc::new(lhs.clone()),
                            ),
                            MonotoneDirection::Decreasing => PureExpr::BinOp(
                                Arc::new(rhs.clone()),
                                BinOp::Le,
                                Arc::new(lhs.clone()),
                            ),
                        };
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    result
}

/// Direction of a monotone body effect.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MonotoneDirection {
    /// Variable increases each iteration (e.g., `var + 1`).
    Increasing,
    /// Variable decreases each iteration (e.g., `var - 1`).
    Decreasing,
}

/// Depth of dereference nesting in a body effect pattern.
///
/// Used by [`detect_direction_from_expr`] to match the correct variable
/// pattern at each indirection level:
/// - `None`: matches `Var(name) + k` (direct assignment `x = x + 1`)
/// - `Single`: matches `Deref(Var(name)) + k` (deref assignment `*x = *x + 1`)
/// - `Double`: matches `Deref(Deref(Var(name))) + k` (double-deref `**x = **x + 1`)
///
/// (#1816)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DerefDepth {
    /// No dereference — matches `Var(name)`.
    None,
    /// Single dereference — matches `Deref(Var(name))`.
    Single,
    /// Double dereference — matches `Deref(Deref(Var(name)))`.
    Double,
}

/// Detect the monotone direction of a variable from its body effect.
///
/// Returns `Some(Increasing)` when the effect is `var + k` (k > 0),
/// `Some(Decreasing)` when `var - k` (k > 0), and `None` otherwise.
///
/// Checks direct effects (`x = x + 1`), deref effects (`*x = *x + 1`),
/// and double-deref effects (`**x = **x + 1`) to support mutable reference
/// loop patterns at all indirection levels. For deref effects, the
/// expression pattern is `Deref(Var(name)) + k` instead of `Var(name) + k`.
/// For double-deref effects, the pattern is `Deref(Deref(Var(name))) + k`.
/// (#1816)
fn detect_body_effect_direction(
    var_name: &str,
    effects: &context::BodyEffects<'_>,
) -> Option<MonotoneDirection> {
    // Try direct effects first.
    if let Some(effect_expr) = effects.direct.get(var_name) {
        if let Some(dir) = detect_direction_from_expr(var_name, effect_expr, DerefDepth::None) {
            return Some(dir);
        }
    }
    // Fall back to deref effects for mutable reference patterns.
    if let Some(effect_expr) = effects.deref.get(var_name) {
        if let Some(dir) = detect_direction_from_expr(var_name, effect_expr, DerefDepth::Single) {
            return Some(dir);
        }
    }
    // Fall back to double-deref effects for `&mut &mut T` patterns.
    if let Some(effect_expr) = effects.double_deref.get(var_name) {
        if let Some(dir) = detect_direction_from_expr(var_name, effect_expr, DerefDepth::Double) {
            return Some(dir);
        }
    }
    None
}

/// Detect the monotone direction of a variable from a body effect expression.
///
/// Matches the variable pattern at the specified [`DerefDepth`]:
/// - `None`: `Var(name) + k` (direct body effects)
/// - `Single`: `Deref(Var(name)) + k` (single-deref body effects)
/// - `Double`: `Deref(Deref(Var(name))) + k` (double-deref body effects)
///
/// Returns `Some(Increasing)` for `+ k` (k > 0) and `Some(Decreasing)`
/// for `- k` (k > 0). Returns `None` for all other patterns. (#1816)
fn detect_direction_from_expr(
    var_name: &str,
    effect_expr: &PureExpr,
    depth: DerefDepth,
) -> Option<MonotoneDirection> {
    let matches_var = |expr: &PureExpr| -> bool {
        match depth {
            DerefDepth::None => {
                matches!(expr, PureExpr::Var(name, _) if name == var_name)
            }
            DerefDepth::Single => {
                matches!(
                    expr,
                    PureExpr::Deref(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == var_name)
                )
            }
            DerefDepth::Double => {
                if let PureExpr::Deref(outer) = expr {
                    if let PureExpr::Deref(inner) = outer.as_ref() {
                        matches!(inner.as_ref(), PureExpr::Var(name, _) if name == var_name)
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
        }
    };

    match effect_expr {
        PureExpr::BinOp(lhs, BinOp::Add, rhs) => {
            let increasing = (matches_var(lhs)
                && matches!(rhs.as_ref(), PureExpr::Int(k) if *k > 0))
                || (matches_var(rhs) && matches!(lhs.as_ref(), PureExpr::Int(k) if *k > 0));
            if increasing {
                Some(MonotoneDirection::Increasing)
            } else {
                None
            }
        }
        PureExpr::BinOp(lhs, BinOp::Sub, rhs) => {
            if matches_var(lhs) && matches!(rhs.as_ref(), PureExpr::Int(k) if *k > 0) {
                Some(MonotoneDirection::Decreasing)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Infer bound invariants from monotone body effects (#3315, #1816).
///
/// **Increasing** (`var + k`, k > 0): generates `var >= init_value` (lower bound).
/// **Decreasing** (`var - k`, k > 0): generates `var <= init_value` (upper bound).
///
/// Both are sound because:
///   - Init: `var = init_value` satisfies `var >= init_value` / `var <= init_value`.
///   - Preservation (increasing): `var >= init_value` and `var' = var + k` (k > 0)
///     implies `var' >= init_value + k >= init_value`.
///   - Preservation (decreasing): `var <= init_value` and `var' = var - k` (k > 0)
///     implies `var' <= init_value - k <= init_value`.
///   - Postcondition: provides floor/ceiling for reasoning about the variable's
///     range at loop exit.
fn infer_monotonicity_lower_bound_invariants(
    effects: context::BodyEffects<'_>,
    pre_loop_assignments: &HashMap<String, trust_wp_core::formula::NamedBindingValue>,
    modified_set: &HashSet<&str>,
    user_invariants: &[PureExpr],
    auto_frame_invariants: &[PureExpr],
    auto_condition_bound_invariants: &[PureExpr],
) -> Vec<PureExpr> {
    let mut result = Vec::new();

    for (var_name, effect_expr) in effects.direct {
        if !modified_set.contains(var_name.as_str()) {
            continue;
        }

        // Determine monotonicity direction from the body effect.
        let direction = match effect_expr {
            PureExpr::BinOp(lhs, BinOp::Add, rhs) => {
                // var + k where k > 0
                let increasing = (matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == var_name)
                    && matches!(rhs.as_ref(), PureExpr::Int(k) if *k > 0))
                    || (matches!(rhs.as_ref(), PureExpr::Var(name, _) if name == var_name)
                        && matches!(lhs.as_ref(), PureExpr::Int(k) if *k > 0));
                if increasing {
                    Some(MonotoneDirection::Increasing)
                } else {
                    None
                }
            }
            PureExpr::BinOp(lhs, BinOp::Sub, rhs) => {
                // var - k where k > 0
                if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == var_name)
                    && matches!(rhs.as_ref(), PureExpr::Int(k) if *k > 0)
                {
                    Some(MonotoneDirection::Decreasing)
                } else {
                    None
                }
            }
            _ => None,
        };

        let Some(dir) = direction else {
            continue;
        };

        // Look up the pre-loop assignment to get the initial value.
        let Some(binding) = pre_loop_assignments.get(var_name) else {
            continue;
        };

        // Only generate bound when the initial value is stable across iterations
        // — we need stability for soundness. Handles:
        // - Concrete integer literals (e.g., `i = 0`)
        // - Unmodified variables (e.g., `i = a` where `a` is not in modified_set)
        // - BinOp expressions over stable operands (e.g., `i = a + 1` where `a`
        //   is not modified). This enables bounds like `i >= a + 1` for patterns
        //   where the initial value is a computed expression. (#1816)
        let init_value = match &binding.value {
            PureExpr::Int(_) => binding.value.clone(),
            PureExpr::Var(_, _) | PureExpr::BinOp(_, _, _) => {
                if !expr_helpers::expr_references_any_var(&binding.value, modified_set) {
                    binding.value.clone()
                } else {
                    continue;
                }
            }
            _ => continue,
        };

        let (op, label) = match dir {
            MonotoneDirection::Increasing => (BinOp::Ge, "lower"),
            MonotoneDirection::Decreasing => (BinOp::Le, "upper"),
        };

        let inv = PureExpr::BinOp(
            Arc::new(PureExpr::Var(var_name.clone(), binding.sort.clone())),
            op,
            Arc::new(init_value),
        );

        let _ = label; // suppress unused warning in non-debug builds

        if !contains_invariant(
            &inv,
            user_invariants,
            auto_frame_invariants,
            auto_condition_bound_invariants,
        ) && !result.contains(&inv)
        {
            result.push(inv);
        }
    }

    for (var_name, effect_expr) in effects.deref {
        if !modified_set.contains(var_name.as_str()) {
            continue;
        }

        let Some(dir) = detect_direction_from_expr(var_name, effect_expr, DerefDepth::Single)
        else {
            continue;
        };

        // Look up the pre-loop assignment to get the initial dereferenced value.
        let Some(binding) = pre_loop_assignments.get(var_name) else {
            continue;
        };

        // Only generate bound when the initial dereferenced value is stable
        // across iterations — we need stability for soundness.
        let init_value = match &binding.value {
            PureExpr::Int(_) => binding.value.clone(),
            PureExpr::Var(_, _) | PureExpr::BinOp(_, _, _) => {
                if !expr_helpers::expr_references_any_var(&binding.value, modified_set) {
                    binding.value.clone()
                } else {
                    continue;
                }
            }
            _ => continue,
        };
        let init_deref_value = PureExpr::Deref(Arc::new(init_value));

        let (op, label) = match dir {
            MonotoneDirection::Increasing => (BinOp::Ge, "lower"),
            MonotoneDirection::Decreasing => (BinOp::Le, "upper"),
        };

        let inv = PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                var_name.clone(),
                binding.sort.clone(),
            )))),
            op,
            Arc::new(init_deref_value),
        );

        let _ = label; // suppress unused warning in non-debug builds

        if !contains_invariant(
            &inv,
            user_invariants,
            auto_frame_invariants,
            auto_condition_bound_invariants,
        ) && !result.contains(&inv)
        {
            result.push(inv);
        }
    }

    // Double-deref effects for `&mut &mut T` patterns (#1816).
    //
    // When the loop body writes through `**x`, generate monotonicity bounds
    // on `Deref(Deref(Var(x)))` analogous to the single-deref case above.
    // The initial double-deref value is `Deref(Deref(init_value))`.
    for (var_name, effect_expr) in effects.double_deref {
        if !modified_set.contains(var_name.as_str()) {
            continue;
        }

        let Some(dir) = detect_direction_from_expr(var_name, effect_expr, DerefDepth::Double)
        else {
            continue;
        };

        let Some(binding) = pre_loop_assignments.get(var_name) else {
            continue;
        };

        // Only generate bound when the initial value is stable across iterations.
        let init_value = match &binding.value {
            PureExpr::Int(_) => binding.value.clone(),
            PureExpr::Var(_, _) | PureExpr::BinOp(_, _, _) => {
                if !expr_helpers::expr_references_any_var(&binding.value, modified_set) {
                    binding.value.clone()
                } else {
                    continue;
                }
            }
            _ => continue,
        };
        let init_double_deref_value =
            PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(init_value))));

        let (op, _label) = match dir {
            MonotoneDirection::Increasing => (BinOp::Ge, "lower"),
            MonotoneDirection::Decreasing => (BinOp::Le, "upper"),
        };

        let inv = PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(
                PureExpr::Var(var_name.clone(), binding.sort.clone()),
            ))))),
            op,
            Arc::new(init_double_deref_value),
        );

        if !contains_invariant(
            &inv,
            user_invariants,
            auto_frame_invariants,
            auto_condition_bound_invariants,
        ) && !result.contains(&inv)
        {
            result.push(inv);
        }
    }

    result
}

/// Infer counter correlation invariants from pairs of modified variables
/// that change in lockstep or in opposition (#2698).
///
/// **Same-step pairs** (`step_a == step_b`): the difference `a - b` is constant
/// across iterations. Generates `a == b + (a_init - b_init)`.
///
/// **Opposing-step pairs** (`step_a + step_b == 0`): the sum `a + b` is constant
/// across iterations. Generates `a + b == a_init + b_init`. This handles patterns
/// like `x -= 1; result += 1` where the user invariant references `x + result`.
///
/// **Soundness (same-step):**
///   - Initialization: `a = a_init`, `b = b_init`, so `a - b = a_init - b_init`.
///   - Preservation: `a' = a + k`, `b' = b + k`, so `a' - b' = a - b` (preserved).
///   - Postcondition: the correlation provides facts connecting the two
///     variables, enabling reasoning like "when `i == n`, then `j == n + offset`".
///
/// **Soundness (opposing-step):**
///   - Initialization: `a = a_init`, `b = b_init`, so `a + b = a_init + b_init`.
///   - Preservation: `a' = a + k`, `b' = b - k`, so `a' + b' = a + b` (preserved).
///   - Postcondition: provides the sum-constant relationship at loop exit.
///
/// Only generates invariants for direct effects (not deref effects) and
/// when both initial values are stable (not referencing other modified vars).
fn infer_counter_correlation_invariants(
    effects: context::BodyEffects<'_>,
    pre_loop_assignments: &HashMap<String, trust_wp_core::formula::NamedBindingValue>,
    modified_set: &HashSet<&str>,
    user_invariants: &[PureExpr],
    auto_frame_invariants: &[PureExpr],
) -> Vec<PureExpr> {
    let mut result = Vec::new();

    // Collect (var_name, direction, step_value, init_value) for each modified
    // variable with a detectable monotone effect and a concrete or stable init.
    struct CounterInfo {
        var_name: String,
        sort: Option<ExprSort>,
        step: i64,
        init: PureExpr,
    }
    let mut counters: Vec<CounterInfo> = Vec::new();

    for (var_name, effect_expr) in effects.direct {
        if !modified_set.contains(var_name.as_str()) {
            continue;
        }
        // Extract step: var + k => step = k, var - k => step = -k
        let step = match effect_expr {
            PureExpr::BinOp(lhs, BinOp::Add, rhs) => {
                if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == var_name) {
                    if let PureExpr::Int(k) = rhs.as_ref() {
                        Some(*k)
                    } else {
                        None
                    }
                } else if matches!(rhs.as_ref(), PureExpr::Var(name, _) if name == var_name) {
                    if let PureExpr::Int(k) = lhs.as_ref() {
                        Some(*k)
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            PureExpr::BinOp(lhs, BinOp::Sub, rhs) => {
                if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == var_name) {
                    if let PureExpr::Int(k) = rhs.as_ref() {
                        Some(-k)
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        };
        let Some(step) = step else { continue };
        if step == 0 {
            continue;
        }

        let Some(binding) = pre_loop_assignments.get(var_name) else {
            continue;
        };
        // Only use stable init values.
        let init = match &binding.value {
            PureExpr::Int(_) => binding.value.clone(),
            PureExpr::Var(_, _) | PureExpr::BinOp(_, _, _) => {
                if !expr_helpers::expr_references_any_var(&binding.value, modified_set) {
                    binding.value.clone()
                } else {
                    continue;
                }
            }
            _ => continue,
        };

        counters.push(CounterInfo {
            var_name: var_name.clone(),
            sort: binding.sort.clone(),
            step,
            init,
        });
    }

    // For each pair with matching step, generate a difference-constant invariant.
    // For each pair with opposing steps (sum == 0), generate a sum-constant invariant.
    for i in 0..counters.len() {
        for j in (i + 1)..counters.len() {
            let a = &counters[i];
            let b = &counters[j];

            if a.step == b.step {
                // Same step: a - b is constant across iterations.
                // a' - b' = (a + k) - (b + k) = a - b.
                // Generate: a == b + (a_init - b_init).
                let offset = match (&a.init, &b.init) {
                    (PureExpr::Int(a_val), PureExpr::Int(b_val)) => PureExpr::Int(a_val - b_val),
                    _ => PureExpr::BinOp(
                        Arc::new(a.init.clone()),
                        BinOp::Sub,
                        Arc::new(b.init.clone()),
                    ),
                };

                let inv = PureExpr::BinOp(
                    Arc::new(PureExpr::Var(a.var_name.clone(), a.sort.clone())),
                    BinOp::Eq,
                    Arc::new(PureExpr::BinOp(
                        Arc::new(PureExpr::Var(b.var_name.clone(), b.sort.clone())),
                        BinOp::Add,
                        Arc::new(offset),
                    )),
                );

                if !contains_invariant(&inv, user_invariants, auto_frame_invariants, &[])
                    && !result.contains(&inv)
                {
                    result.push(inv);
                }
            } else if a.step + b.step == 0 {
                // Opposing steps: a + b is constant across iterations.
                // a' + b' = (a + k) + (b - k) = a + b.
                // Generate: a + b == a_init + b_init.
                //
                // This handles patterns like `x -= 1; result += 1` where
                // the user invariant is `total == x + result`. The auto-
                // generated `x + result == x_init + result_init` provides
                // the missing algebraic fact. (#2698)
                //
                // Soundness:
                //   - Init: a = a_init, b = b_init, so a + b = a_init + b_init.
                //   - Preservation: a' = a + step_a, b' = b + step_b, step_a + step_b = 0,
                //     so a' + b' = a + step_a + b + step_b = a + b + 0 = a + b.
                //   - Postcondition: provides the sum-constant relationship at loop exit.
                let sum_init = match (&a.init, &b.init) {
                    (PureExpr::Int(a_val), PureExpr::Int(b_val)) => PureExpr::Int(a_val + b_val),
                    _ => PureExpr::BinOp(
                        Arc::new(a.init.clone()),
                        BinOp::Add,
                        Arc::new(b.init.clone()),
                    ),
                };

                let inv = PureExpr::BinOp(
                    Arc::new(PureExpr::BinOp(
                        Arc::new(PureExpr::Var(a.var_name.clone(), a.sort.clone())),
                        BinOp::Add,
                        Arc::new(PureExpr::Var(b.var_name.clone(), b.sort.clone())),
                    )),
                    BinOp::Eq,
                    Arc::new(sum_init),
                );

                if !contains_invariant(&inv, user_invariants, auto_frame_invariants, &[])
                    && !result.contains(&inv)
                {
                    result.push(inv);
                }
            }
        }
    }

    result
}

/// Collect binary comparison sub-expressions from a condition.
///
/// Handles AND-chains: `a < b && c < d` yields both comparisons.
///
/// NOTE: OR-chains (`a < b || c < d`) are NOT decomposed because the
/// resulting bounds are not individually guaranteed at loop entry. When the
/// condition is `a < b || c < d`, only the disjunction holds — individual
/// disjuncts may be false. Generating `a <= b` as an auto-invariant would
/// fail initialization when only the second disjunct holds (e.g., `a = 5,
/// b = 3, c = 0, d = 1`). (#1816)
///
/// Also collects `Ne` and `Eq` comparisons for monotone-direction-aware
/// invariant inference (#1816, #2698).
/// Returns owned clones to avoid lifetime complications with `Arc` innards.
fn collect_comparisons(expr: &PureExpr, out: &mut Vec<(PureExpr, BinOp, PureExpr)>) {
    match expr {
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            collect_comparisons(lhs, out);
            collect_comparisons(rhs, out);
        }
        PureExpr::BinOp(lhs, op, rhs)
            if matches!(
                op,
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Ne | BinOp::Eq
            ) =>
        {
            out.push((lhs.as_ref().clone(), *op, rhs.as_ref().clone()));
        }
        _ => {}
    }
}

/// Returns true if the expression is a `Var` (or `Deref(Var)`) that is in the
/// modified set.
///
/// Matches both direct variables (`x`) and single-deref patterns (`*x`)
/// because mutable reference loop conditions use `*x < n` where `x` is the
/// modified variable. Without matching `Deref(Var)`, condition-bound
/// auto-invariants are not generated for `&mut` loop patterns. (#1816)
fn is_modified_var(expr: &PureExpr, modified_set: &HashSet<&str>) -> bool {
    match expr {
        PureExpr::Var(name, _) => modified_set.contains(name.as_str()),
        PureExpr::Deref(inner) => {
            matches!(inner.as_ref(), PureExpr::Var(name, _) if modified_set.contains(name.as_str()))
        }
        _ => false,
    }
}

/// Extract the variable name from a `Var` or `Deref(Var)` expression.
///
/// Used by condition-bound inference to look up body effect direction for
/// both direct variables and deref patterns. Returns `None` for expressions
/// that don't match either pattern.
fn extract_modified_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => Some(name.as_str()),
            _ => None,
        },
        _ => None,
    }
}

/// Returns true if the expression references any variable in the modified set.
fn references_modified(expr: &PureExpr, modified_set: &HashSet<&str>) -> bool {
    expr_helpers::expr_references_any_var(expr, modified_set)
}

/// Check if an invariant is already present in any of the existing invariant lists.
fn contains_invariant(
    inv: &PureExpr,
    user_invariants: &[PureExpr],
    auto_frame: &[PureExpr],
    other: &[PureExpr],
) -> bool {
    user_invariants.contains(inv) || auto_frame.contains(inv) || other.contains(inv)
}

/// Peel through Deref, View, Old, and Final wrappers to extract the root
/// variable name from a receiver expression (#1816).
///
/// Handles chains like `Deref(Deref(Var("x")))` and `View(Deref(Var("x")))`.
/// Returns `None` if the root is not a `Var`.
fn peel_to_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner)
        | PureExpr::View(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner) => peel_to_var_name(inner),
        _ => None,
    }
}

/// Flatten AND-chains into individual conjuncts (#1816).
///
/// Decomposes `a && b && c` into `[a, b, c]`. Non-AND expressions are pushed
/// as-is. This enables per-conjunct stability analysis in auto-stable-requires:
/// from `x > 0 && y > 0` where only `x` is modified, `y > 0` can still be
/// promoted as a loop invariant.
fn flatten_and_conjuncts<'a>(expr: &'a PureExpr, out: &mut Vec<&'a PureExpr>) {
    match expr {
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            flatten_and_conjuncts(lhs, out);
            flatten_and_conjuncts(rhs, out);
        }
        _ => out.push(expr),
    }
}

/// Infer constant-deref invariants from stable body effects (#2698).
///
/// Infer bound invariants from the NEGATED exit condition of body-break
/// loops (#2698).
///
/// For body-break loops (`loop { body; if exit_cond { break } }`), the exit
/// condition holds AFTER the body when the loop terminates. When the loop
/// CONTINUES, NOT(exit_cond) holds after the body. This negation provides
/// bound information for the next iteration's start.
///
/// **Key insight:** for body-break, the continuation path is:
///   inv(top) → body → NOT(exit_cond) → inv(next top)
/// So NOT(exit_cond) after body provides the bound that connects iterations.
///
/// **Examples:**
/// - Exit `i >= n`, body `i += 1`: NOT(i' >= n) => i' < n.
///   Auto-invariant: `i < n` (STRICT). Since post-body value becomes next
///   loop-top, the strict bound is the exact continuation condition.
///   At exit: exit_cond `i' >= n` AND `i < n` AND `i' = i + 1`
///   gives `i + 1 >= n AND i < n` => `i = n - 1` => `i' = n` (exact!).
///
/// - Exit `i <= 0`, body `i -= 1`: NOT(i' <= 0) => i' > 0.
///   Auto-invariant: `i > 0` (STRICT). At exit: `i' <= 0 AND i > 0 AND
///   i' = i - 1` => `i - 1 <= 0 AND i > 0` => `i = 1` => `i' = 0` (exact!).
///
/// **Why strict bounds (not relaxed)?**
/// The continuation condition NOT(exit_cond) on the post-body value `var'`
/// becomes the loop-top invariant directly, because `var'` IS the next
/// loop-top value. No relaxation needed. Relaxation (e.g., `i <= n` instead
/// of `i < n`) allows the loop-top value to equal the bound, which creates
/// a counterexample: if `i = n`, then `i' = n + 1`, and `NOT(i' < n)` (exit),
/// but `i' != n` (postcondition violated).
///
/// **Input convention:** The `condition` parameter is the CONTINUATION
/// condition (same as for header-while loops). The driver's
/// `find_body_break_condition` negates the break predicate to produce
/// continuation form (e.g., `loop { ...; if i >= n { break } }` yields
/// continuation `i < n`).
///
/// **Why body-break gets its own function (not just `infer_condition_bound_invariants`):**
/// For header-while, the continuation `i < n` is relaxed to `i <= n` because
/// the body may temporarily exceed the strict bound within an iteration.
/// For body-break, the continuation is checked AFTER the body, so the
/// post-body value satisfying continuation IS the next loop-top value.
/// No relaxation needed — the continuation condition is used DIRECTLY.
///
/// **Soundness:**
/// - Initialization: the strict bound must hold at the initial state.
///   For `i < n` with `i = 0`, needs `0 < n` (i.e., `n > 0` from
///   preconditions). If init fails, the invariant is dropped.
/// - Preservation: body-break continuation on post-body IS the next
///   loop-top state. The invariant `i < n` at top and `i' < n` at
///   continuation are the same variable at different times.
/// - Postcondition: NOT(continuation) at exit, combined with invariant,
///   pins the exit value (e.g., `i < n AND NOT(i' < n) AND i'=i+1`
///   gives `i' = n`).
///
/// Only generates bounds when:
/// - The bound variable is NOT modified by the loop body (constant bound).
/// - The modified variable has a detectable monotone body effect compatible
///   with the derived bound direction.
fn infer_body_break_condition_bound_invariants(
    condition: &PureExpr,
    modified_set: &HashSet<&str>,
    user_invariants: &[PureExpr],
    auto_frame_invariants: &[PureExpr],
    auto_stable_requires: &[PureExpr],
    body_effects: context::BodyEffects<'_>,
) -> Vec<PureExpr> {
    let mut result = Vec::new();

    // Extract comparisons from the CONTINUATION condition.
    let mut comparisons = Vec::new();
    collect_comparisons(condition, &mut comparisons);

    for (lhs, op, rhs) in &comparisons {
        // For body-break, the continuation condition is checked AFTER the body.
        // The post-body value satisfying continuation becomes the next loop-top
        // value. So the continuation condition IS the invariant directly —
        // no operator inversion or relaxation needed.
        //
        // Continuation condition      Direction check    Auto-invariant
        // ------------------------------------------------------------------
        // var < bound  (increasing i)  Increasing         var < bound
        // var <= bound (increasing i)  Increasing         var <= bound
        // var > bound  (decreasing i)  Decreasing         var > bound
        // var >= bound (decreasing i)  Decreasing         var >= bound
        match op {
            BinOp::Lt => {
                // Continuation: var < bound. Increasing var: auto-invariant var < bound.
                if is_modified_var(lhs, modified_set) && !references_modified(rhs, modified_set) {
                    let var_name = extract_modified_var_name(lhs);
                    if let Some(MonotoneDirection::Increasing) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = PureExpr::BinOp(
                            Arc::new(lhs.clone()),
                            BinOp::Lt,
                            Arc::new(rhs.clone()),
                        );
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
                // Symmetric: bound < var => var > bound (decreasing var)
                if is_modified_var(rhs, modified_set) && !references_modified(lhs, modified_set) {
                    let var_name = extract_modified_var_name(rhs);
                    if let Some(MonotoneDirection::Decreasing) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = PureExpr::BinOp(
                            Arc::new(rhs.clone()),
                            BinOp::Gt,
                            Arc::new(lhs.clone()),
                        );
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
            }
            BinOp::Le => {
                // Continuation: var <= bound. Increasing var: auto-invariant var <= bound.
                if is_modified_var(lhs, modified_set) && !references_modified(rhs, modified_set) {
                    let var_name = extract_modified_var_name(lhs);
                    if let Some(MonotoneDirection::Increasing) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = PureExpr::BinOp(
                            Arc::new(lhs.clone()),
                            BinOp::Le,
                            Arc::new(rhs.clone()),
                        );
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
                // Symmetric: bound <= var => var >= bound (decreasing var)
                if is_modified_var(rhs, modified_set) && !references_modified(lhs, modified_set) {
                    let var_name = extract_modified_var_name(rhs);
                    if let Some(MonotoneDirection::Decreasing) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = PureExpr::BinOp(
                            Arc::new(rhs.clone()),
                            BinOp::Ge,
                            Arc::new(lhs.clone()),
                        );
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
            }
            BinOp::Gt => {
                // Continuation: var > bound. Decreasing var: auto-invariant var > bound.
                if is_modified_var(lhs, modified_set) && !references_modified(rhs, modified_set) {
                    let var_name = extract_modified_var_name(lhs);
                    if let Some(MonotoneDirection::Decreasing) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = PureExpr::BinOp(
                            Arc::new(lhs.clone()),
                            BinOp::Gt,
                            Arc::new(rhs.clone()),
                        );
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
                // Symmetric: bound > var => var < bound (increasing var)
                if is_modified_var(rhs, modified_set) && !references_modified(lhs, modified_set) {
                    let var_name = extract_modified_var_name(rhs);
                    if let Some(MonotoneDirection::Increasing) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = PureExpr::BinOp(
                            Arc::new(rhs.clone()),
                            BinOp::Lt,
                            Arc::new(lhs.clone()),
                        );
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
            }
            BinOp::Ge => {
                // Continuation: var >= bound. Decreasing var: auto-invariant var >= bound.
                if is_modified_var(lhs, modified_set) && !references_modified(rhs, modified_set) {
                    let var_name = extract_modified_var_name(lhs);
                    if let Some(MonotoneDirection::Decreasing) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = PureExpr::BinOp(
                            Arc::new(lhs.clone()),
                            BinOp::Ge,
                            Arc::new(rhs.clone()),
                        );
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
                // Symmetric: bound >= var => var <= bound (increasing var)
                if is_modified_var(rhs, modified_set) && !references_modified(lhs, modified_set) {
                    let var_name = extract_modified_var_name(rhs);
                    if let Some(MonotoneDirection::Increasing) =
                        var_name.and_then(|n| detect_body_effect_direction(n, &body_effects))
                    {
                        let inv = PureExpr::BinOp(
                            Arc::new(rhs.clone()),
                            BinOp::Le,
                            Arc::new(lhs.clone()),
                        );
                        if !contains_invariant(
                            &inv,
                            user_invariants,
                            auto_frame_invariants,
                            auto_stable_requires,
                        ) && !result.contains(&inv)
                        {
                            result.push(inv);
                        }
                    }
                }
            }
            // Ne and Eq exit conditions: the negation gives equality/inequality
            // which doesn't directly provide a useful bound invariant. Skip.
            _ => {}
        }
    }

    result
}

/// When the loop body writes `*x = expr` where `expr` does not reference any
/// modified variable, the deref value is constant across iterations. This
/// function generates `Deref(Var(x)) == expr` for such effects, enabling
/// postcondition reasoning about the final deref value.
///
/// Only deref effects in `effects.deref` are considered (single dereference).
/// Double-deref effects are skipped because they involve nested mutable
/// references whose outer pointer may alias.
fn infer_constant_deref_invariants(
    effects: context::BodyEffects<'_>,
    modified_set: &HashSet<&str>,
    user_invariants: &[PureExpr],
    auto_frame_invariants: &[PureExpr],
) -> Vec<PureExpr> {
    let mut result = Vec::new();

    for (var_name, effect_expr) in effects.deref {
        // Skip if the effect expression references any modified variable.
        // Such effects change each iteration and are not invariant.
        if expr_helpers::expr_references_any_var(effect_expr, modified_set) {
            continue;
        }

        // Look up the sort from the effect expression or from the deref map.
        // The Var in the deref pattern should use the sort from the body effect
        // map's key variable (which is a reference), but since we are generating
        // `Deref(Var(x)) == expr`, the Var sort represents the reference type.
        // Using None lets sort inference handle it.
        let inv = PureExpr::BinOp(
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                var_name.clone(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(effect_expr.clone()),
        );

        if !contains_invariant(&inv, user_invariants, auto_frame_invariants, &[])
            && !result.contains(&inv)
        {
            result.push(inv);
        }
    }

    // NOTE: Double-deref constant invariants for `&mut &mut T` are NOT
    // generated. Nested mutable references may alias (two double-deref
    // paths can refer to the same memory location), making equality
    // invariants potentially unsound. See test
    // `auto_constant_deref_skips_double_deref`. (#1816)

    result
}

#[cfg(test)]
mod tests;
