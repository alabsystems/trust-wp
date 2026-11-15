// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call-site precondition obligation verification under loop invariants.
//!
//! Contains `ObligationOutcome`, `classify_obligation_result`,
//! `record_encoding_error`, `report_obligation_result`,
//! `LoopCallObligationContext`, `worse_result`, and
//! `verify_loop_call_obligations`.

use std::collections::HashMap;
#[cfg(test)]
use std::sync::Arc;

use trust_wp_ay::{
    verify_function_with_modes_outcome, EncodingError, ProofCertificateSummary,
    VerificationOutcome, VerificationRequest, VerificationResult,
};
#[cfg(test)]
use trust_wp_core::logic::type_invariant_method_name;
use trust_wp_core::{
    formula::{BinOp, PureExpr},
    logic::{AdtDecls, LogicFnDef, LogicMode, TypeInvariantDef},
    TrackLevel,
};

use super::super::super::{
    ghost_context::rustc_span_to_source_span,
    helpers::report_counterexample,
    loop_verify::pre_loop_store::PreLoopStoreLinks,
    reporting::{
        verified_evidence_gap_reason, withhold_unvalidated_refutation, VerificationCounters,
    },
    verification_context::VerificationContext,
};

/// Outcome of processing a loop call obligation verification result.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum ObligationOutcome {
    /// A failure or error was recorded in counters; caller should treat as unsuccessful.
    ErrorRecorded,
    /// Obligations verified successfully.
    Verified,
    /// Obligations assumed (not proven). Carries the assumption reason.
    Assumed(String),
    /// Obligations were vacuous because their premises were contradictory.
    Vacuous,
    /// Obligations returned a verified-shaped result without accepted proof evidence.
    EvidenceGap,
}

/// Map a `VerificationResult` to counter updates and an `ObligationOutcome`.
///
/// TyCtxt-free core of `report_obligation_result` — handles the `Ok(...)` branches
/// that don't need compiler context. Emits diagnostics to stderr for `Failed` and
/// `Unknown` outcomes.
///
/// Returns `(ObligationOutcome, delta_failed, delta_errors, delta_demoted)` so
/// callers (and tests) can verify the counter accounting independently.
pub(crate) fn classify_obligation_result(
    result: VerificationResult,
    def_path: &str,
    loc: &str,
) -> (ObligationOutcome, usize, usize, usize) {
    match result {
        VerificationResult::Verified(_) => (ObligationOutcome::Verified, 0, 0, 0),
        VerificationResult::Assumed(reason) => {
            eprintln!("trust-wp: {def_path} assumed (loop call obligations: {reason})");
            eprintln!("  at {loc}");
            (ObligationOutcome::Assumed(reason), 0, 0, 0)
        }
        VerificationResult::Failed(counterexample) => {
            eprintln!("trust-wp: {def_path} FAILED ✗ (loop call obligations)");
            eprintln!("  at {loc}");
            eprintln!("  check: call-site precondition obligations under loop invariants");
            report_counterexample(&counterexample);
            (ObligationOutcome::ErrorRecorded, 1, 0, 0)
        }
        VerificationResult::Unknown(ref reason) => {
            // Vacuous proofs indicate contradictory premises — do NOT
            // count as verified (#2663). Report as a warning and keep it
            // visible through the vacuous telemetry counter.
            let is_vacuous = matches!(
                reason,
                trust_wp_ay::UnknownReason::SolverMessage(msg) if msg.contains("vacuous proof")
            );
            if is_vacuous {
                eprintln!(
                    "trust-wp: {def_path} vacuous (loop obligations, contradictory premises)"
                );
                eprintln!("  at {loc}");
                return (ObligationOutcome::Vacuous, 0, 0, 0);
            }
            // Track demotions from the unsoundness demotion pipeline (#2106).
            let is_demoted = matches!(reason, trust_wp_ay::UnknownReason::Demoted(_));
            eprintln!("trust-wp: {def_path} unknown (loop call obligations: {reason})");
            eprintln!("  at {loc}");
            (
                ObligationOutcome::ErrorRecorded,
                0,
                1,
                usize::from(is_demoted),
            )
        }
        // VerificationResult is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => (ObligationOutcome::ErrorRecorded, 0, 1, 0),
    }
}

pub(crate) fn classify_obligation_outcome(
    outcome: VerificationOutcome,
    def_path: &str,
    loc: &str,
) -> (ObligationOutcome, usize, usize, usize, usize, usize) {
    // No FAILED without a validated counterexample -- applied here as well as
    // at the ay boundary so this classifier is correct for ANY outcome handed
    // to it, including one a caller built itself. Idempotent; the discarded
    // count is tallied by `report_obligation_result`, which owns the counters.
    let outcome = withhold_unvalidated_refutation(outcome, &mut 0);
    if let Some(reason) = verified_evidence_gap_reason(&outcome) {
        eprintln!("trust-wp: {def_path} evidence gap (loop call obligations: {reason})");
        eprintln!("  at {loc}");
        return (ObligationOutcome::EvidenceGap, 0, 0, 0, 1, 1);
    }
    let (outcome, failed, errors, demoted) =
        classify_obligation_result(outcome.result, def_path, loc);
    (outcome, failed, errors, demoted, 0, 0)
}

/// TyCtxt-free core of the `Err(EncodingError)` branch of `report_obligation_result`.
///
/// Records the error in the breakdown tracker, increments the aggregate errors
/// counter, and emits diagnostics to stderr. Returns `ErrorRecorded` so callers
/// treat the outcome as unsuccessful.
///
/// Kept TyCtxt-free so the counter-mutation logic is directly testable without
/// a compiler context (#1996).
pub(crate) fn record_encoding_error(
    err: &EncodingError,
    counters: &mut VerificationCounters,
    def_path: &str,
    loc: &str,
) -> ObligationOutcome {
    counters.encoding_errors.record(err);
    counters.errors += 1;
    eprintln!("trust-wp: {def_path} error while verifying loop call obligations: {err}");
    eprintln!("  at {loc}");
    ObligationOutcome::ErrorRecorded
}

/// Dispatch a loop call obligation verification result to counters and diagnostics.
///
/// Handles `Failed`, `Unknown`, and `Err` outcomes by updating counters and
/// emitting diagnostics, returning `ErrorRecorded`. Returns `Verified` or
/// `Assumed` for success outcomes so the caller can apply context-specific
/// reporting (e.g., spec-drop fail-closed logic, message suffix selection).
///
/// The one dispatch shared by both call-obligation result sites in
/// `verify_contract_loop_path` — the partial-result `Ok` arm and
/// `handle_all_verified` — so their counter accounting cannot drift apart
/// (#1986).
pub(crate) fn report_obligation_result(
    result: Result<VerificationOutcome, EncodingError>,
    vctx: &VerificationContext<'_, '_>,
    counters: &mut VerificationCounters,
) -> ObligationOutcome {
    match result {
        Ok(outcome) => {
            let outcome =
                withhold_unvalidated_refutation(outcome, &mut counters.refutations_withheld);
            let (
                outcome,
                delta_failed,
                delta_errors,
                delta_demoted,
                delta_evidence_gaps,
                delta_warnings,
            ) = classify_obligation_outcome(outcome, vctx.def_path, vctx.loc);
            counters.failed = counters.failed.saturating_add(delta_failed);
            counters.errors = counters.errors.saturating_add(delta_errors);
            counters.demoted = counters.demoted.saturating_add(delta_demoted);
            counters.evidence_gaps = counters.evidence_gaps.saturating_add(delta_evidence_gaps);
            counters.warnings = counters.warnings.saturating_add(delta_warnings);
            if matches!(outcome, ObligationOutcome::Vacuous) {
                counters.vacuous += 1;
                counters.warnings += 1;
            }
            if matches!(outcome, ObligationOutcome::Assumed(_)) {
                counters.assumed += 1;
            }
            outcome
        }
        Err(e) => {
            // Enrich the error with source-level span information when available.
            // This is purely cosmetic — the counter accounting is delegated to
            // `record_encoding_error` which is TyCtxt-free and directly testable.
            let enriched = match rustc_span_to_source_span(
                vctx.tcx.sess.source_map(),
                vctx.tcx.def_span(vctx.contract.def_id),
            ) {
                Some(src_span) => e.with_span(src_span),
                None => e,
            };
            record_encoding_error(&enriched, counters, vctx.def_path, vctx.loc)
        }
    }
}

/// Context for verifying call-site precondition obligations in loop-verified functions.
pub(crate) struct LoopCallObligationContext<'a> {
    pub(crate) base_requires: &'a [PureExpr],
    /// Assumptions produced by calls before the first loop. These are valid
    /// for genuinely pre-loop obligations, but are intentionally not exposed
    /// to in-loop obligation groups.
    pub(crate) pre_loop_assumptions: &'a [PureExpr],
    /// Effective invariants of each loop, indexed like `loop_analysis.loops`.
    /// A group assumes only the entry at its own `loop_index`: the invariants
    /// of loop `k` hold at loop `k`'s header, and pooling them makes one loop's
    /// stable bindings premises of another loop's checks
    /// (`s40v5_crossloop_user_invariant_pooled.rs`).
    pub(crate) per_loop_invariants: &'a [Vec<PureExpr>],
    pub(crate) pre_loop_obligations: &'a [PureExpr],
    /// Per-loop obligation groups, each with its own condition (#752).
    pub(crate) loop_obligation_groups: &'a [super::super::super::parsing::LoopObligationGroup],
    pub(crate) logic_fns_opt: Option<&'a [LogicFnDef]>,
    pub(crate) mode_overrides_opt: Option<&'a [LogicMode]>,
    /// Type invariant definitions needed for the encoder to resolve
    /// type-level predicates in obligation expressions. (#1709)
    pub(crate) type_invariants_opt: Option<&'a [TypeInvariantDef]>,
    /// Type-level constants (e.g., `size_of::<T>()`) needed for the encoder
    /// to resolve constant expressions in obligations. (#1709)
    pub(crate) type_constants_opt: Option<&'a HashMap<String, PureExpr>>,
    /// Rustc-backed ADT declarations for native datatype registration.
    /// Required for the encoder to resolve SliceIndexSpec axioms and other
    /// trait-based method calls in obligation expressions. (#1709)
    pub(crate) adt_decls_opt: Option<&'a AdtDecls>,
    /// Machine-integer ranges of ADT fields. A field value outside its type's
    /// range is not one the program can hold, so a model picking one is not a
    /// counterexample (loop_call_obligation_field_range_control).
    pub(crate) adt_field_ranges_opt: Option<&'a trust_wp_core::logic::AdtFieldRanges>,
    pub(crate) track_level: TrackLevel,
    pub(crate) timeout: Option<std::time::Duration>,
}

/// Pick the more severe of two `VerificationResult` values (#2010).
/// Priority: Failed > Unknown > Assumed > Verified.
#[cfg(test)]
pub(crate) fn worse_result(
    current: Option<VerificationResult>,
    new: VerificationResult,
) -> VerificationResult {
    let Some(current) = current else {
        return new;
    };
    fn severity(r: &VerificationResult) -> u8 {
        #[allow(unreachable_patterns)]
        match r {
            VerificationResult::Verified(_) => 0,
            VerificationResult::Assumed(_) => 1,
            VerificationResult::Unknown(_) => 2,
            VerificationResult::Failed(_) => 3,
            _ => 3,
        }
    }
    if severity(&new) > severity(&current) {
        new
    } else {
        current
    }
}

fn push_dedup(vec: &mut Vec<PureExpr>, expr: PureExpr) {
    if !vec.contains(&expr) {
        vec.push(expr);
    }
}

/// The effective invariants a group's VC may assume: its own loop's, never
/// another loop's (`s40v5_crossloop_user_invariant_pooled.rs`). A group with no
/// (or an out-of-range) loop index assumes none — dropping premises only.
fn group_invariants<'a>(
    ctx: &LoopCallObligationContext<'a>,
    group: &super::super::super::parsing::LoopObligationGroup,
) -> &'a [PureExpr] {
    group
        .loop_index
        .and_then(|index| ctx.per_loop_invariants.get(index))
        .map_or(&[], Vec::as_slice)
}

fn loop_group_obligation_requires(
    ctx: &LoopCallObligationContext<'_>,
    group: &super::super::super::parsing::LoopObligationGroup,
) -> Vec<PureExpr> {
    let invariants = group_invariants(ctx, group);
    let extra_condition = usize::from(group.condition.is_some());
    let mut obligation_requires = Vec::with_capacity(
        ctx.base_requires.len() + invariants.len() + group.assumptions.len() + extra_condition,
    );
    obligation_requires.extend(ctx.base_requires.iter().cloned());
    obligation_requires.extend(group.assumptions.iter().cloned());
    obligation_requires.extend(invariants.iter().cloned());

    if let Some(ref cond) = group.condition {
        // Condition-guarded range facts are not raw invariants: they only hold
        // while this loop body is active. Since this VC also assumes the loop
        // condition, expose matching RHS facts directly to avoid making simple
        // call obligations reconstruct bounds through an implication.
        for invariant in invariants {
            if let PureExpr::BinOp(lhs, BinOp::Implies, rhs) = invariant {
                if lhs.as_ref() == cond {
                    push_dedup(&mut obligation_requires, rhs.as_ref().clone());
                }
            }
        }
        push_dedup(&mut obligation_requires, cond.clone());
    }

    obligation_requires
}

#[cfg(test)]
#[cfg(test)]
fn filter_directly_unproved_obligations(
    requires: &[PureExpr],
    obligations: &[PureExpr],
) -> Vec<PureExpr> {
    filter_directly_unproved_obligations_with_facts(requires, obligations)
}

#[cfg(test)]
fn filter_directly_unproved_obligations_with_ctx(
    ctx: &LoopCallObligationContext<'_>,
    requires: &[PureExpr],
    obligations: &[PureExpr],
) -> Vec<PureExpr> {
    let direct_facts = direct_obligation_facts(ctx, requires);
    filter_directly_unproved_obligations_with_facts(&direct_facts, obligations)
}

#[cfg(test)]
fn filter_directly_unproved_obligations_with_facts(
    direct_facts: &[PureExpr],
    obligations: &[PureExpr],
) -> Vec<PureExpr> {
    obligations
        .iter()
        .filter(|obligation| !direct_requires_prove_obligation(direct_facts, obligation))
        .cloned()
        .collect()
}

#[cfg(test)]
fn direct_obligation_facts(
    ctx: &LoopCallObligationContext<'_>,
    requires: &[PureExpr],
) -> Vec<PureExpr> {
    let mut facts = requires.to_vec();
    let Some(type_invariants) = ctx.type_invariants_opt else {
        return facts;
    };

    for require in requires {
        let PureExpr::MethodCall {
            receiver,
            method,
            args,
        } = require
        else {
            continue;
        };
        if !args.is_empty() {
            continue;
        }
        let Some(inv_def) = type_invariants
            .iter()
            .find(|inv| method == &type_invariant_method_name(inv.type_name()))
        else {
            continue;
        };
        let mut substitutions = HashMap::new();
        substitutions.insert(inv_def.self_param().to_string(), receiver.as_ref().clone());
        let body = inv_def.body().substitute(&substitutions);
        push_lightweight_conjuncts(&mut facts, &body);
    }

    facts
}

#[cfg(test)]
fn push_lightweight_conjuncts(out: &mut Vec<PureExpr>, expr: &PureExpr) {
    if let PureExpr::BinOp(lhs, BinOp::And, rhs) = expr {
        push_lightweight_conjuncts(out, lhs);
        push_lightweight_conjuncts(out, rhs);
    } else if is_lightweight_direct_fact(expr) {
        push_dedup(out, expr.clone());
    }
}

#[cfg(test)]
fn is_lightweight_direct_fact(expr: &PureExpr) -> bool {
    !matches!(
        expr,
        PureExpr::Forall { .. } | PureExpr::Exists { .. } | PureExpr::Match { .. }
    )
}

#[cfg(test)]
fn direct_requires_prove_obligation(requires: &[PureExpr], obligation: &PureExpr) -> bool {
    if requires.contains(obligation) {
        return true;
    }

    match obligation {
        PureExpr::BinOp(antecedent, BinOp::Implies, consequent) => {
            // Proving the consequent unconditionally is enough for a guarded
            // obligation. If the guard itself contains the needed path fact
            // (for example `call_result && (call_result ==> p)`), discharge it
            // propositionally instead of sending that shape to the quantified
            // solver.
            direct_requires_prove_obligation(requires, consequent)
                || antecedent_directly_proves_obligation(requires, antecedent, consequent)
        }
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            direct_requires_prove_obligation(requires, lhs)
                && direct_requires_prove_obligation(requires, rhs)
        }
        _ => {
            direct_requires_prove_in_bounds(requires, obligation)
                || direct_requires_prove_int_bound(requires, obligation)
                || direct_requires_prove_positive_scaled_expr(requires, obligation)
        }
    }
}

#[cfg(test)]
fn antecedent_directly_proves_obligation(
    requires: &[PureExpr],
    antecedent: &PureExpr,
    obligation: &PureExpr,
) -> bool {
    let mut facts = requires.to_vec();
    let mut antecedent_facts = Vec::new();
    flatten_and_conjuncts(antecedent, &mut antecedent_facts);
    facts.extend(antecedent_facts.into_iter().cloned());

    facts.iter().any(|fact| {
        fact_directly_proves_obligation(&facts, fact, obligation)
            || direct_fact_matches_obligation(fact, obligation)
    })
}

#[cfg(test)]
fn flatten_and_conjuncts<'a>(expr: &'a PureExpr, out: &mut Vec<&'a PureExpr>) {
    if let PureExpr::BinOp(lhs, BinOp::And, rhs) = expr {
        flatten_and_conjuncts(lhs, out);
        flatten_and_conjuncts(rhs, out);
    } else {
        out.push(expr);
    }
}

#[cfg(test)]
fn fact_directly_proves_obligation(
    facts: &[PureExpr],
    fact: &PureExpr,
    obligation: &PureExpr,
) -> bool {
    let PureExpr::BinOp(fact_antecedent, BinOp::Implies, fact_consequent) = fact else {
        return false;
    };
    let mut consequent_facts = Vec::new();
    flatten_and_conjuncts(fact_consequent, &mut consequent_facts);
    let consequent_facts: Vec<_> = consequent_facts.into_iter().cloned().collect();
    (direct_fact_matches_obligation(fact_consequent, obligation)
        || direct_requires_prove_obligation(&consequent_facts, obligation))
        && fact_set_contains(facts, fact_antecedent)
}

#[cfg(test)]
fn fact_set_contains(facts: &[PureExpr], expected: &PureExpr) -> bool {
    match expected {
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            fact_set_contains(facts, lhs) && fact_set_contains(facts, rhs)
        }
        _ => facts
            .iter()
            .any(|fact| direct_fact_matches_obligation(fact, expected)),
    }
}

#[cfg(test)]
fn direct_fact_matches_obligation(fact: &PureExpr, obligation: &PureExpr) -> bool {
    fact == obligation
        || matches!(
            fact,
            PureExpr::BinOp(lhs, BinOp::Eq, rhs)
                if matches!(rhs.as_ref(), PureExpr::Bool(true)) && lhs.as_ref() == obligation
        )
        || matches!(
            fact,
            PureExpr::BinOp(lhs, BinOp::Eq, rhs)
                if matches!(lhs.as_ref(), PureExpr::Bool(true)) && rhs.as_ref() == obligation
        )
}

#[cfg(test)]
fn direct_requires_prove_in_bounds(requires: &[PureExpr], obligation: &PureExpr) -> bool {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = obligation
    else {
        return false;
    };
    if method != "in_bounds" || args.len() != 1 {
        return false;
    }
    let index = receiver.as_ref();
    let seq = &args[0];

    requires
        .iter()
        .any(|req| is_direct_nonnegative_fact(req, index))
        && requires
            .iter()
            .any(|req| is_direct_len_upper_bound_fact(req, index, seq))
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg(test)]
enum IntBoundKind {
    Lower,
    Upper,
}

#[cfg(test)]
struct IntBound<'a> {
    expr: &'a PureExpr,
    kind: IntBoundKind,
    value: i64,
}

#[cfg(test)]
fn direct_requires_prove_int_bound(requires: &[PureExpr], obligation: &PureExpr) -> bool {
    let Some(target) = normalize_nonstrict_int_bound(obligation) else {
        return false;
    };

    requires.iter().any(|req| {
        normalize_nonstrict_int_bound(req)
            .as_ref()
            .is_some_and(|candidate| int_bound_covers(candidate, &target))
    })
}

#[cfg(test)]
fn normalize_nonstrict_int_bound(expr: &PureExpr) -> Option<IntBound<'_>> {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Le, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
            (PureExpr::Int(value), bounded_expr) => Some(IntBound {
                expr: bounded_expr,
                kind: IntBoundKind::Lower,
                value: *value,
            }),
            (bounded_expr, PureExpr::Int(value)) => Some(IntBound {
                expr: bounded_expr,
                kind: IntBoundKind::Upper,
                value: *value,
            }),
            _ => None,
        },
        PureExpr::BinOp(lhs, BinOp::Ge, rhs) => match (lhs.as_ref(), rhs.as_ref()) {
            (bounded_expr, PureExpr::Int(value)) => Some(IntBound {
                expr: bounded_expr,
                kind: IntBoundKind::Lower,
                value: *value,
            }),
            (PureExpr::Int(value), bounded_expr) => Some(IntBound {
                expr: bounded_expr,
                kind: IntBoundKind::Upper,
                value: *value,
            }),
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
fn direct_requires_prove_positive_scaled_expr(
    requires: &[PureExpr],
    obligation: &PureExpr,
) -> bool {
    let Some(scaled_expr) = strict_positive_expr(obligation) else {
        return false;
    };
    let Some(base_expr) = positive_scaled_base(scaled_expr) else {
        return false;
    };
    requires.iter().any(|fact| {
        strict_positive_expr(fact).is_some_and(|positive_fact| {
            expr_equivalent_under_direct_equalities(requires, positive_fact, &base_expr)
        })
    })
}

#[cfg(test)]
fn strict_positive_expr(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::BinOp(lhs, op, rhs) = expr else {
        return None;
    };
    match op {
        BinOp::Lt if matches!(lhs.as_ref(), PureExpr::Int(0)) => Some(rhs),
        BinOp::Gt if matches!(rhs.as_ref(), PureExpr::Int(0)) => Some(lhs),
        _ => None,
    }
}

#[cfg(test)]
fn positive_scaled_base(expr: &PureExpr) -> Option<PureExpr> {
    match expr {
        PureExpr::View(inner) => {
            positive_scaled_base_inner(inner).map(|base| PureExpr::View(Arc::new(base)))
        }
        _ => positive_scaled_base_inner(expr),
    }
}

#[cfg(test)]
fn positive_scaled_base_inner(expr: &PureExpr) -> Option<PureExpr> {
    let PureExpr::BinOp(lhs, BinOp::Mul, rhs) = expr else {
        return None;
    };
    match (lhs.as_ref(), rhs.as_ref()) {
        (base, PureExpr::Int(factor)) if *factor > 0 => Some(base.clone()),
        (PureExpr::Int(factor), base) if *factor > 0 => Some(base.clone()),
        _ => None,
    }
}

#[cfg(test)]
fn expr_equivalent_under_direct_equalities(
    facts: &[PureExpr],
    lhs: &PureExpr,
    rhs: &PureExpr,
) -> bool {
    lhs == rhs
        || facts
            .iter()
            .any(|fact| equality_sides(fact).is_some_and(|(a, b)| same_expr_pair(a, b, lhs, rhs)))
}

#[cfg(test)]
fn equality_sides(expr: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    Some((lhs, rhs))
}

#[cfg(test)]
fn same_expr_pair(a: &PureExpr, b: &PureExpr, lhs: &PureExpr, rhs: &PureExpr) -> bool {
    (a == lhs && b == rhs) || (a == rhs && b == lhs)
}

#[cfg(test)]
fn int_bound_covers(candidate: &IntBound<'_>, target: &IntBound<'_>) -> bool {
    if candidate.kind != target.kind || candidate.expr != target.expr {
        return false;
    }

    match candidate.kind {
        IntBoundKind::Lower => candidate.value >= target.value,
        IntBoundKind::Upper => candidate.value <= target.value,
    }
}

#[cfg(test)]
fn is_direct_nonnegative_fact(expr: &PureExpr, index: &PureExpr) -> bool {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Ge, rhs) => {
            lhs.as_ref() == index && matches!(rhs.as_ref(), PureExpr::Int(0))
        }
        PureExpr::BinOp(lhs, BinOp::Le, rhs) => {
            matches!(lhs.as_ref(), PureExpr::Int(0)) && rhs.as_ref() == index
        }
        _ => false,
    }
}

#[cfg(test)]
fn is_direct_len_upper_bound_fact(expr: &PureExpr, index: &PureExpr, seq: &PureExpr) -> bool {
    let PureExpr::BinOp(lhs, BinOp::Lt, rhs) = expr else {
        return false;
    };
    if lhs.as_ref() != index {
        return false;
    }
    matches!(
        rhs.as_ref(),
        PureExpr::MethodCall { receiver, method, args }
            if receiver.as_ref() == seq && method == "len" && args.is_empty()
    )
}

fn verify_function_obligations_outcome(
    ctx: &LoopCallObligationContext<'_>,
    requires: &[PureExpr],
    obligations: &[PureExpr],
    guarded_marker: bool,
) -> Result<VerificationOutcome, EncodingError> {
    verify_function_with_modes_outcome(
        VerificationRequest::new(requires, obligations)
            // D-27: every goal here is a call obligation the DRIVER built,
            // so a `false` among them is always a fail-closed marker
            // for a construct trust-wp could not model — never a user clause.
            // A marker the loop body walk put under its path is `path ⇒
            // false`, which no scan for `false` sees; the walk says so.
            .injected_fail_closed_goal(
                guarded_marker || trust_wp_ay::goals_carry_fail_closed_marker(obligations),
            )
            .logic_fns(ctx.logic_fns_opt)
            .mode_overrides(ctx.mode_overrides_opt)
            .type_invariants(ctx.type_invariants_opt)
            .type_constants(ctx.type_constants_opt)
            .adt_decls(ctx.adt_decls_opt.cloned())
            .adt_field_ranges(ctx.adt_field_ranges_opt.cloned())
            .track(Some(ctx.track_level))
            .timeout(ctx.timeout),
    )
}

#[cfg(test)]
#[tracing::instrument(
    name = "trust_wp::verify_loop_call_obligations",
    level = "debug",
    skip_all,
    fields(
        pre_loop = ctx.pre_loop_obligations.len(),
        loop_groups = ctx.loop_obligation_groups.len(),
    )
)]
pub(crate) fn verify_loop_call_obligations(
    ctx: &LoopCallObligationContext<'_>,
) -> Result<VerificationResult, EncodingError> {
    Ok(verify_loop_call_obligations_outcome(ctx)?.result)
}

pub(crate) fn verify_loop_call_obligations_outcome(
    ctx: &LoopCallObligationContext<'_>,
) -> Result<VerificationOutcome, EncodingError> {
    // Track the worst result across all obligation groups (#2010, #752).
    // Priority: Failed > Unknown > Assumed > Verified.
    // Pre-loop and per-loop obligations are independent VCs, so a Failed in
    // any group is more actionable than an Unknown from another (#1715).
    let mut worst: Option<VerificationOutcome> = None;
    let mut first_assumed: Option<VerificationOutcome> = None;
    let mut first_verified: Option<VerificationOutcome> = None;
    let mut verified_summary: Option<ProofCertificateSummary> = None;
    let mut verified_summaries_complete = true;

    // Filter pre-loop obligations to remove those already covered by per-loop
    // groups. The function-level body extraction walks into loop bodies and
    // collects call obligations from both pre-loop and in-loop calls. Per-loop
    // groups also collect in-loop obligations with proper loop conditions.
    // Without filtering, in-loop obligations get checked twice: once as
    // pre-loop (without condition, often fails) and once per-loop (with
    // condition, correct). Remove duplicates so only genuinely pre-loop
    // obligations are checked here.
    let filtered_pre_loop: Vec<_> = ctx
        .pre_loop_obligations
        .iter()
        .filter(|pre_obl| {
            !ctx.loop_obligation_groups.iter().any(|g| {
                g.obligations.iter().any(|loop_obl| {
                    // Match raw obligation or the RHS of a guarded implication.
                    loop_obl == *pre_obl
                        || matches!(
                            loop_obl,
                            PureExpr::BinOp(_, BinOp::Implies, rhs) if rhs.as_ref() == *pre_obl
                        )
                })
            })
        })
        .cloned()
        .collect();
    if !filtered_pre_loop.is_empty() {
        // No loop invariant holds before the first loop runs:
        // `need_pos(x); x = 5; #[invariant(x > 0)] loop {}` must not discharge
        // `x > 0` at the call from the invariant established later
        // (`s40v5_preloop_call_later_invariant.rs`).
        let mut obligation_requires =
            Vec::with_capacity(ctx.base_requires.len() + ctx.pre_loop_assumptions.len());
        obligation_requires.extend(ctx.base_requires.iter().cloned());
        obligation_requires.extend(ctx.pre_loop_assumptions.iter().cloned());

        if std::env::var_os("TRUST_WP_LOOP_GROUP_DUMP").is_some() {
            eprintln!(
                "TRUST_WP_LOOP_GROUP_DUMP pre_loop requires={obligation_requires:?} obligations={filtered_pre_loop:?}"
            );
        }
        let outcome = verify_function_obligations_outcome(
            ctx,
            &obligation_requires,
            &filtered_pre_loop,
            false,
        )?;

        match &outcome.result {
            VerificationResult::Verified(_) => {
                verified_summaries_complete &=
                    accumulate_verified_summary(&mut verified_summary, &outcome);
                if first_verified.is_none() {
                    first_verified = Some(outcome);
                }
            }
            VerificationResult::Assumed(_) => {
                if first_assumed.is_none() {
                    first_assumed = Some(outcome);
                }
            }
            _ => {
                worst = Some(worse_outcome(worst, outcome));
            }
        }
    }

    // Verify each loop's in-body obligations with that loop's condition (#752).
    for group in ctx.loop_obligation_groups {
        if group.obligations.is_empty() {
            continue;
        }
        let obligation_requires = loop_group_obligation_requires(ctx, group);
        if std::env::var_os("TRUST_WP_LOOP_GROUP_DUMP").is_some() {
            eprintln!(
                "TRUST_WP_LOOP_GROUP_DUMP vc condition={:?} requires={:?} obligations={:?}",
                group.condition, obligation_requires, group.obligations
            );
        }

        let mut outcome = verify_function_obligations_outcome(
            ctx,
            &obligation_requires,
            &group.obligations,
            group.injected_fail_closed,
        )?;
        if let Some(unstated) = group.condition_unstated.as_deref() {
            withhold_condition_refutation(&mut outcome, unstated);
        }
        // The group's VC reads a name a store through a reference before the
        // loop changed at its entry value, under the precondition and the
        // invariants inferred from it (loop_call_obligation_after_param_store_control).
        if let Some(reason) =
            PreLoopStoreLinks::new(&group.pre_loop_stored_names, &obligation_requires, [])
                .reason(&group.obligations)
        {
            withhold_stale_store_refutation(&mut outcome, &reason);
        }
        // An obligation reads a havoc the arithmetic walk bound for a local no
        // loop writes; the program gave it one value before the loop, which
        // the VC leaves free (loop_overflow_after_param_store_control).
        if let Some(havoc) =
            PreLoopStoreLinks::new(&group.unstated_entry_values, &obligation_requires, [])
                .linked(&group.obligations)
        {
            withhold_stale_store_refutation(
                &mut outcome,
                &format!("the loop VC leaves free a value code before the loop fixed (`{havoc}`)"),
            );
        }

        match &outcome.result {
            VerificationResult::Verified(_) => {
                verified_summaries_complete &=
                    accumulate_verified_summary(&mut verified_summary, &outcome);
                if first_verified.is_none() {
                    first_verified = Some(outcome);
                }
            }
            VerificationResult::Assumed(_) => {
                if first_assumed.is_none() {
                    first_assumed = Some(outcome);
                }
            }
            _ => {
                worst = Some(worse_outcome(worst, outcome));
            }
        }
    }

    // Return worst result: Failed > Unknown > Assumed > Verified (#2010).
    if let Some(outcome) = worst {
        Ok(outcome)
    } else if let Some(outcome) = first_assumed {
        Ok(outcome)
    } else if let Some(mut outcome) = first_verified {
        // Each group is an independent VC. `verify_function_with_modes_outcome`
        // has already applied mandatory proof authority to every one, but the
        // representative outcome alone would otherwise retain only the first
        // group's certificate. Publish the conjunction of all checked
        // certificates so the aggregate cannot claim authority for a strict
        // subset of the loop-call obligations.
        outcome.result = VerificationResult::Verified(
            verified_summaries_complete
                .then_some(verified_summary)
                .flatten(),
        );
        Ok(outcome)
    } else {
        verify_function_with_modes_outcome(
            VerificationRequest::new(&[], &[])
                .logic_fns(ctx.logic_fns_opt)
                .mode_overrides(ctx.mode_overrides_opt)
                .type_invariants(ctx.type_invariants_opt)
                .type_constants(ctx.type_constants_opt)
                .adt_decls(ctx.adt_decls_opt.cloned())
                .track(Some(ctx.track_level))
                .timeout(ctx.timeout),
        )
    }
}

/// Withhold a refutation over a VC that assumes a loop condition reading a
/// value no premise states: the model picks that value freely, so it need not
/// be a state the program reaches (loop_condition_call_unstated_control).
pub(crate) fn withhold_condition_refutation(outcome: &mut VerificationOutcome, unstated: &str) {
    if matches!(outcome.result, VerificationResult::Failed(_)) {
        *outcome = VerificationOutcome::without_provenance(VerificationResult::Unknown(
            trust_wp_ay::UnknownReason::SolverMessage(format!(
                "{}: the loop condition reads a value the loop VC does not state: {unstated}",
                trust_wp_ay::REFUTATION_AUTHORITY_MESSAGE
            )),
        ));
    }
}

/// Withhold a refutation over a VC that reads a stale entry value
/// (`PreLoopStoreLinks::reason`), or a value it leaves free although the
/// program fixed it before the loop.
fn withhold_stale_store_refutation(outcome: &mut VerificationOutcome, reason: &str) {
    if matches!(outcome.result, VerificationResult::Failed(_)) {
        *outcome = VerificationOutcome::without_provenance(VerificationResult::Unknown(
            trust_wp_ay::UnknownReason::SolverMessage(format!(
                "{}: {reason}",
                trust_wp_ay::REFUTATION_AUTHORITY_MESSAGE
            )),
        ));
    }
}

fn accumulate_verified_summary(
    aggregate: &mut Option<ProofCertificateSummary>,
    outcome: &VerificationOutcome,
) -> bool {
    let VerificationResult::Verified(Some(summary)) = &outcome.result else {
        // Public function verification has already applied mandatory proof
        // authority, so a verified result without a summary is unreachable.
        // Keep this fail-closed if that boundary ever changes.
        return false;
    };

    *aggregate = Some(match aggregate.take() {
        Some(previous) => combine_independent_proof_summaries(previous, summary.clone()),
        None => summary.clone(),
    });
    true
}

fn combine_independent_proof_summaries(
    lhs: ProofCertificateSummary,
    rhs: ProofCertificateSummary,
) -> ProofCertificateSummary {
    ProofCertificateSummary {
        strict_verified: lhs.strict_verified && rhs.strict_verified,
        restricted_rule_subset: lhs.restricted_rule_subset && rhs.restricted_rule_subset,
        trust_count: lhs.trust_count.saturating_add(rhs.trust_count),
        trust_fallback_count: lhs
            .trust_fallback_count
            .saturating_add(rhs.trust_fallback_count),
        hole_count: lhs.hole_count.saturating_add(rhs.hole_count),
        theory_lemma_count: lhs
            .theory_lemma_count
            .saturating_add(rhs.theory_lemma_count),
        resolution_count: lhs.resolution_count.saturating_add(rhs.resolution_count),
        farkas_certificate_count: lhs
            .farkas_certificate_count
            .saturating_add(rhs.farkas_certificate_count),
        lrat_present: lhs.lrat_present && rhs.lrat_present,
        // Alethe step identifiers are proof-local, so concatenating independent
        // renderings would not form one replayable wire proof.
        alethe_text: None,
    }
}

fn worse_outcome(
    current: Option<VerificationOutcome>,
    next: VerificationOutcome,
) -> VerificationOutcome {
    let Some(current) = current else {
        return next;
    };
    let current_rank = obligation_rank(&current.result);
    let next_rank = obligation_rank(&next.result);
    if next_rank < current_rank {
        return next;
    }
    if next_rank == current_rank
        && matches!(&next.result, VerificationResult::Unknown(_))
        && matches!(
            &current.result,
            VerificationResult::Unknown(trust_wp_ay::UnknownReason::Unspecified)
        )
    {
        return next;
    }
    current
}

fn obligation_rank(result: &VerificationResult) -> u8 {
    match result {
        VerificationResult::Failed(_) => 0,
        VerificationResult::Unknown(_) => 1,
        VerificationResult::Assumed(_) => 2,
        VerificationResult::Verified(_) => 3,
        #[allow(unreachable_patterns)]
        _ => 4,
    }
}

#[cfg(test)]
mod tests {
    use std::{sync::Arc, time::Duration};

    use trust_wp_core::{
        formula::{intern_sort_name, ExprSort, PureExpr},
        logic::{type_invariant_method_name, TypeInvariantDef},
    };

    use super::{
        combine_independent_proof_summaries, loop_group_obligation_requires, BinOp,
        LoopCallObligationContext,
    };
    use crate::callbacks::parsing::LoopObligationGroup;

    fn proof_summary(
        resolution_count: u32,
        farkas_certificate_count: u32,
    ) -> trust_wp_ay::ProofCertificateSummary {
        trust_wp_ay::ProofCertificateSummary {
            strict_verified: true,
            restricted_rule_subset: true,
            trust_count: 0,
            trust_fallback_count: 0,
            hole_count: 0,
            theory_lemma_count: 0,
            resolution_count,
            farkas_certificate_count,
            lrat_present: true,
            alethe_text: Some("proof".to_string()),
        }
    }

    #[test]
    fn independent_loop_call_certificates_are_combined_conjunctively() {
        let combined =
            combine_independent_proof_summaries(proof_summary(3, 1), proof_summary(5, 2));

        assert!(combined.is_fully_verified());
        assert!(combined.restricted_rule_subset);
        assert!(combined.lrat_present);
        assert_eq!(combined.resolution_count, 8);
        assert_eq!(combined.farkas_certificate_count, 3);
        assert!(combined.alethe_text.is_none());
    }

    fn var(name: &str, sort: Option<ExprSort>) -> PureExpr {
        PureExpr::Var(name.to_string(), sort)
    }

    fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: method.to_string(),
            args,
        }
    }

    fn binop(lhs: PureExpr, op: BinOp, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), op, Arc::new(rhs))
    }

    fn buckets_len(receiver: PureExpr) -> PureExpr {
        method_call(
            PureExpr::View(Arc::new(PureExpr::LogicFnCall {
                name: "__trust_wp_field_buckets".to_string(),
                args: vec![receiver],
            })),
            "len",
            vec![],
        )
    }

    #[test]
    fn loop_group_requires_expose_matching_guarded_fact_only_when_condition_active() {
        let condition = PureExpr::Var("__iter_result_12_is_some".to_string(), Some(ExprSort::Bool));
        let matching_upper_bound = PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
            BinOp::Lt,
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                    PureExpr::Var(
                        "v".to_string(),
                        Some(ExprSort::MutRef(Box::new(ExprSort::Seq))),
                    ),
                ))))),
                method: "len".to_string(),
                args: vec![],
            }),
        );
        let other_condition = PureExpr::Var("other_loop_active".to_string(), Some(ExprSort::Bool));
        let other_fact = PureExpr::BinOp(
            Arc::new(PureExpr::Var("j".to_string(), Some(ExprSort::Int))),
            BinOp::Lt,
            Arc::new(PureExpr::Var("n".to_string(), Some(ExprSort::Int))),
        );
        let guarded_upper_bound = PureExpr::BinOp(
            Arc::new(condition.clone()),
            BinOp::Implies,
            Arc::new(matching_upper_bound.clone()),
        );
        let guarded_other_loop_fact = PureExpr::BinOp(
            Arc::new(other_condition),
            BinOp::Implies,
            Arc::new(other_fact.clone()),
        );
        let base_requires = vec![PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        )];
        let invariants = vec![guarded_upper_bound.clone(), guarded_other_loop_fact.clone()];
        let obligations = vec![PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
            method: "in_bounds".to_string(),
            args: vec![PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(
                PureExpr::Var(
                    "v".to_string(),
                    Some(ExprSort::MutRef(Box::new(ExprSort::Seq))),
                ),
            ))))],
        }];
        let group = LoopObligationGroup {
            loop_index: Some(0),
            condition_unstated: None,
            pre_loop_stored_names: Default::default(),
            unstated_entry_values: Default::default(),
            injected_fail_closed: false,
            assumptions: Vec::new(),
            obligations,
            condition: Some(condition.clone()),
        };
        let ctx = LoopCallObligationContext {
            base_requires: &base_requires,
            pre_loop_assumptions: &[],
            per_loop_invariants: std::slice::from_ref(&invariants),
            pre_loop_obligations: &[],
            loop_obligation_groups: &[],
            logic_fns_opt: None,
            mode_overrides_opt: None,
            type_invariants_opt: None,
            type_constants_opt: None,
            adt_decls_opt: None,
            adt_field_ranges_opt: None,
            track_level: trust_wp_core::TrackLevel::Auto,
            timeout: None,
        };

        let requires = loop_group_obligation_requires(&ctx, &group);

        assert!(
            requires.contains(&guarded_upper_bound),
            "the guarded fact remains available as a loop assumption"
        );
        assert!(
            requires.contains(&matching_upper_bound),
            "the active loop VC should get the direct upper-bound fact"
        );
        assert!(
            requires.contains(&condition),
            "the loop condition is still threaded as an assumption"
        );
        assert!(
            !requires.contains(&other_fact),
            "facts guarded by another loop's condition must not become active assumptions"
        );
        assert!(
            requires.contains(&guarded_other_loop_fact),
            "non-matching guarded invariants should stay guarded"
        );
    }

    #[test]
    fn loop_group_preheader_assumptions_are_active_requires() {
        let condition = var("loop_active", Some(ExprSort::Bool));
        let preheader_fact = binop(var("m", None), BinOp::Eq, var("moves_at_i", None));
        let group = LoopObligationGroup {
            loop_index: Some(0),
            condition_unstated: None,
            pre_loop_stored_names: Default::default(),
            unstated_entry_values: Default::default(),
            injected_fail_closed: false,
            assumptions: vec![preheader_fact.clone()],
            obligations: vec![var("obligation", Some(ExprSort::Bool))],
            condition: Some(condition.clone()),
        };
        let ctx = LoopCallObligationContext {
            base_requires: &[],
            pre_loop_assumptions: &[],
            per_loop_invariants: &[],
            pre_loop_obligations: &[],
            loop_obligation_groups: &[],
            logic_fns_opt: None,
            mode_overrides_opt: None,
            type_invariants_opt: None,
            type_constants_opt: None,
            adt_decls_opt: None,
            adt_field_ranges_opt: None,
            track_level: trust_wp_core::TrackLevel::Auto,
            timeout: None,
        };

        let requires = loop_group_obligation_requires(&ctx, &group);

        assert!(
            requires.contains(&preheader_fact),
            "loop-call VCs must include postconditions from calls before the loop header"
        );
        assert!(requires.contains(&condition));
    }

    #[test]
    fn quantified_invariants_do_not_block_direct_in_bounds_loop_obligation() {
        let i = var("i", Some(ExprSort::Int));
        let j = var("j", Some(ExprSort::Int));
        let produced = var("produced", Some(ExprSort::Seq));
        let v = var(
            "v",
            Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(
                intern_sort_name("std::vec::Vec"),
            )))),
        );
        let v_view = PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(v))));
        let v_len = method_call(v_view.clone(), "len", vec![]);
        let condition = method_call(var("__iter_result_12", None), "discriminant", vec![]);
        let condition = binop(condition, BinOp::Eq, PureExpr::Int(1));

        let quantified_invariant = PureExpr::Forall {
            var: "j".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(binop(
                binop(
                    binop(PureExpr::Int(0), BinOp::Le, j.clone()),
                    BinOp::And,
                    binop(
                        j.clone(),
                        BinOp::Lt,
                        method_call(produced.clone(), "len", vec![]),
                    ),
                ),
                BinOp::Implies,
                binop(
                    method_call(produced, "index_logic", vec![j]),
                    BinOp::Eq,
                    PureExpr::Int(0),
                ),
            )),
            triggers: vec![],
        };
        let direct_lower = binop(i.clone(), BinOp::Ge, PureExpr::Int(0));
        let guarded_upper = binop(
            condition.clone(),
            BinOp::Implies,
            binop(i.clone(), BinOp::Lt, v_len),
        );
        let invariants = vec![quantified_invariant, direct_lower, guarded_upper];
        let obligations = vec![method_call(i, "in_bounds", vec![v_view])];
        let group = LoopObligationGroup {
            loop_index: Some(0),
            condition_unstated: None,
            pre_loop_stored_names: Default::default(),
            unstated_entry_values: Default::default(),
            injected_fail_closed: false,
            assumptions: Vec::new(),
            obligations,
            condition: Some(condition),
        };
        let ctx = LoopCallObligationContext {
            base_requires: &[],
            pre_loop_assumptions: &[],
            per_loop_invariants: std::slice::from_ref(&invariants),
            pre_loop_obligations: &[],
            loop_obligation_groups: std::slice::from_ref(&group),
            logic_fns_opt: None,
            mode_overrides_opt: None,
            type_invariants_opt: None,
            type_constants_opt: None,
            adt_decls_opt: None,
            adt_field_ranges_opt: None,
            track_level: trust_wp_core::TrackLevel::Auto,
            timeout: Some(Duration::from_secs(5)),
        };

        let result = super::verify_loop_call_obligations(&ctx)
            .expect("loop obligation verification should encode");

        assert!(
            matches!(result, trust_wp_ay::VerificationResult::Verified(_)),
            "direct in_bounds obligation should verify without entering the quantified invariant path, got {result:?}"
        );
    }

    #[test]
    fn guarded_call_postcondition_discharges_later_loop_obligation() {
        let active_call = var("available_result", Some(ExprSort::Bool));
        let board = var("board", None);
        let adj = var("adj", None);
        let in_bounds = method_call(board, "in_bounds", vec![adj]);
        let call_postcondition = binop(active_call.clone(), BinOp::Implies, in_bounds.clone());
        let guard = binop(
            binop(active_call, BinOp::Eq, PureExpr::Bool(true)),
            BinOp::And,
            call_postcondition,
        );
        let obligations = vec![binop(guard, BinOp::Implies, in_bounds)];

        let remaining = super::filter_directly_unproved_obligations(&[], &obligations);

        assert!(
            remaining.is_empty(),
            "active call result plus its postcondition should discharge the guarded follow-up obligation, got {remaining:?}"
        );
    }

    #[test]
    fn guarded_call_postcondition_requires_active_call_fact() {
        let active_call = var("available_result", Some(ExprSort::Bool));
        let board = var("board", None);
        let adj = var("adj", None);
        let in_bounds = method_call(board, "in_bounds", vec![adj]);
        let call_postcondition = binop(active_call, BinOp::Implies, in_bounds.clone());
        let obligations = vec![binop(call_postcondition, BinOp::Implies, in_bounds)];

        let remaining = super::filter_directly_unproved_obligations(&[], &obligations);

        assert_eq!(
            remaining, obligations,
            "a postcondition implication alone does not prove its consequent"
        );
    }

    #[test]
    fn direct_integer_bounds_discharge_weaker_loop_obligations() {
        let m0 = PureExpr::View(Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![var("m", None)],
        }));
        let requires = vec![
            binop(PureExpr::Int(-2), BinOp::Le, m0.clone()),
            binop(m0.clone(), BinOp::Le, PureExpr::Int(2)),
        ];
        let obligations = vec![
            binop(PureExpr::Int(-10000), BinOp::Le, m0.clone()),
            binop(m0, BinOp::Le, PureExpr::Int(10000)),
        ];

        let remaining = super::filter_directly_unproved_obligations(&requires, &obligations);

        assert!(
            remaining.is_empty(),
            "trusted moves() yielded bounds should discharge weaker Point::mov bounds, got {remaining:?}"
        );
    }

    #[test]
    fn type_invariant_len_fact_discharges_positive_scaled_new_size_obligation() {
        let self_var = var("self", None);
        let receiver = PureExpr::Deref(Arc::new(self_var.clone()));
        let call_len = PureExpr::View(Arc::new(var("_call_7", Some(ExprSort::Int))));
        let concrete_len = buckets_len(receiver.clone());
        let invariant_method = type_invariant_method_name("MyHashMap");
        let invariant_def = TypeInvariantDef::new(
            "MyHashMap".to_string(),
            "self".to_string(),
            binop(PureExpr::Int(0), BinOp::Lt, buckets_len(var("self", None))),
        );
        let requires = vec![
            method_call(receiver, &invariant_method, vec![]),
            binop(call_len, BinOp::Eq, concrete_len),
        ];
        let obligation = binop(
            PureExpr::Int(0),
            BinOp::Lt,
            PureExpr::View(Arc::new(binop(
                var("_call_7", Some(ExprSort::Int)),
                BinOp::Mul,
                PureExpr::Int(2),
            ))),
        );
        let obligations = vec![obligation];
        let ctx = LoopCallObligationContext {
            base_requires: &[],
            pre_loop_assumptions: &[],
            per_loop_invariants: &[],
            pre_loop_obligations: &[],
            loop_obligation_groups: &[],
            logic_fns_opt: None,
            mode_overrides_opt: None,
            type_invariants_opt: Some(std::slice::from_ref(&invariant_def)),
            type_constants_opt: None,
            adt_decls_opt: None,
            adt_field_ranges_opt: None,
            track_level: trust_wp_core::TrackLevel::Auto,
            timeout: Some(Duration::from_secs(5)),
        };

        let remaining =
            super::filter_directly_unproved_obligations_with_ctx(&ctx, &requires, &obligations);

        assert!(
            remaining.is_empty(),
            "active type invariant len>0 and len alias should discharge positive scaled constructor size, got {remaining:?}"
        );
    }

    #[test]
    fn guarded_integer_bounds_discharge_weaker_guarded_loop_obligations() {
        let active = binop(
            method_call(var("call_41", None), "discriminant", vec![]),
            BinOp::Eq,
            PureExpr::Int(1),
        );
        let m0 = PureExpr::View(Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![var("m", None)],
        }));
        let tight_bounds = binop(
            binop(PureExpr::Int(-2), BinOp::Le, m0.clone()),
            BinOp::And,
            binop(m0.clone(), BinOp::Le, PureExpr::Int(2)),
        );
        let requires = vec![
            active.clone(),
            binop(active.clone(), BinOp::Implies, tight_bounds),
        ];
        let obligations = vec![binop(
            active,
            BinOp::Implies,
            binop(
                binop(PureExpr::Int(-10000), BinOp::Le, m0.clone()),
                BinOp::And,
                binop(m0, BinOp::Le, PureExpr::Int(10000)),
            ),
        )];

        let remaining = super::filter_directly_unproved_obligations(&requires, &obligations);

        assert!(
            remaining.is_empty(),
            "active yielded bounds should discharge weaker guarded Point::mov bounds, got {remaining:?}"
        );
    }

    #[test]
    fn direct_integer_bounds_keep_stronger_loop_obligations() {
        let m0 = PureExpr::View(Arc::new(PureExpr::LogicFnCall {
            name: "__trust_wp_tuple_get_0".to_string(),
            args: vec![var("m", None)],
        }));
        let requires = vec![
            binop(PureExpr::Int(-2), BinOp::Le, m0.clone()),
            binop(m0.clone(), BinOp::Le, PureExpr::Int(2)),
        ];
        let obligations = vec![
            binop(PureExpr::Int(0), BinOp::Le, m0.clone()),
            binop(m0, BinOp::Le, PureExpr::Int(1)),
        ];

        let remaining = super::filter_directly_unproved_obligations(&requires, &obligations);

        assert_eq!(
            remaining, obligations,
            "bounds stronger than the active yielded facts still need solver checking"
        );
    }

    #[test]
    fn pre_loop_assumptions_discharge_pre_loop_obligations() {
        let fact = binop(var("x", None), BinOp::Gt, PureExpr::Int(0));
        let ctx = LoopCallObligationContext {
            base_requires: &[],
            pre_loop_assumptions: std::slice::from_ref(&fact),
            per_loop_invariants: &[],
            pre_loop_obligations: std::slice::from_ref(&fact),
            loop_obligation_groups: &[],
            logic_fns_opt: None,
            mode_overrides_opt: None,
            type_invariants_opt: None,
            type_constants_opt: None,
            adt_decls_opt: None,
            adt_field_ranges_opt: None,
            track_level: trust_wp_core::TrackLevel::Auto,
            timeout: Some(Duration::from_secs(5)),
        };

        let result = super::verify_loop_call_obligations(&ctx)
            .expect("pre-loop assumption obligation should encode");

        assert!(
            matches!(result, trust_wp_ay::VerificationResult::Verified(_)),
            "pre-loop assumptions should prove pre-loop obligations, got {result:?}"
        );
    }

    #[test]
    fn pre_loop_assumptions_do_not_leak_to_loop_groups() {
        let fact = binop(var("x", None), BinOp::Gt, PureExpr::Int(0));
        let group = LoopObligationGroup {
            loop_index: Some(0),
            condition_unstated: None,
            pre_loop_stored_names: Default::default(),
            unstated_entry_values: Default::default(),
            injected_fail_closed: false,
            assumptions: Vec::new(),
            obligations: vec![fact.clone()],
            condition: None,
        };
        let ctx = LoopCallObligationContext {
            base_requires: &[],
            pre_loop_assumptions: std::slice::from_ref(&fact),
            per_loop_invariants: &[],
            pre_loop_obligations: &[],
            loop_obligation_groups: std::slice::from_ref(&group),
            logic_fns_opt: None,
            mode_overrides_opt: None,
            type_invariants_opt: None,
            type_constants_opt: None,
            adt_decls_opt: None,
            adt_field_ranges_opt: None,
            track_level: trust_wp_core::TrackLevel::Auto,
            timeout: Some(Duration::from_secs(5)),
        };

        let result =
            super::verify_loop_call_obligations(&ctx).expect("loop-group obligation should encode");

        assert!(
            matches!(result, trust_wp_ay::VerificationResult::Failed(_)),
            "pre-loop assumptions must not prove in-loop obligations, got {result:?}"
        );
    }

    /// A group whose condition reads a value no premise states has models
    /// that pick it freely: its refutation is withheld, its proof is not.
    #[test]
    fn a_group_over_an_unstated_condition_withholds_its_refutation() {
        let obligation = binop(var("x", None), BinOp::Gt, PureExpr::Int(0));
        let group = |obligations: Vec<PureExpr>| LoopObligationGroup {
            loop_index: Some(0),
            condition_unstated: Some("the behaviour of `f`, which has no contract".to_string()),
            pre_loop_stored_names: Default::default(),
            unstated_entry_values: Default::default(),
            injected_fail_closed: false,
            assumptions: Vec::new(),
            obligations,
            condition: Some(var("$iter_result_3", Some(ExprSort::Bool))),
        };
        let run = |group: &LoopObligationGroup| {
            let ctx = LoopCallObligationContext {
                base_requires: &[],
                pre_loop_assumptions: &[],
                per_loop_invariants: &[],
                pre_loop_obligations: &[],
                loop_obligation_groups: std::slice::from_ref(group),
                logic_fns_opt: None,
                mode_overrides_opt: None,
                type_invariants_opt: None,
                type_constants_opt: None,
                adt_decls_opt: None,
                adt_field_ranges_opt: None,
                track_level: trust_wp_core::TrackLevel::Auto,
                timeout: Some(Duration::from_secs(5)),
            };
            super::verify_loop_call_obligations(&ctx).expect("loop-group obligation should encode")
        };

        let refuted = run(&group(vec![obligation]));
        assert!(
            trust_wp_ay::is_withheld_refutation(&refuted),
            "a refutation over an unstated condition is withheld, got {refuted:?}"
        );
        let proved = run(&group(vec![PureExpr::Bool(true)]));
        assert!(
            matches!(proved, trust_wp_ay::VerificationResult::Verified(_)),
            "withholding never touches a proof, got {proved:?}"
        );
    }

    /// A group whose obligation reads a name a store before the loop changed,
    /// under a precondition about its entry value, withholds its refutation;
    /// one whose obligation reads no such name keeps it
    /// (loop_call_obligation_after_param_store_{control,false}).
    #[test]
    fn a_group_over_a_stale_entry_value_withholds_its_refutation() {
        let entry_fact = binop(var("a", None), BinOp::Eq, PureExpr::Int(0));
        let reads_a = binop(var("a", None), BinOp::Eq, PureExpr::Int(7));
        let reads_i = binop(var("i", None), BinOp::Gt, PureExpr::Int(5));
        let run = |obligation: &PureExpr| {
            let group = LoopObligationGroup {
                loop_index: Some(0),
                condition_unstated: None,
                pre_loop_stored_names: std::collections::HashSet::from(["a".to_string()]),
                unstated_entry_values: Default::default(),
                injected_fail_closed: false,
                assumptions: Vec::new(),
                obligations: vec![obligation.clone()],
                condition: None,
            };
            let ctx = LoopCallObligationContext {
                base_requires: std::slice::from_ref(&entry_fact),
                pre_loop_assumptions: &[],
                per_loop_invariants: &[],
                pre_loop_obligations: &[],
                loop_obligation_groups: std::slice::from_ref(&group),
                logic_fns_opt: None,
                mode_overrides_opt: None,
                type_invariants_opt: None,
                type_constants_opt: None,
                adt_decls_opt: None,
                adt_field_ranges_opt: None,
                track_level: trust_wp_core::TrackLevel::Auto,
                timeout: Some(Duration::from_secs(5)),
            };
            super::verify_loop_call_obligations(&ctx).expect("loop-group obligation should encode")
        };

        let stale = run(&reads_a);
        assert!(
            trust_wp_ay::is_withheld_refutation(&stale),
            "a refutation over a stale entry value is withheld, got {stale:?}"
        );
        let independent = run(&reads_i);
        assert!(
            matches!(independent, trust_wp_ay::VerificationResult::Failed(_)),
            "a refutation no premise links to the store stands, got {independent:?}"
        );
    }

    /// A group whose obligation reads a havoc the arithmetic walk bound for a
    /// local no loop writes withholds its refutation: the model picks the
    /// value code before the loop fixed. An obligation over the loop counter
    /// alone keeps its refutation (loop_overflow_after_param_store_control,
    /// loop_overflow_loop_written_local_false).
    #[test]
    fn a_group_over_an_unstated_entry_value_withholds_its_refutation() {
        let havoc = "__trust_wp_arith_havoc_1_8";
        let no_overflow = binop(
            binop(var(havoc, None), BinOp::Add, PureExpr::Int(1)),
            BinOp::Le,
            PureExpr::Int(4_294_967_295),
        );
        let reads_i = binop(var("i", None), BinOp::Gt, PureExpr::Int(5));
        let run = |obligation: &PureExpr, unstated: &[&str]| {
            let group = LoopObligationGroup {
                loop_index: Some(0),
                condition_unstated: None,
                pre_loop_stored_names: Default::default(),
                unstated_entry_values: unstated.iter().map(|name| name.to_string()).collect(),
                injected_fail_closed: false,
                assumptions: Vec::new(),
                obligations: vec![obligation.clone()],
                condition: None,
            };
            let ctx = LoopCallObligationContext {
                base_requires: &[],
                pre_loop_assumptions: &[],
                per_loop_invariants: &[],
                pre_loop_obligations: &[],
                loop_obligation_groups: std::slice::from_ref(&group),
                logic_fns_opt: None,
                mode_overrides_opt: None,
                type_invariants_opt: None,
                type_constants_opt: None,
                adt_decls_opt: None,
                adt_field_ranges_opt: None,
                track_level: trust_wp_core::TrackLevel::Auto,
                timeout: Some(Duration::from_secs(5)),
            };
            super::verify_loop_call_obligations(&ctx).expect("loop-group obligation should encode")
        };

        let unstated = run(&no_overflow, &[havoc]);
        assert!(
            trust_wp_ay::is_withheld_refutation(&unstated),
            "a refutation over a value the VC leaves free is withheld, got {unstated:?}"
        );
        let loop_written = run(&no_overflow, &[]);
        assert!(
            matches!(loop_written, trust_wp_ay::VerificationResult::Failed(_)),
            "a havoc for a loop-written local keeps its refutation, got {loop_written:?}"
        );
        let independent = run(&reads_i, &[havoc]);
        assert!(
            matches!(independent, trust_wp_ay::VerificationResult::Failed(_)),
            "a refutation that reads no such havoc stands, got {independent:?}"
        );
    }

    /// A marker the loop body walk injected under its path (`i < 3 ⇒ false`)
    /// is refuted by every model that reaches it, so its refutation is
    /// withheld whether the group says it holds one or the verdict gate reads
    /// the guarded `false` itself (D-141). A goal that is no marker keeps its
    /// refutation.
    #[test]
    fn a_group_holding_a_guarded_marker_withholds_its_refutation() {
        let marker = binop(
            binop(var("i", None), BinOp::Lt, PureExpr::Int(3)),
            BinOp::Implies,
            PureExpr::Bool(false),
        );
        let run = |injected_fail_closed: bool, goal: &PureExpr| {
            let group = LoopObligationGroup {
                loop_index: Some(0),
                condition_unstated: None,
                pre_loop_stored_names: Default::default(),
                unstated_entry_values: Default::default(),
                injected_fail_closed,
                assumptions: Vec::new(),
                obligations: vec![goal.clone()],
                condition: None,
            };
            let ctx = LoopCallObligationContext {
                base_requires: &[],
                pre_loop_assumptions: &[],
                per_loop_invariants: &[],
                pre_loop_obligations: &[],
                loop_obligation_groups: std::slice::from_ref(&group),
                logic_fns_opt: None,
                mode_overrides_opt: None,
                type_invariants_opt: None,
                type_constants_opt: None,
                adt_decls_opt: None,
                adt_field_ranges_opt: None,
                track_level: trust_wp_core::TrackLevel::Auto,
                timeout: Some(Duration::from_secs(5)),
            };
            super::verify_loop_call_obligations(&ctx).expect("loop-group obligation should encode")
        };
        for injected in [true, false] {
            let outcome = run(injected, &marker);
            assert!(
                trust_wp_ay::is_withheld_refutation(&outcome),
                "a refutation of a guarded marker is withheld (flag {injected}), got {outcome:?}"
            );
        }
        let goal = binop(var("i", None), BinOp::Lt, PureExpr::Int(3));
        let refuted = run(false, &goal);
        assert!(
            matches!(refuted, trust_wp_ay::VerificationResult::Failed(_)),
            "a goal that is no marker keeps its refutation, got {refuted:?}"
        );
    }
}
