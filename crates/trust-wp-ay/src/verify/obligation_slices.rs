// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Obligation slicing for per-postcondition verification.
//!
//! Instead of checking all postconditions in a single monolithic solver query,
//! obligation slicing verifies each `ensures` clause independently against the
//! shared precondition/body context. This decouples unrelated obligations so
//! that a quantifier-heavy ensure cannot make a sibling pure ensure harder to
//! prove.
//!
//! # Architecture
//!
//! The shared setup (preconditions, body constraints, axioms) is asserted once
//! into a base solver scope. For each obligation slice, the solver's incremental
//! push/pop mechanism creates an isolated scope where only the negated
//! postcondition for that slice is asserted. Results are aggregated with
//! precedence: `Failed` > `Unknown` > `Verified`.
//!
//! See `designs/2026-02-17-994-alternative.md` for the full design rationale.
//!
//! # Push/Pop Safety (ay#3664, trust-vc#1529)
//!
//! ay-dpll historically had an underspecified push/pop contract, causing theory
//! solver state leaks between scopes (ay#3664). This has been fixed: the
//! `TheorySolver` trait now has a formal push/pop restoration contract
//! (`ay-core/src/theory.rs:329-466`) and all theory implementations comply.
//!
//! Obligation slicing's push/pop usage is safe because:
//! 1. Each scope is short-lived: push, encode one postcondition, check_sat, pop.
//! 2. No solver state from one slice leaks to the next (ay contract guarantees).
//! 3. The base context (preconditions, body, axioms) is established before any
//!    push and is never modified between slices.
//! 4. This is the canonical use case for incremental solving.
//!
//! The alternative (fresh encoder per slice) would re-encode preconditions, body
//! constraints, sort hints, and axioms N times for N postconditions. The loop
//! verification module uses fresh encoders for a different reason: timeout
//! isolation between proof phases, where each phase has independent expressions.

use std::{borrow::Cow, sync::Arc};

use trust_wp_core::formula::{BinOp, PureExpr};

use super::{
    function::axiom_detection::expr_contains_embedded_existential, Counterexample,
    ProofCertificateSummary, UnknownReason, VerificationOutcome, VerificationResult,
};
use crate::shared_types::ProofAssertSliceDerivation;

/// A single obligation to verify: one `ensures` clause with its index.
#[derive(Debug, Clone)]
pub(crate) struct ObligationSlice<'a> {
    /// The postcondition expression to verify.
    pub ensure: Cow<'a, PureExpr>,
    /// Index into the original `ensures` slice (for error reporting).
    pub index: usize,
}

/// Split an ensures slice into individual obligation slices.
///
/// Each ensure becomes one or more independent verification obligations.
/// Top-level conjunctions are flattened so a single `a && b` ensure is
/// verified as two slices with the same source index. When `ensures` is
/// empty, returns an empty vec (caller should return `Verified` early).
pub(crate) fn split_ensures(ensures: &[PureExpr]) -> Vec<ObligationSlice<'_>> {
    let mut slices = Vec::new();
    for (index, ensure) in ensures.iter().enumerate() {
        collect_top_level_conjunct_slices(ensure, index, &mut slices);
    }
    slices
}

/// Stable PreparedAssertion-side claim text for every independently verified
/// proof-assert obligation slice.
#[must_use]
pub fn proof_assert_obligation_slice_claims(ensures: &[PureExpr]) -> Vec<String> {
    split_ensures(ensures)
        .into_iter()
        .map(|slice| format!("{:#?}", slice.ensure.as_ref()))
        .collect()
}

/// Recover the only structural derivations accepted at the `proof_assert`
/// authority boundary from the original prepared assertion.
///
/// This intentionally performs exact AST comparisons. It does not simplify,
/// normalize, consult ghost context, or apply semantic equivalence rules. That
/// makes the classification independently reproducible by the reporting
/// process before it accepts a certificate whose native artifact proves the
/// small Boolean derivation kernel instead of the encoded user claim.
#[must_use]
pub fn proof_assert_obligation_slice_derivations(
    ensures: &[PureExpr],
    preconditions: &[PureExpr],
) -> Vec<ProofAssertSliceDerivation> {
    split_ensures(ensures)
        .into_iter()
        .map(|slice| {
            let ensure = slice.ensure.as_ref();
            if matches!(ensure, PureExpr::Bool(true)) {
                ProofAssertSliceDerivation::SyntacticTruth
            } else if preconditions.iter().any(|premise| premise == ensure) {
                ProofAssertSliceDerivation::ExactPreparedPremise
            } else {
                ProofAssertSliceDerivation::NativeEncoded
            }
        })
        .collect()
}

/// Number of independently verified proof-assert obligation slices.
#[must_use]
pub fn proof_assert_obligation_slice_count(ensures: &[PureExpr]) -> usize {
    split_ensures(ensures).len()
}

fn collect_top_level_conjunct_slices<'a>(
    ensure: &'a PureExpr,
    index: usize,
    slices: &mut Vec<ObligationSlice<'a>>,
) {
    // Keep conjunctions containing existentials intact so the downstream
    // negation pipeline still sees embedded existential context and can apply
    // body-witness instantiation before solving. Flattening `a && exists y. P`
    // into a standalone top-level existential slice would bypass that rewrite
    // and regress to quantifier-driven Unknown(Incomplete). (#2141, #2517)
    if expr_contains_embedded_existential(ensure) {
        slices.push(ObligationSlice {
            ensure: Cow::Borrowed(ensure),
            index,
        });
        return;
    }

    if let Some(parts) = split_expr_owned(ensure) {
        for part in parts {
            slices.push(ObligationSlice {
                ensure: Cow::Owned(part),
                index,
            });
        }
    } else {
        slices.push(ObligationSlice {
            ensure: Cow::Borrowed(ensure),
            index,
        });
    }
}

fn split_expr_owned(expr: &PureExpr) -> Option<Vec<PureExpr>> {
    match expr {
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            let mut parts = Vec::new();
            extend_split_or_self(lhs, &mut parts);
            extend_split_or_self(rhs, &mut parts);
            (parts.len() > 1).then_some(parts)
        }
        PureExpr::BinOp(guard, BinOp::Implies, consequent) => {
            let parts = split_expr_owned(consequent)?;
            (parts.len() > 1).then(|| {
                parts
                    .into_iter()
                    .map(|part| PureExpr::BinOp(guard.clone(), BinOp::Implies, Arc::new(part)))
                    .collect()
            })
        }
        PureExpr::Let { var, value, body } => {
            let parts = split_expr_owned(body)?;
            (parts.len() > 1).then(|| {
                parts
                    .into_iter()
                    .map(|part| PureExpr::Let {
                        var: var.clone(),
                        value: value.clone(),
                        body: Arc::new(part),
                    })
                    .collect()
            })
        }
        PureExpr::LetAssume { assumption, body } => {
            let parts = split_expr_owned(body)?;
            (parts.len() > 1).then(|| {
                parts
                    .into_iter()
                    .map(|part| PureExpr::LetAssume {
                        assumption: assumption.clone(),
                        body: Arc::new(part),
                    })
                    .collect()
            })
        }
        PureExpr::LetObligation { obligation, body } => {
            let parts = split_expr_owned(body)?;
            (parts.len() > 1).then(|| {
                parts
                    .into_iter()
                    .map(|part| PureExpr::LetObligation {
                        obligation: obligation.clone(),
                        body: Arc::new(part),
                    })
                    .collect()
            })
        }
        _ => None,
    }
}

fn extend_split_or_self(expr: &PureExpr, parts: &mut Vec<PureExpr>) {
    if let Some(split) = split_expr_owned(expr) {
        parts.extend(split);
    } else {
        parts.push(expr.clone());
    }
}

/// Result of verifying a single obligation slice.
#[derive(Debug)]
pub(crate) struct SliceResult {
    /// Index of the ensure clause this result corresponds to.
    pub index: usize,
    /// Verification outcome for this slice.
    pub result: VerificationResult,
}

/// Result of verifying a single obligation slice with provenance.
#[derive(Debug)]
pub(crate) struct SliceOutcome {
    /// Index of the ensure clause this result corresponds to.
    pub index: usize,
    /// Verification outcome for this slice.
    pub outcome: VerificationOutcome,
}

/// Aggregate per-slice results into a single [`VerificationResult`].
///
/// Precedence: `Failed` > `Unknown` > `Assumed` > `Verified`.
///
/// - If any slice failed, the overall result is `Failed` (with the first
///   counterexample found).
/// - If no slice failed but any is `Unknown`, the overall result is `Unknown`.
/// - If no failures or unknowns but any is `Assumed`, the overall result is
///   `Assumed` (preserving the assumption reason). This prevents silent
///   promotion of axiom-assumed obligations to verified status (#1889).
/// - If all slices verified, their strict certificate summaries are combined;
///   a missing summary remains `Verified(None)` so the mandatory public
///   authority boundary will reject it.
///
/// When `results` is empty, returns `Verified(None)`; callers that want proof
/// authority must discharge the empty conjunction through the checked trivial
/// proof lane.
///
/// # The deciding slice, and why reporting it here does not work
///
/// 760fac2 named a follow-up: attribute a multi-slice obligation's diagnostic
/// strict-replay measurement to the slice that decided its verdict, which
/// "needs the deciding slice index out of `aggregate_slice_results`". Both parts
/// were built and measured. Recording the outcome so it is not attempted a
/// third time:
///
/// * The deciding slice IS well-defined, for `Failed`, `Unknown` and `Assumed`:
///   each returns one slice's payload verbatim (`first_failed`'s counterexample,
///   `first_unknown`'s reason, `first_assumed`'s reason), and the `_idx` those
///   arms already discard identifies it. It is NOT well-defined for a `Verified`
///   aggregate over two or more slices, whose summary is the conjunction of every
///   verified slice's summary via [`combine_proof_summaries`] — no single replay
///   measured that, and one accepted conjunct is not a certificate for the
///   conjunction.
/// * ★ The index to thread out is the POSITION, never [`SliceResult::index`].
///   [`split_ensures`] gives every top-level conjunct of one `ensures` clause the
///   SAME source index, so `a && b` yields two independent slices both reporting
///   `index = 0`. Keying a per-slice measurement by that number re-fuses the two
///   conjuncts and lets one answer for the other — 760fac2's defect rebuilt on a
///   different key.
/// * It recovers nothing anyway. The observation is bound on
///   (obligation, slice, SOLVE) and a later `check_sat` on the same slice — the
///   base/vacuity recheck — unbinds it before the slice ends, so no measurement
///   survives to the slice boundary for the aggregate to attribute. Measured:
///   `vector/09_capacity::change_capacity` and `closures/13_ref_box::test7` each
///   produced two such refusals and still reported `strict_replay=none`. See
///   `solve_details_tests::test_a_later_solve_on_the_same_slice_already_unbinds_the_observation`.
///
/// The blocker is the `solve` component, not slice attribution. Relaxing it is a
/// scope loosening, which is the regression the binding exists to prevent.
pub(crate) fn aggregate_slice_results(results: Vec<SliceResult>) -> VerificationResult {
    let mut first_failed: Option<(usize, Counterexample)> = None;
    let mut first_unknown: Option<(usize, UnknownReason)> = None;
    let mut first_assumed: Option<(usize, String)> = None;
    let mut verified_summary: Option<ProofCertificateSummary> = None;
    let mut verified_missing_summary = false;
    let mut verified_count = 0usize;

    for sr in results {
        match sr.result {
            VerificationResult::Failed(ce) => {
                if first_failed.is_none() {
                    first_failed = Some((sr.index, ce));
                }
            }
            VerificationResult::Unknown(reason) => {
                if first_failed.is_none() && first_unknown.is_none() {
                    first_unknown = Some((sr.index, reason));
                }
            }
            VerificationResult::Assumed(reason) => {
                if first_assumed.is_none() {
                    first_assumed = Some((sr.index, reason));
                }
            }
            VerificationResult::Verified(summary) => {
                verified_count += 1;
                match summary {
                    Some(summary) => {
                        verified_summary = Some(match verified_summary {
                            Some(acc) => combine_proof_summaries(acc, summary),
                            None => summary,
                        });
                    }
                    None => verified_missing_summary = true,
                }
            }
        }
    }

    if let Some((_idx, ce)) = first_failed {
        VerificationResult::Failed(ce)
    } else if let Some((_idx, reason)) = first_unknown {
        VerificationResult::Unknown(reason)
    } else if let Some((_idx, reason)) = first_assumed {
        // Propagate Assumed instead of silently promoting to Verified (#1889).
        // If any obligation was assumed rather than proven, the aggregate
        // result must reflect that — callers need to count these separately.
        VerificationResult::Assumed(reason)
    } else if verified_count == 0 || verified_missing_summary {
        VerificationResult::Verified(None)
    } else {
        VerificationResult::Verified(verified_summary)
    }
}

/// Combine metadata for independently strict-checked conjunct proofs.
///
/// This is not a new proof step: each input summary already authenticates one
/// slice, and the aggregate represents their conjunction. A multi-slice Alethe
/// text would not be a valid single proof (step identifiers may overlap), so
/// only a one-slice aggregate retains the rendered text.
///
/// The combination is deliberately conservative in the refusing direction:
/// `strict_verified`/`lrat_present` are ANDed and every trust/hole/fallback
/// count is SUMMED, so the conjunction is fully verified only when every
/// conjunct was. It can never launder a weaker conjunct into a stronger
/// aggregate. Shared with the loop-phase aggregation in
/// [`crate::verify::types::LoopVerificationResult::overall`], whose phases are
/// conjuncts in exactly the same sense.
pub(crate) fn combine_proof_summaries(
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
        alethe_text: None,
    }
}

/// Aggregate per-slice outcomes, preserving provenance from the winning slice.
///
/// Precedence matches [`aggregate_slice_results`]: `Failed` > `Unknown` >
/// `Assumed` > `Verified`. Among verified slices, a missing/rejected solver
/// proof or certificate summary is not hidden by a sibling with accepted proof
/// evidence. Fully checked summaries are combined conjunctively.
pub(crate) fn aggregate_slice_outcomes(results: Vec<SliceOutcome>) -> VerificationOutcome {
    let mut first_failed: Option<(usize, VerificationOutcome)> = None;
    let mut first_unknown: Option<(usize, VerificationOutcome)> = None;
    let mut first_assumed: Option<(usize, VerificationOutcome)> = None;
    let mut first_verified_gap: Option<(usize, VerificationOutcome)> = None;
    let mut first_verified_with_evidence: Option<(usize, VerificationOutcome)> = None;
    let mut verified_summary: Option<ProofCertificateSummary> = None;

    for sr in results {
        let rank = match &sr.outcome.result {
            VerificationResult::Failed(_) => 0,
            VerificationResult::Unknown(_) => 1,
            VerificationResult::Assumed(_) => 2,
            VerificationResult::Verified(_) => 3,
        };
        match rank {
            0 => {
                if first_failed.is_none() {
                    first_failed = Some((sr.index, sr.outcome));
                }
            }
            1 => {
                if first_failed.is_none() && first_unknown.is_none() {
                    first_unknown = Some((sr.index, sr.outcome));
                }
            }
            2 => {
                if first_assumed.is_none() {
                    first_assumed = Some((sr.index, sr.outcome));
                }
            }
            3 => {
                if verified_outcome_has_accepted_unsat_evidence(&sr.outcome) {
                    let summary = match &sr.outcome.result {
                        VerificationResult::Verified(Some(summary)) => summary.clone(),
                        _ => unreachable!("accepted verified evidence requires a summary"),
                    };
                    verified_summary = Some(match verified_summary {
                        Some(acc) => combine_proof_summaries(acc, summary),
                        None => summary,
                    });
                    if first_verified_with_evidence.is_none() {
                        first_verified_with_evidence = Some((sr.index, sr.outcome));
                    }
                } else if first_verified_gap.is_none() {
                    first_verified_gap = Some((sr.index, sr.outcome));
                }
            }
            _ => unreachable!(),
        }
    }

    if let Some((_idx, outcome)) = first_failed {
        outcome
    } else if let Some((_idx, outcome)) = first_unknown {
        outcome
    } else if let Some((_idx, outcome)) = first_assumed {
        outcome
    } else if let Some((_idx, mut outcome)) = first_verified_gap {
        outcome.result = VerificationResult::Verified(None);
        outcome
    } else if let Some((_idx, mut outcome)) = first_verified_with_evidence {
        outcome.result = VerificationResult::Verified(verified_summary);
        outcome
    } else {
        VerificationOutcome::without_provenance(VerificationResult::Verified(None))
    }
}

fn verified_outcome_has_accepted_unsat_evidence(outcome: &VerificationOutcome) -> bool {
    if !matches!(
        &outcome.result,
        VerificationResult::Verified(Some(summary)) if summary.is_fully_verified()
    ) {
        return false;
    }

    outcome
        .provenance
        .as_ref()
        .and_then(|provenance| provenance.solve_evidence.as_ref())
        .is_some_and(|evidence| {
            evidence.accepted_for_consumer && solve_evidence_result_is_unsat(&evidence.result)
        })
}

fn solve_evidence_result_is_unsat(result: &str) -> bool {
    result.eq_ignore_ascii_case("unsat")
        || result
            .strip_prefix("Unsat")
            .is_some_and(|suffix| suffix.is_empty() || suffix.starts_with('('))
}

#[cfg(test)]
mod tests;
