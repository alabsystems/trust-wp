// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::{self, Write},
    sync::Arc,
};

use sha2::{Digest, Sha256};

use super::{
    native_predicate_for_obligation, BundleClaimFormat, BundleDigest, BundleEvidenceMetadata,
    BundleNativeToolIdentity, BundleObligation, BundleObligationKind, BundleObligationResult,
    BundleObligationStatus, BundleResultMetadata, BundleSolverMetadata, BundleSummaryFact,
    BundleSummaryFactKind, EvidenceArtifact, EvidenceArtifactKind, NativeBundlePredicate,
    NativeClaimFormat, ProofEvidence, ProofEvidenceFormat, ProofStrength, VerifyBundleRequest,
    VerifyBundleResult, VerifyBundleStatus, PROOF_EVIDENCE_SCHEMA_VERSION,
    TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION, TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION,
    VERIFY_BUNDLE_API_VERSION,
};
use crate::{
    contract_parser::parse_contract,
    formula::{
        elaborate::{dereferenced, elaborate, sort_of, Dereference},
        BinOp, CaptureAvoidingSubstOptions, ExprSort, PureExpr, UnOp,
    },
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct NativePureProof {
    normalized_predicate: String,
    steps: Vec<NativeReplayStep>,
}

impl NativePureProof {
    fn replay_step_count(&self) -> usize {
        self.steps.len()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum NativeReplayStep {
    DecodeClaimFormat(NativeClaimFormat),
    Normalize(String),
    ApplyRule(&'static str),
    Verified,
}

impl NativeReplayStep {
    fn as_wire_line(&self) -> String {
        match self {
            Self::DecodeClaimFormat(format) => format!("decode:{}", format.as_str()),
            Self::Normalize(predicate) => format!("normalize:{predicate}"),
            Self::ApplyRule(rule) => format!("replay-rule:{rule}"),
            Self::Verified => "result:verified".to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum NativePureProofOutcome {
    Verified(NativePureProof),
    Failed(String),
    Unsupported(String),
}

/// Native proof replay failure with stable code and human-readable context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofReplayError {
    pub code: String,
    pub message: String,
}

impl ProofReplayError {
    fn new(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            code: code.into(),
            message: message.into(),
        }
    }
}

impl fmt::Display for ProofReplayError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.code, self.message)
    }
}

impl std::error::Error for ProofReplayError {}

pub(super) fn prove_native_pure_predicate(
    predicate: &PureExpr,
    claim_format: NativeClaimFormat,
    summary_facts: &[BundleSummaryFact],
) -> NativePureProofOutcome {
    // The rules below read each name at the sort the elaboration writes on
    // it, so a claim reading one name at two sorts would be proved of two
    // names: `(0 < 1 ==> b + 1 > b) && ((b : bool) || true)`. Replay refuses
    // what the claim decoder refuses, by the same elaboration.
    let elaboration = elaborate(predicate);
    if let Some((name, first, second)) = elaboration.conflict {
        return NativePureProofOutcome::Unsupported(format!(
            "native pure replay cannot prove or refute predicate: it reads `{name}` at both \
             {first} and {second}"
        ));
    }
    let normalized_predicate = predicate.to_string();
    // The decoder bound each fact to the binders the claim opens with as
    // written (`summary_fact_names`), before alias resolution moved any.
    let predicate = elaboration.typed;
    let context = NativeReplayContext { summary_facts };
    // Case splitting decides VALIDITY of the complete goal. A counterexample
    // must never be fed back as the truth value of a subexpression: doing that
    // to `p` inside `p ==> false` would prove the implication.
    let truth = match prove_bool(&predicate, &context) {
        unknown @ TruthValue::Unknown { .. } => match boolean_validity(&predicate) {
            Some(true) => TruthValue::True {
                rule: "boolean-case-split",
            },
            Some(false) => {
                return NativePureProofOutcome::Failed(
                    "typed Boolean goal has a counterexample under exhaustive case splitting"
                        .into(),
                )
            }
            None => match mixed_boolean_integer_validity(&predicate, &context) {
                Some(true) => TruthValue::True {
                    rule: "boolean-integer-case-split",
                },
                Some(false) => {
                    return NativePureProofOutcome::Failed(
                        "typed scalar goal has a counterexample under exhaustive Boolean case splitting"
                            .into(),
                    )
                }
                None => unknown,
            },
        },
        truth => truth,
    };
    match truth {
        TruthValue::True { rule } => NativePureProofOutcome::Verified(NativePureProof {
            steps: vec![
                NativeReplayStep::DecodeClaimFormat(claim_format),
                NativeReplayStep::Normalize(normalized_predicate.clone()),
                NativeReplayStep::ApplyRule(rule),
                NativeReplayStep::Verified,
            ],
            normalized_predicate,
        }),
        TruthValue::False { rule } => NativePureProofOutcome::Failed(format!(
            "typed predicate is false by native pure replay rule `{rule}`"
        )),
        TruthValue::Unknown { reason } => {
            if let Some(assignment) = checked_scalar_counterexample(&predicate, &context) {
                NativePureProofOutcome::Failed(format!(
                    "typed scalar goal has a checked whole-predicate counterexample: {assignment}"
                ))
            } else {
                NativePureProofOutcome::Unsupported(format!(
                    "native pure replay cannot prove or refute predicate: {reason}"
                ))
            }
        }
    }
}

/// A bounded decision procedure for the explicitly typed Boolean fragment.
/// Every valuation is checked; no solver verdict or external assumption enters.
fn boolean_validity(predicate: &PureExpr) -> Option<bool> {
    fn collect(
        expr: &PureExpr,
        names: &mut BTreeMap<String, bool>,
        remaining: &mut usize,
        depth: usize,
    ) -> Option<()> {
        if depth > 64 {
            return None;
        }
        *remaining = remaining.checked_sub(1)?;
        match expr {
            PureExpr::Bool(_) => Some(()),
            PureExpr::Var(name, Some(ExprSort::Bool)) => {
                names.insert(name.clone(), false);
                (names.len() <= 8).then_some(())
            }
            PureExpr::UnOp(UnOp::Not, inner) => collect(inner, names, remaining, depth + 1),
            PureExpr::BinOp(
                left,
                BinOp::And | BinOp::Or | BinOp::Implies | BinOp::Eq | BinOp::Ne,
                right,
            ) => {
                collect(left, names, remaining, depth + 1)?;
                collect(right, names, remaining, depth + 1)
            }
            PureExpr::Ite(condition, left, right) => {
                collect(condition, names, remaining, depth + 1)?;
                collect(left, names, remaining, depth + 1)?;
                collect(right, names, remaining, depth + 1)
            }
            _ => None,
        }
    }
    fn evaluate(expr: &PureExpr, values: &BTreeMap<String, bool>) -> Option<bool> {
        Some(match expr {
            PureExpr::Bool(value) => *value,
            PureExpr::Var(name, Some(ExprSort::Bool)) => *values.get(name)?,
            PureExpr::UnOp(UnOp::Not, inner) => !evaluate(inner, values)?,
            PureExpr::BinOp(left, op, right) => {
                let left = evaluate(left, values)?;
                let right = evaluate(right, values)?;
                match op {
                    BinOp::And => left && right,
                    BinOp::Or => left || right,
                    BinOp::Implies => !left || right,
                    BinOp::Eq => left == right,
                    BinOp::Ne => left != right,
                    _ => return None,
                }
            }
            PureExpr::Ite(condition, left, right) => {
                if evaluate(condition, values)? {
                    evaluate(left, values)?
                } else {
                    evaluate(right, values)?
                }
            }
            _ => return None,
        })
    }
    let mut values = BTreeMap::new();
    collect(predicate, &mut values, &mut 4096, 0)?;
    for bits in 0..(1usize << values.len()) {
        for (index, value) in values.values_mut().enumerate() {
            *value = bits & (1 << index) != 0;
        }
        if !evaluate(predicate, &values)? {
            return Some(false);
        }
    }
    Some(true)
}

// Both validity and countermodel discovery admit exactly this state-free typed
// fragment. Binding/state constructs are deliberately not traversed by substitution.
fn collect_scalar_case_inputs(
    expr: &PureExpr,
    names: &mut BTreeMap<String, bool>,
    integers: &mut BTreeMap<String, ()>,
    has_integer: &mut bool,
    remaining: &mut usize,
    depth: usize,
) -> Option<()> {
    if depth > 64 {
        return None;
    }
    *remaining = remaining.checked_sub(1)?;
    match expr {
        PureExpr::Bool(_) => Some(()),
        PureExpr::Int(_) => {
            *has_integer = true;
            Some(())
        }
        PureExpr::Var(name, Some(ExprSort::Int)) => {
            *has_integer = true;
            integers.insert(name.clone(), ());
            Some(())
        }
        PureExpr::Var(name, Some(ExprSort::Bool)) => {
            names.insert(name.clone(), false);
            (names.len() <= 8).then_some(())
        }
        PureExpr::UnOp(op, inner) => {
            let sort = match op {
                UnOp::Not => ExprSort::Bool,
                UnOp::Neg | UnOp::BitNot => ExprSort::Int,
            };
            (scalar_sort(inner) == Some(sort)).then_some(())?;
            collect_scalar_case_inputs(inner, names, integers, has_integer, remaining, depth + 1)
        }
        PureExpr::BinOp(left, op, right) => {
            let left_sort = scalar_sort(left)?;
            let right_sort = scalar_sort(right)?;
            let well_sorted = match op {
                BinOp::And | BinOp::Or | BinOp::Implies => {
                    left_sort == ExprSort::Bool && right_sort == ExprSort::Bool
                }
                BinOp::Eq | BinOp::Ne => left_sort == right_sort,
                _ => left_sort == ExprSort::Int && right_sort == ExprSort::Int,
            };
            well_sorted.then_some(())?;
            collect_scalar_case_inputs(left, names, integers, has_integer, remaining, depth + 1)?;
            collect_scalar_case_inputs(right, names, integers, has_integer, remaining, depth + 1)
        }
        PureExpr::Ite(condition, left, right) => {
            (scalar_sort(condition) == Some(ExprSort::Bool)
                && scalar_sort(left).is_some()
                && scalar_sort(left) == scalar_sort(right))
            .then_some(())?;
            collect_scalar_case_inputs(
                condition,
                names,
                integers,
                has_integer,
                remaining,
                depth + 1,
            )?;
            collect_scalar_case_inputs(left, names, integers, has_integer, remaining, depth + 1)?;
            collect_scalar_case_inputs(right, names, integers, has_integer, remaining, depth + 1)
        }
        // Substitution must not identify current and old-state values or
        // rewrite a bound name. Those constructs keep their existing rules.
        _ => None,
    }
}

/// Exhaust only Boolean inputs, then prove each complete residual goal with
/// the ordinary scalar replay rules. Integer names remain universally symbolic;
/// failure to prove one residual is not a counterexample to that residual.
fn mixed_boolean_integer_validity(
    predicate: &PureExpr,
    context: &NativeReplayContext<'_>,
) -> Option<bool> {
    let mut values = BTreeMap::new();
    let mut integers = BTreeMap::new();
    let mut has_integer = false;
    collect_scalar_case_inputs(
        predicate,
        &mut values,
        &mut integers,
        &mut has_integer,
        &mut 4096,
        0,
    )?;
    if values.is_empty() || !has_integer || scalar_sort(predicate) != Some(ExprSort::Bool) {
        return None;
    }
    let mut all_proved = true;
    for bits in 0..(1usize << values.len()) {
        let mut substitutions = HashMap::new();
        for (index, (name, value)) in values.iter_mut().enumerate() {
            *value = bits & (1 << index) != 0;
            substitutions.insert(name.clone(), PureExpr::Bool(*value));
        }
        let residual = predicate
            .substitute_capture_avoiding(&substitutions, &CaptureAvoidingSubstOptions::default());
        match prove_bool(&residual, context) {
            TruthValue::True { .. } => {}
            TruthValue::False { .. } => return Some(false),
            TruthValue::Unknown { .. } => all_proved = false,
        }
    }
    all_proved.then_some(true)
}

/// Search hints are not a decision procedure for integers. Only a total,
/// sort-exact assignment making the entire original goal false can refute it.
/// Failure to find one leaves the existing Unknown result unchanged.
fn checked_scalar_counterexample(
    predicate: &PureExpr,
    context: &NativeReplayContext<'_>,
) -> Option<String> {
    // Summary facts may constrain candidate values. This fragment does not yet
    // instantiate/check those facts, so it must not refute under an empty context.
    if !context.summary_facts.is_empty() {
        return None;
    }
    let mut booleans = BTreeMap::new();
    let mut integers = BTreeMap::new();
    let mut has_integer = false;
    collect_scalar_case_inputs(
        predicate,
        &mut booleans,
        &mut integers,
        &mut has_integer,
        &mut 4096,
        0,
    )?;
    if integers.is_empty() || integers.len() > 8 || scalar_sort(predicate) != Some(ExprSort::Bool) {
        return None;
    }
    // Zero, each individual one, and all ones find distinct unsigned inputs
    // without enumerating an integer domain or changing the predicate's guards.
    for bits in 0..(1usize << booleans.len()) {
        for integer_case in 0..integers.len() + 2 {
            let mut substitutions = HashMap::new();
            for (index, name) in booleans.keys().enumerate() {
                substitutions.insert(name.clone(), PureExpr::Bool(bits & (1 << index) != 0));
            }
            for (index, name) in integers.keys().enumerate() {
                let value =
                    i64::from(integer_case == index + 1 || integer_case == integers.len() + 1);
                substitutions.insert(name.clone(), PureExpr::Int(value));
            }
            if check_scalar_counterexample(predicate, &substitutions) {
                let mut assignments = substitutions.iter().collect::<Vec<_>>();
                assignments.sort_by(|left, right| left.0.cmp(right.0));
                return Some(
                    assignments
                        .iter()
                        .map(|(name, value)| format!("{name}={value}"))
                        .collect::<Vec<_>>()
                        .join(", "),
                );
            }
        }
    }
    None
}

fn check_scalar_counterexample(
    predicate: &PureExpr,
    substitutions: &HashMap<String, PureExpr>,
) -> bool {
    let mut booleans = BTreeMap::new();
    let mut integers = BTreeMap::new();
    let mut has_integer = false;
    if collect_scalar_case_inputs(
        predicate,
        &mut booleans,
        &mut integers,
        &mut has_integer,
        &mut 4096,
        0,
    )
    .is_none()
        || scalar_sort(predicate) != Some(ExprSort::Bool)
    {
        return false;
    }
    if substitutions.len() != booleans.len() + integers.len()
        || booleans
            .keys()
            .any(|name| !matches!(substitutions.get(name), Some(PureExpr::Bool(_))))
        || integers
            .keys()
            .any(|name| !matches!(substitutions.get(name), Some(PureExpr::Int(_))))
    {
        return false;
    }
    let ground = predicate
        .substitute_capture_avoiding(substitutions, &CaptureAvoidingSubstOptions::default());
    matches!(
        prove_bool(&ground, &NativeReplayContext { summary_facts: &[] }),
        TruthValue::False { .. }
    )
}

#[cfg(test)]
mod boolean_case_split_tests {
    use super::*;

    #[test]
    fn complete_goal_validity_is_not_subexpression_truth() {
        for text in ["(p : bool) ==> false", "(p : bool) == !(p : bool)"] {
            let predicate = parse_contract(text).unwrap();
            assert_eq!(boolean_validity(&predicate), Some(false));
            assert!(!matches!(
                prove_native_pure_predicate(&predicate, NativeClaimFormat::TrustWpPureExprV1, &[]),
                NativePureProofOutcome::Verified(_)
            ));
        }
    }

    #[test]
    fn boolean_branch_identity_has_checked_cases() {
        let predicate = parse_contract(
            "((p : bool) ==> (false == !(p : bool))) && (!(p : bool) ==> (true == !(p : bool)))",
        )
        .unwrap();
        assert_eq!(boolean_validity(&predicate), Some(true));
        assert!(matches!(
            prove_native_pure_predicate(&predicate, NativeClaimFormat::TrustWpPureExprV1, &[]),
            NativePureProofOutcome::Verified(_)
        ));
    }

    #[test]
    fn concrete_counterexample_checks_total_sort_exact_values_and_original_guards() {
        let predicate = elaborate(
            &parse_contract(
                "((x : Int) >= 0 && x <= 255 && (y : Int) >= 0 && y <= 255) ==> \
             (((c : bool) ==> y == x) && (!c ==> x == y))",
            )
            .unwrap(),
        )
        .typed;
        let candidate = HashMap::from([
            ("c".into(), PureExpr::Bool(false)),
            ("x".into(), PureExpr::Int(0)),
            ("y".into(), PureExpr::Int(1)),
        ]);
        assert!(check_scalar_counterexample(&predicate, &candidate));
        let mut changed = candidate.clone();
        changed.remove("y");
        assert!(!check_scalar_counterexample(&predicate, &changed));
        let mut changed = candidate.clone();
        changed.insert("y".into(), PureExpr::Bool(true));
        assert!(!check_scalar_counterexample(&predicate, &changed));
        let mut changed = candidate.clone();
        changed.insert("y".into(), PureExpr::Int(256));
        assert!(!check_scalar_counterexample(&predicate, &changed));
        let mut changed = candidate.clone();
        changed.insert("y".into(), PureExpr::Int(0));
        assert!(!check_scalar_counterexample(&predicate, &changed));
        let mut changed = candidate;
        changed.insert("unrelated".into(), PureExpr::Int(1));
        assert!(!check_scalar_counterexample(&predicate, &changed));
        let stateful = elaborate(&parse_contract("(p : bool) == old(p)").unwrap()).typed;
        assert!(!check_scalar_counterexample(
            &stateful,
            &HashMap::from([("p".into(), PureExpr::Bool(false))])
        ));
    }

    #[test]
    fn untyped_integer_and_oversized_cases_are_not_boolean_proofs() {
        assert_eq!(boolean_validity(&parse_contract("x == x").unwrap()), None);
        assert_eq!(
            boolean_validity(&parse_contract("(x : Int) == (x : Int)").unwrap()),
            None
        );
        let names = (0..9)
            .map(|index| format!("(p{index} : bool)"))
            .collect::<Vec<_>>()
            .join(" || ");
        assert_eq!(boolean_validity(&parse_contract(&names).unwrap()), None);
    }
}

/// Create checked native pure replay evidence for one obligation.
///
/// This is the public construction side of [`replay_native_pure_evidence`].
/// It validates that the obligation belongs to the request, proves the typed
/// native predicate through trust-wp's replay rules, and returns the canonical
/// proof-grade evidence envelope committed to the request, typed metadata,
/// summary facts, normalized obligation, and replay log.
pub fn create_native_pure_replay_evidence(
    request: &VerifyBundleRequest,
    obligation: &BundleObligation,
) -> Result<ProofEvidence, ProofReplayError> {
    let (_, proof) = checked_native_pure_proof(request, obligation)?;
    Ok(proof_evidence_for_obligation(request, obligation, &proof))
}

/// Create a verified obligation result with native replay evidence and solver
/// metadata.
///
/// Callers integrating MIR/tMIR directly can use this when they already have a
/// single typed obligation and need the same result surface produced by
/// [`NativeTrustWpBundleVerifier`](super::NativeTrustWpBundleVerifier).
pub fn create_native_pure_replay_result(
    request: &VerifyBundleRequest,
    obligation: &BundleObligation,
) -> Result<BundleObligationResult, ProofReplayError> {
    let (native_predicate, proof) = checked_native_pure_proof(request, obligation)?;
    let evidence = proof_evidence_for_obligation(request, obligation, &proof);
    let metadata =
        proof_result_metadata_for_obligation(obligation, &native_predicate, &proof, &evidence);
    Ok(BundleObligationResult::verified(obligation.id.clone(), evidence).with_metadata(metadata))
}

/// Replay and validate native trust-wp pure-predicate evidence for one obligation.
///
/// This is intentionally exact for v1: the replayed canonical evidence must
/// match the provided evidence byte-for-byte after stable wire serialization,
/// including artifact order. Missing, duplicated, tampered, or reordered
/// artifacts therefore fail closed.
pub fn replay_native_pure_evidence(
    request: &VerifyBundleRequest,
    obligation: &BundleObligation,
    evidence: &ProofEvidence,
) -> Result<(), ProofReplayError> {
    if !request
        .obligations
        .iter()
        .any(|candidate| candidate == obligation)
    {
        return Err(ProofReplayError::new(
            "proof_replay.obligation",
            format!(
                "obligation `{}` is not present in bundle `{}`",
                obligation.id, request.bundle_id
            ),
        ));
    }

    if let Some(diagnostic) = request.validation_diagnostics().into_iter().next() {
        return Err(ProofReplayError::new(diagnostic.code, diagnostic.message));
    }

    if evidence.format != ProofEvidenceFormat::TrustWpNativePureReplayV1 {
        return Err(ProofReplayError::new(
            "proof_replay.format",
            format!(
                "native pure replay requires `{}` evidence, got `{}`",
                TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
                evidence.format.as_str()
            ),
        ));
    }

    if !evidence.is_proof_grade() {
        return Err(ProofReplayError::new(
            "proof_replay.evidence",
            "evidence is missing proof-grade schema, checker, digest, or artifact identity",
        ));
    }

    let (_, proof) = checked_native_pure_proof(request, obligation)?;
    let expected = proof_evidence_for_obligation(request, obligation, &proof);

    if evidence.to_stable_wire() != expected.to_stable_wire() {
        return Err(ProofReplayError::new(
            "proof_replay.mismatch",
            format!(
                "canonical evidence does not match replayed native proof: {}",
                evidence_mismatch_detail(evidence, &expected)
            ),
        ));
    }

    Ok(())
}

fn checked_native_pure_proof(
    request: &VerifyBundleRequest,
    obligation: &BundleObligation,
) -> Result<(NativeBundlePredicate, NativePureProof), ProofReplayError> {
    if !request
        .obligations
        .iter()
        .any(|candidate| candidate == obligation)
    {
        return Err(ProofReplayError::new(
            "proof_replay.obligation",
            format!(
                "obligation `{}` is not present in bundle `{}`",
                obligation.id, request.bundle_id
            ),
        ));
    }

    if let Some(diagnostic) = request.validation_diagnostics().into_iter().next() {
        return Err(ProofReplayError::new(diagnostic.code, diagnostic.message));
    }

    if !is_trust_wp_owned_obligation_kind(&obligation.kind) {
        return Err(ProofReplayError::new(
            "proof_replay.kind",
            "trust-wp native replay does not own this obligation kind",
        ));
    }

    let native_predicate = native_predicate_for_obligation(obligation)
        .map_err(|diagnostic| ProofReplayError::new(diagnostic.code, diagnostic.message))?;

    match prove_native_pure_predicate(
        &native_predicate.predicate,
        native_predicate.claim_format,
        &obligation.summary_facts,
    ) {
        NativePureProofOutcome::Verified(proof) => Ok((native_predicate, proof)),
        NativePureProofOutcome::Failed(reason) | NativePureProofOutcome::Unsupported(reason) => {
            Err(ProofReplayError::new(
                "proof_replay.result",
                format!("obligation does not replay to verified: {reason}"),
            ))
        }
    }
}

/// Replay and validate aggregate verify-bundle evidence for a successful
/// result.
///
/// This validates the request and bundle-level manifest, then re-proves each
/// obligation with the native checker. Other proof formats are readable DATA,
/// but this API has no checker for them and refuses them regardless of metadata.
pub fn replay_verify_bundle_result_evidence(
    request: &VerifyBundleRequest,
    result: &VerifyBundleResult,
) -> Result<(), ProofReplayError> {
    if let Some(diagnostic) = request.validation_diagnostics().into_iter().next() {
        return Err(ProofReplayError::new(diagnostic.code, diagnostic.message));
    }
    let aggregate = checked_aggregate_result_evidence(request, result)?;
    replay_result_obligation_evidence(request, result)?;

    let expected = aggregate_proof_evidence_for_result(request, &result.obligation_results)
        .ok_or_else(|| {
            ProofReplayError::new(
                "proof_replay.aggregate_evidence",
                "verified result cannot be reconstructed into aggregate proof evidence",
            )
        })?;
    if aggregate.to_stable_wire() != expected.to_stable_wire() {
        return Err(ProofReplayError::new(
            "proof_replay.aggregate_mismatch",
            format!(
                "aggregate evidence does not match replayed bundle proof: {}",
                evidence_mismatch_detail(aggregate, &expected)
            ),
        ));
    }

    Ok(())
}

fn checked_aggregate_result_evidence<'a>(
    request: &VerifyBundleRequest,
    result: &'a VerifyBundleResult,
) -> Result<&'a ProofEvidence, ProofReplayError> {
    if result.api_version != VERIFY_BUNDLE_API_VERSION {
        return Err(ProofReplayError::new(
            "proof_replay.aggregate_api_version",
            format!(
                "result API version `{}` does not match `{VERIFY_BUNDLE_API_VERSION}`",
                result.api_version
            ),
        ));
    }
    if result.bundle_id != request.bundle_id {
        return Err(ProofReplayError::new(
            "proof_replay.aggregate_bundle",
            format!(
                "result bundle `{}` does not match request bundle `{}`",
                result.bundle_id, request.bundle_id
            ),
        ));
    }
    if result.status != VerifyBundleStatus::Verified {
        return Err(ProofReplayError::new(
            "proof_replay.aggregate_status",
            format!(
                "aggregate replay requires verified result status, got `{}`",
                result.status.as_str()
            ),
        ));
    }
    if result
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity != super::BundleDiagnosticSeverity::Warning)
    {
        return Err(ProofReplayError::new(
            "proof_replay.aggregate_diagnostics",
            "verified aggregate result contains fail-closed diagnostics",
        ));
    }

    let aggregate = result.aggregate_evidence.as_ref().ok_or_else(|| {
        ProofReplayError::new(
            "proof_replay.aggregate_evidence",
            "verified result is missing aggregate proof evidence",
        )
    })?;
    if aggregate.format != ProofEvidenceFormat::TrustWpVerifyBundleAggregateV1 {
        return Err(ProofReplayError::new(
            "proof_replay.aggregate_format",
            format!(
                "aggregate replay requires `{}` evidence, got `{}`",
                TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION,
                aggregate.format.as_str()
            ),
        ));
    }
    if !aggregate.is_proof_grade() {
        return Err(ProofReplayError::new(
            "proof_replay.aggregate_evidence",
            "aggregate evidence is missing proof-grade schema, checker, digest, or artifact identity",
        ));
    }

    Ok(aggregate)
}

fn replay_result_obligation_evidence(
    request: &VerifyBundleRequest,
    result: &VerifyBundleResult,
) -> Result<(), ProofReplayError> {
    for obligation in &request.obligations {
        let obligation_result = result
            .obligation_results
            .iter()
            .find(|candidate| candidate.obligation_id == obligation.id)
            .ok_or_else(|| {
                ProofReplayError::new(
                    "proof_replay.aggregate_obligation",
                    format!(
                        "verified aggregate result is missing obligation `{}`",
                        obligation.id
                    ),
                )
            })?;
        let BundleObligationStatus::Verified { evidence } = &obligation_result.status else {
            return Err(ProofReplayError::new(
                "proof_replay.aggregate_obligation",
                format!(
                    "aggregate replay requires verified obligation `{}`",
                    obligation.id
                ),
            ));
        };
        if obligation_result
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity != super::BundleDiagnosticSeverity::Warning)
        {
            return Err(ProofReplayError::new(
                "proof_replay.aggregate_obligation_diagnostics",
                format!(
                    "verified obligation `{}` contains fail-closed diagnostics",
                    obligation.id
                ),
            ));
        }
        replay_native_pure_evidence(request, obligation, evidence)?;
    }

    Ok(())
}

#[allow(clippy::too_many_lines)]
fn evidence_mismatch_detail(provided: &ProofEvidence, expected: &ProofEvidence) -> String {
    let mut details = Vec::new();

    push_field_diff(
        &mut details,
        "schema_version",
        provided.schema_version.as_str(),
        expected.schema_version.as_str(),
    );
    push_field_diff(
        &mut details,
        "producer",
        provided.producer.as_str(),
        expected.producer.as_str(),
    );
    push_field_diff(
        &mut details,
        "format",
        provided.format.as_str(),
        expected.format.as_str(),
    );
    push_field_diff(
        &mut details,
        "strength",
        provided.strength.as_str(),
        expected.strength.as_str(),
    );
    push_optional_field_diff(
        &mut details,
        "checked_by",
        provided.checked_by.as_deref(),
        expected.checked_by.as_deref(),
    );

    if provided.artifacts.len() != expected.artifacts.len() {
        details.push(format!(
            "artifact count differs: expected {}, got {}",
            expected.artifacts.len(),
            provided.artifacts.len()
        ));
    }

    for (index, (provided_artifact, expected_artifact)) in provided
        .artifacts
        .iter()
        .zip(expected.artifacts.iter())
        .enumerate()
    {
        let label = artifact_diagnostic_label(index, expected_artifact);
        push_digest_diff(
            &mut details,
            &format!("{label} digest"),
            &provided_artifact.digest,
            &expected_artifact.digest,
        );
        push_field_diff(
            &mut details,
            &format!("{label} schema_version"),
            provided_artifact.schema_version.as_str(),
            expected_artifact.schema_version.as_str(),
        );
        if provided_artifact.digest == expected_artifact.digest
            && provided_artifact.kind == expected_artifact.kind
        {
            push_field_diff(
                &mut details,
                &format!("{label} id"),
                provided_artifact.id.as_str(),
                expected_artifact.id.as_str(),
            );
        }
        push_field_diff(
            &mut details,
            &format!("{label} kind"),
            provided_artifact.kind.as_str(),
            expected_artifact.kind.as_str(),
        );
        push_field_diff(
            &mut details,
            &format!("{label} description"),
            provided_artifact.description.as_str(),
            expected_artifact.description.as_str(),
        );
        push_optional_field_diff(
            &mut details,
            &format!("{label} uri"),
            provided_artifact.uri.as_deref(),
            expected_artifact.uri.as_deref(),
        );
        push_optional_field_diff(
            &mut details,
            &format!("{label} inline bytes encoding"),
            provided_artifact
                .inline_bytes
                .as_ref()
                .map(|bytes| bytes.encoding.as_str()),
            expected_artifact
                .inline_bytes
                .as_ref()
                .map(|bytes| bytes.encoding.as_str()),
        );
        if provided_artifact.inline_bytes.is_some() != expected_artifact.inline_bytes.is_some() {
            details.push(format!(
                "{label} inline bytes presence differs: expected `{}`, got `{}`",
                expected_artifact.inline_bytes.is_some(),
                provided_artifact.inline_bytes.is_some(),
            ));
        }
    }
    push_optional_digest_diff(
        &mut details,
        "digest",
        provided.digest.as_ref(),
        expected.digest.as_ref(),
    );

    if details.is_empty() {
        "stable wire differs without a structured field mismatch".to_string()
    } else {
        details.truncate(4);
        details.join("; ")
    }
}

fn push_field_diff(details: &mut Vec<String>, field: &str, provided: &str, expected: &str) {
    if provided != expected {
        details.push(format!(
            "{field} differs: expected `{expected}`, got `{provided}`"
        ));
    }
}

fn push_optional_field_diff(
    details: &mut Vec<String>,
    field: &str,
    provided: Option<&str>,
    expected: Option<&str>,
) {
    if provided != expected {
        details.push(format!(
            "{field} differs: expected `{}`, got `{}`",
            expected.unwrap_or("none"),
            provided.unwrap_or("none"),
        ));
    }
}

fn push_optional_digest_diff(
    details: &mut Vec<String>,
    field: &str,
    provided: Option<&BundleDigest>,
    expected: Option<&BundleDigest>,
) {
    if provided != expected {
        details.push(format!(
            "{field} differs: expected `{}`, got `{}`",
            digest_material(expected),
            digest_material(provided),
        ));
    }
}

fn push_digest_diff(
    details: &mut Vec<String>,
    field: &str,
    provided: &BundleDigest,
    expected: &BundleDigest,
) {
    if provided != expected {
        details.push(format!(
            "{field} differs: expected `{}`, got `{}`",
            digest_material(Some(expected)),
            digest_material(Some(provided)),
        ));
    }
}

fn artifact_diagnostic_label(index: usize, expected_artifact: &EvidenceArtifact) -> String {
    format!(
        "artifact {index} (`{}`; binds {})",
        expected_artifact.kind.as_str(),
        artifact_diagnostic_scope(&expected_artifact.kind)
    )
}

fn artifact_diagnostic_scope(kind: &EvidenceArtifactKind) -> &'static str {
    match kind {
        EvidenceArtifactKind::RequestDigest => {
            "typed request envelope, verification options, and obligation inventory"
        }
        EvidenceArtifactKind::AggregateProofManifest => {
            "bundle-level proof result, per-obligation evidence identities, and request digest"
        }
        EvidenceArtifactKind::NormalizedObligation => {
            "typed claim, tMIR metadata, native replay/verifier/solver identities, proof context, and summary digest"
        }
        EvidenceArtifactKind::SummaryEvidence => {
            "cross-crate summary fact identities, producers, endpoints, and digests"
        }
        EvidenceArtifactKind::ReplayLog => {
            "normalized proof digest, summary digest, and native replay steps"
        }
        EvidenceArtifactKind::ProofCertificate => "external proof certificate identity",
        EvidenceArtifactKind::SolverTranscript => "external solver transcript identity",
        EvidenceArtifactKind::Counterexample => "counterexample artifact identity",
        EvidenceArtifactKind::Model => "solver model artifact identity",
        EvidenceArtifactKind::DiagnosticTrace => "diagnostic trace artifact identity",
    }
}

#[allow(clippy::too_many_lines)]
pub(super) fn proof_evidence_for_obligation(
    request: &VerifyBundleRequest,
    obligation: &BundleObligation,
    proof: &NativePureProof,
) -> ProofEvidence {
    let summary_artifact = summary_facts_artifact(&obligation.summary_facts);
    let summary_digest_line = summary_artifact.as_ref().map_or_else(
        || "none".to_string(),
        |artifact| {
            format!(
                "{}:{}",
                artifact.digest.algorithm.as_str(),
                artifact.digest.value.as_str()
            )
        },
    );
    let claim_digest_line = digest_material(obligation.claim.digest.as_ref());
    let source_location = source_location_material(obligation.location.as_ref());
    let native_origin = native_origin_material(obligation);
    let tmir_source_span = tmir_source_span_material(obligation);
    let native_verifier = native_verifier_material(obligation);
    let native_replay = native_replay_material(obligation);
    let native_solvers = native_solvers_material(obligation);
    let tmir_obligation_source = tmir_obligation_source_material(obligation);
    let proof_context_digest = proof_context_digest_line(&obligation.metadata.proof_context);
    let normalized_material = format!(
        "api={api}\nevidence-schema={evidence_schema}\nreplay-schema={replay_schema}\nbundle={bundle}\nproducer.name={producer_name}\nproducer.version={producer_version}\nproducer.revision={producer_revision}\ntarget.crate={target_crate}\ntarget.package={target_package}\ntarget.triple={target_triple}\nobligation={obligation_id}\nkind={kind}\nfunction={function}\nlocation.file={location_file}\nlocation.line={location_line}\nlocation.column={location_column}\nnative-origin={native_origin}\ntmir-source-span={tmir_source_span}\nnative-verifier={native_verifier}\nnative-replay={native_replay}\nnative-solvers={native_solvers}\ntmir-obligation-source={tmir_obligation_source}\nproof-context.assumptions={assumptions}\nproof-context.assertions={assertions}\nproof-context-digest={proof_context_digest}\nclaim-format={claim_format}\nclaim-digest={claim_digest}\npredicate={predicate}\nsummary-count={summary_count}\nsummary-digest={summary_digest}\n",
        api = VERIFY_BUNDLE_API_VERSION,
        evidence_schema = PROOF_EVIDENCE_SCHEMA_VERSION,
        replay_schema = TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
        bundle = request.bundle_id.as_str(),
        producer_name = material_text(&request.producer.name),
        producer_version = optional_material_text(request.producer.version.as_deref()),
        producer_revision = optional_material_text(request.producer.revision.as_deref()),
        target_crate = material_text(&request.target.crate_name),
        target_package = optional_material_text(request.target.package_name.as_deref()),
        target_triple = optional_material_text(request.target.target_triple.as_deref()),
        obligation_id = obligation.id.as_str(),
        kind = obligation_kind_label(&obligation.kind),
        function = obligation.function.as_str(),
        location_file = source_location.file.as_str(),
        location_line = source_location.line.as_str(),
        location_column = source_location.column.as_str(),
        native_origin = native_origin.as_str(),
        tmir_source_span = tmir_source_span.as_str(),
        native_verifier = native_verifier.as_str(),
        native_replay = native_replay.as_str(),
        native_solvers = native_solvers.as_str(),
        tmir_obligation_source = tmir_obligation_source.as_str(),
        assumptions = obligation.metadata.proof_context.assumptions.len(),
        assertions = obligation.metadata.proof_context.assertions.len(),
        proof_context_digest = proof_context_digest.as_str(),
        claim_format = claim_format_label(&obligation.claim.format),
        claim_digest = claim_digest_line.as_str(),
        predicate = proof.normalized_predicate.as_str(),
        summary_count = obligation.summary_facts.len(),
        summary_digest = summary_digest_line.as_str(),
    );
    let normalized_digest = stable_digest(&normalized_material);

    let replay_material = format!(
        "api={api}\nevidence-schema={evidence_schema}\nreplay-schema={replay_schema}\nnormalized-digest={algorithm}:{value}\nsummary-digest={summary_digest}\nsteps=\n{steps}\n",
        api = VERIFY_BUNDLE_API_VERSION,
        evidence_schema = PROOF_EVIDENCE_SCHEMA_VERSION,
        replay_schema = TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
        algorithm = normalized_digest.algorithm.as_str(),
        value = normalized_digest.value.as_str(),
        summary_digest = summary_digest_line.as_str(),
        steps = proof
            .steps
            .iter()
            .map(NativeReplayStep::as_wire_line)
            .collect::<Vec<_>>()
            .join("\n"),
    );
    let replay_digest = stable_digest(&replay_material);

    let normalized_artifact = EvidenceArtifact::new(
        EvidenceArtifactKind::NormalizedObligation,
        normalized_digest,
        "normalized typed trust-wp PureExpr obligation",
    )
    .with_utf8_bytes(normalized_material);
    let replay_artifact = EvidenceArtifact::new(
        EvidenceArtifactKind::ReplayLog,
        replay_digest,
        "native pure predicate replay trace",
    )
    .with_utf8_bytes(replay_material);
    let mut artifacts = vec![request_digest_artifact(request), normalized_artifact];
    artifacts.extend(summary_artifact);
    artifacts.push(replay_artifact);
    artifacts.push(proof_check_transcript_artifact(
        request, obligation, proof, &artifacts,
    ));
    let evidence_digest = stable_digest(&evidence_manifest_material(
        &ProofEvidenceFormat::TrustWpNativePureReplayV1,
        TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
        &artifacts,
    ));

    let mut evidence = ProofEvidence::checked(
        "trust-wp-core.verify_bundle",
        ProofEvidenceFormat::TrustWpNativePureReplayV1,
        TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
    )
    .with_strength(ProofStrength::Sound)
    .with_digest(evidence_digest);
    for artifact in artifacts {
        evidence = evidence.with_artifact(artifact);
    }
    evidence
}

pub(super) fn aggregate_proof_evidence_for_result(
    request: &VerifyBundleRequest,
    obligation_results: &[BundleObligationResult],
) -> Option<ProofEvidence> {
    if obligation_results.len() != request.obligations.len() {
        return None;
    }

    let mut seen = HashSet::new();
    for obligation in &request.obligations {
        let result = obligation_results
            .iter()
            .find(|candidate| candidate.obligation_id == obligation.id)?;
        if !seen.insert(result.obligation_id.as_str()) {
            return None;
        }
        let BundleObligationStatus::Verified { evidence } = &result.status else {
            return None;
        };
        if !evidence.is_proof_grade() {
            return None;
        }
    }

    let request_artifact = request_digest_artifact(request);
    let aggregate_material = aggregate_proof_manifest_material(request, obligation_results);
    let aggregate_artifact = EvidenceArtifact::new(
        EvidenceArtifactKind::AggregateProofManifest,
        stable_digest(&aggregate_material),
        "aggregate verify-bundle proof manifest",
    )
    .with_utf8_bytes(aggregate_material);
    let artifacts = vec![request_artifact, aggregate_artifact];
    let evidence_digest = stable_digest(&evidence_manifest_material(
        &ProofEvidenceFormat::TrustWpVerifyBundleAggregateV1,
        TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION,
        &artifacts,
    ));

    let mut evidence = ProofEvidence::checked(
        "trust-wp-core.verify_bundle",
        ProofEvidenceFormat::TrustWpVerifyBundleAggregateV1,
        TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION,
    )
    .with_strength(ProofStrength::Sound)
    .with_digest(evidence_digest);
    for artifact in artifacts {
        evidence = evidence.with_artifact(artifact);
    }
    Some(evidence)
}

pub(super) fn proof_result_metadata_for_obligation(
    obligation: &BundleObligation,
    native_predicate: &NativeBundlePredicate,
    proof: &NativePureProof,
    evidence: &ProofEvidence,
) -> BundleResultMetadata {
    let proof_context = &obligation.metadata.proof_context;
    BundleResultMetadata::new(
        Some(BundleSolverMetadata::new(
            "trust-wp-core.native-pure-replay",
            TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
            native_predicate.claim_format.as_str(),
            proof.replay_step_count(),
            proof_context.assumptions.len(),
            proof_context.assertions.len(),
        )),
        Some(BundleEvidenceMetadata::from_evidence(evidence)),
    )
}

pub(super) fn is_trust_wp_owned_obligation_kind(kind: &BundleObligationKind) -> bool {
    matches!(
        kind,
        BundleObligationKind::Precondition { .. }
            | BundleObligationKind::Postcondition
            | BundleObligationKind::LoopInvariant
    )
}

fn aggregate_proof_manifest_material(
    request: &VerifyBundleRequest,
    obligation_results: &[BundleObligationResult],
) -> String {
    let request_digest = stable_digest(&request_digest_material(request));
    let mut material = format!(
        "api={api}\nevidence-schema={evidence_schema}\naggregate-schema={aggregate_schema}\nbundle={bundle}\nrequest-digest={request_algorithm}:{request_value}\nobligation-count={obligation_count}\n",
        api = VERIFY_BUNDLE_API_VERSION,
        evidence_schema = PROOF_EVIDENCE_SCHEMA_VERSION,
        aggregate_schema = TRUST_WP_VERIFY_BUNDLE_AGGREGATE_SCHEMA_VERSION,
        bundle = material_text(&request.bundle_id),
        request_algorithm = request_digest.algorithm.as_str(),
        request_value = request_digest.value.as_str(),
        obligation_count = request.obligations.len(),
    );

    for (index, obligation) in request.obligations.iter().enumerate() {
        let result = obligation_results
            .iter()
            .find(|candidate| candidate.obligation_id == obligation.id)
            .expect("aggregate caller checked that all obligation results are present");
        let BundleObligationStatus::Verified { evidence } = &result.status else {
            unreachable!("aggregate caller checked that all obligation results are verified");
        };
        let evidence_wire_digest = stable_digest(&evidence.to_stable_wire());
        let _ = writeln!(
            material,
            "obligation.{index}.id={id}\nobligation.{index}.status=verified\nobligation.{index}.evidence-format={format}\nobligation.{index}.evidence-strength={strength}\nobligation.{index}.evidence-digest={digest}\nobligation.{index}.evidence-wire-digest={wire_algorithm}:{wire_value}\nobligation.{index}.checked-by={checked_by}\nobligation.{index}.artifact-count={artifact_count}",
            id = material_text(&obligation.id),
            format = material_text(evidence.format.as_str()),
            strength = evidence.strength.as_str(),
            digest = digest_material(evidence.digest.as_ref()),
            wire_algorithm = evidence_wire_digest.algorithm.as_str(),
            wire_value = evidence_wire_digest.value.as_str(),
            checked_by = optional_material_text(evidence.checked_by.as_deref()),
            artifact_count = evidence.artifacts.len(),
        );
        for (artifact_index, artifact) in evidence.artifacts.iter().enumerate() {
            let _ = writeln!(
                material,
                "obligation.{index}.artifact.{artifact_index}.id={id}\nobligation.{index}.artifact.{artifact_index}.kind={kind}\nobligation.{index}.artifact.{artifact_index}.digest={algorithm}:{value}",
                id = material_text(&artifact.id),
                kind = artifact.kind.as_str(),
                algorithm = artifact.digest.algorithm.as_str(),
                value = artifact.digest.value.as_str(),
            );
        }
    }

    material
}

fn evidence_manifest_material(
    format: &ProofEvidenceFormat,
    checker: &str,
    artifacts: &[EvidenceArtifact],
) -> String {
    let mut material = format!(
        "api={api}\nevidence-schema={evidence_schema}\nformat={format}\nstrength={strength}\nchecker={checker}\nartifact-count={artifact_count}\n",
        api = VERIFY_BUNDLE_API_VERSION,
        evidence_schema = PROOF_EVIDENCE_SCHEMA_VERSION,
        format = format.as_str(),
        strength = ProofStrength::Sound.as_str(),
        checker = checker,
        artifact_count = artifacts.len(),
    );
    for (index, artifact) in artifacts.iter().enumerate() {
        let _ = writeln!(
            material,
            "artifact.{index}.id={id}\nartifact.{index}.kind={kind}\nartifact.{index}.digest={algorithm}:{value}",
            id = artifact.id.as_str(),
            kind = artifact.kind.as_str(),
            algorithm = artifact.digest.algorithm.as_str(),
            value = artifact.digest.value.as_str(),
        );
    }
    material
}

fn summary_facts_artifact(summary_facts: &[BundleSummaryFact]) -> Option<EvidenceArtifact> {
    (!summary_facts.is_empty()).then(|| {
        let material = summary_facts_material(summary_facts);
        EvidenceArtifact::new(
            EvidenceArtifactKind::SummaryEvidence,
            stable_digest(&material),
            "cross-crate summary evidence inputs",
        )
        .with_utf8_bytes(material)
    })
}

fn request_digest_artifact(request: &VerifyBundleRequest) -> EvidenceArtifact {
    let material = request_digest_material(request);
    EvidenceArtifact::new(
        EvidenceArtifactKind::RequestDigest,
        stable_digest(&material),
        "canonical verify-bundle request digest",
    )
    .with_utf8_bytes(material)
}

fn proof_check_transcript_artifact(
    request: &VerifyBundleRequest,
    obligation: &BundleObligation,
    proof: &NativePureProof,
    checked_artifacts: &[EvidenceArtifact],
) -> EvidenceArtifact {
    let material = proof_check_transcript_material(request, obligation, proof, checked_artifacts);
    EvidenceArtifact::new(
        EvidenceArtifactKind::SolverTranscript,
        stable_digest(&material),
        "native pure replay proof-check transcript over evidence artifact bytes",
    )
    .with_utf8_bytes(material)
}

fn proof_check_transcript_material(
    request: &VerifyBundleRequest,
    obligation: &BundleObligation,
    proof: &NativePureProof,
    checked_artifacts: &[EvidenceArtifact],
) -> String {
    let mut material = format!(
        "schema=trust-wp.native-pure-proof-check-transcript.v1\napi={api}\nevidence-schema={evidence_schema}\nreplay-schema={replay_schema}\nbundle={bundle}\nobligation={obligation}\nchecker={checker}\nresult=verified\nreplay-steps={replay_steps}\nchecked-artifacts={artifact_count}\n",
        api = VERIFY_BUNDLE_API_VERSION,
        evidence_schema = PROOF_EVIDENCE_SCHEMA_VERSION,
        replay_schema = TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
        bundle = material_text(&request.bundle_id),
        obligation = material_text(&obligation.id),
        checker = TRUST_WP_NATIVE_PURE_REPLAY_SCHEMA_VERSION,
        replay_steps = proof.replay_step_count(),
        artifact_count = checked_artifacts.len(),
    );

    for (index, artifact) in checked_artifacts.iter().enumerate() {
        let transport = artifact_transport_material(artifact);
        let _ = writeln!(
            material,
            "artifact.{index}.id={id}\nartifact.{index}.kind={kind}\nartifact.{index}.declared-digest={declared_algorithm}:{declared_value}\nartifact.{index}.transport={transport}\nartifact.{index}.actual-digest={actual_digest}\nartifact.{index}.byte-len={byte_len}",
            id = artifact.id.as_str(),
            kind = artifact.kind.as_str(),
            declared_algorithm = artifact.digest.algorithm.as_str(),
            declared_value = artifact.digest.value.as_str(),
            transport = transport.kind.as_str(),
            actual_digest = transport.digest.as_str(),
            byte_len = transport.byte_len.as_str(),
        );
    }

    material
}

struct ArtifactTransportMaterial {
    kind: String,
    digest: String,
    byte_len: String,
}

fn artifact_transport_material(artifact: &EvidenceArtifact) -> ArtifactTransportMaterial {
    match artifact
        .inline_bytes
        .as_ref()
        .and_then(|bytes| bytes.decoded_bytes().ok())
    {
        Some(bytes) => ArtifactTransportMaterial {
            kind: artifact.inline_bytes.as_ref().map_or_else(
                || "inline:unknown".to_string(),
                |bytes| format!("inline:{}", bytes.encoding.as_str()),
            ),
            digest: digest_bytes_material(&bytes),
            byte_len: bytes.len().to_string(),
        },
        None => ArtifactTransportMaterial {
            kind: artifact.uri.as_ref().map_or_else(
                || "missing".to_string(),
                |uri| format!("uri:{}", material_text(uri)),
            ),
            digest: "none".to_string(),
            byte_len: "none".to_string(),
        },
    }
}

fn digest_material(digest: Option<&BundleDigest>) -> String {
    digest.map_or_else(
        || "none".to_string(),
        |digest| format!("{}:{}", digest.algorithm.as_str(), digest.value.as_str()),
    )
}

fn digest_bytes_material(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    format!("sha256:{}", hex_bytes(&hasher.finalize()))
}

fn material_text(value: &str) -> String {
    format!("hex:{}", hex_bytes(value.as_bytes()))
}

fn optional_material_text(value: Option<&str>) -> String {
    value.map_or_else(|| "none".to_string(), material_text)
}

struct SourceLocationMaterial {
    file: String,
    line: String,
    column: String,
}

fn source_location_material(location: Option<&super::BundleSourceSpan>) -> SourceLocationMaterial {
    location.map_or_else(
        || SourceLocationMaterial {
            file: "none".to_string(),
            line: "none".to_string(),
            column: "none".to_string(),
        },
        |location| SourceLocationMaterial {
            file: material_text(&location.file),
            line: location.line.to_string(),
            column: location.column.to_string(),
        },
    )
}

fn native_origin_material(obligation: &BundleObligation) -> String {
    obligation.metadata.native_origin.as_ref().map_or_else(
        || "none".to_string(),
        |origin| {
            let lineage_roots = if origin.lineage_roots.is_empty() {
                "none".to_string()
            } else {
                origin
                    .lineage_roots
                    .iter()
                    .map(u32::to_string)
                    .collect::<Vec<_>>()
                    .join(",")
            };
            let module_digest = digest_material(origin.tmir_module_digest.as_ref());
            format!(
                "schema={};mode={};request={};function={};obligation={};lineage-roots={};tmir-digest={}",
                material_text(&origin.schema),
                origin.mode.as_str(),
                origin.request_id,
                origin.function_id,
                origin.obligation_id,
                lineage_roots,
                module_digest,
            )
        },
    )
}

fn tmir_source_span_material(obligation: &BundleObligation) -> String {
    obligation.metadata.tmir_source_span.map_or_else(
        || "none".to_string(),
        |span| {
            format!(
                "file-id={};line={};column={}",
                span.file_id, span.line, span.column
            )
        },
    )
}

fn native_verifier_material(obligation: &BundleObligation) -> String {
    obligation
        .metadata
        .native_verifier
        .as_ref()
        .map_or_else(|| "none".to_string(), native_tool_identity_material)
}

fn native_replay_material(obligation: &BundleObligation) -> String {
    obligation.metadata.native_replay.as_ref().map_or_else(
        || "none".to_string(),
        |replay| {
            format!(
                "engine={};invocation={};transcript={}",
                material_text(&replay.engine),
                material_text(&replay.invocation),
                digest_material(Some(&replay.transcript_digest)),
            )
        },
    )
}

fn native_solvers_material(obligation: &BundleObligation) -> String {
    if obligation.metadata.native_solvers.is_empty() {
        return "none".to_string();
    }

    obligation
        .metadata
        .native_solvers
        .iter()
        .enumerate()
        .map(|(index, solver)| format!("{index}:{}", native_tool_identity_material(solver)))
        .collect::<Vec<_>>()
        .join(",")
}

fn native_tool_identity_material(identity: &BundleNativeToolIdentity) -> String {
    format!(
        "name={};version={};revision={};digest={}",
        material_text(&identity.name),
        optional_material_text(identity.version.as_deref()),
        optional_material_text(identity.revision.as_deref()),
        digest_material(identity.digest.as_ref()),
    )
}

fn tmir_obligation_source_material(obligation: &BundleObligation) -> String {
    obligation
        .metadata
        .tmir_obligation_source
        .as_ref()
        .map_or_else(
            || "none".to_string(),
            |source| {
                let mut fact_refs = source.compiler_fact_refs.iter().collect::<Vec<_>>();
                fact_refs.sort_by(|left, right| {
                    left.kind
                        .as_str()
                        .cmp(right.kind.as_str())
                        .then(left.id.cmp(&right.id))
                });
                let facts = if fact_refs.is_empty() {
                    "none".to_string()
                } else {
                    fact_refs
                        .into_iter()
                        .map(|fact| {
                            format!(
                                "{}:{}:{}",
                                fact.kind.as_str(),
                                fact.id,
                                digest_material(fact.digest.as_ref())
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(",")
                };
                format!(
                    "cause={};function={};assertion={};monomorphization={};facts={}",
                    material_text(source.cause.as_str()),
                    source
                        .function_id
                        .map_or_else(|| "none".to_string(), |id| id.to_string()),
                    source
                        .assertion_id
                        .map_or_else(|| "none".to_string(), |id| id.to_string()),
                    source
                        .monomorphization_id
                        .map_or_else(|| "none".to_string(), |id| id.to_string()),
                    material_text(&facts),
                )
            },
        )
}

fn proof_context_digest_line(context: &super::BundleProofContext) -> String {
    context.canonical_digest().map_or_else(
        || "none".to_string(),
        |digest| format!("{}:{}", digest.algorithm.as_str(), digest.value.as_str()),
    )
}

fn request_digest_material(request: &VerifyBundleRequest) -> String {
    let mut material = format!(
        "api={api}\nevidence-schema={evidence_schema}\nrequest.api={request_api}\nbundle={bundle}\nproducer.name={producer_name}\nproducer.version={producer_version}\nproducer.revision={producer_revision}\ntarget.crate={target_crate}\ntarget.package={target_package}\ntarget.triple={target_triple}\noptions.require-proof-evidence={require_proof_evidence}\noptions.timeout-ms={timeout_ms}\nobligation-count={obligation_count}\n",
        api = VERIFY_BUNDLE_API_VERSION,
        evidence_schema = PROOF_EVIDENCE_SCHEMA_VERSION,
        request_api = material_text(&request.api_version),
        bundle = material_text(&request.bundle_id),
        producer_name = material_text(&request.producer.name),
        producer_version = optional_material_text(request.producer.version.as_deref()),
        producer_revision = optional_material_text(request.producer.revision.as_deref()),
        target_crate = material_text(&request.target.crate_name),
        target_package = optional_material_text(request.target.package_name.as_deref()),
        target_triple = optional_material_text(request.target.target_triple.as_deref()),
        require_proof_evidence = request.options.require_proof_evidence,
        timeout_ms = timeout_material(request.options.timeout_ms),
        obligation_count = request.obligations.len(),
    );

    for (index, obligation) in request.obligations.iter().enumerate() {
        let location = source_location_material(obligation.location.as_ref());
        let native_origin = native_origin_material(obligation);
        let tmir_source_span = tmir_source_span_material(obligation);
        let native_verifier = native_verifier_material(obligation);
        let native_replay = native_replay_material(obligation);
        let native_solvers = native_solvers_material(obligation);
        let tmir_obligation_source = tmir_obligation_source_material(obligation);
        let proof_context_digest = proof_context_digest_line(&obligation.metadata.proof_context);
        let payload_digest = stable_digest(&obligation.claim.payload);
        let summary_digest_line = if obligation.summary_facts.is_empty() {
            "none".to_string()
        } else {
            let digest = stable_digest(&summary_facts_material(&obligation.summary_facts));
            format!("{}:{}", digest.algorithm.as_str(), digest.value.as_str())
        };
        let _ = writeln!(
            material,
            "obligation.{index}.id={id}\nobligation.{index}.kind={kind}\nobligation.{index}.function={function}\nobligation.{index}.location.file={location_file}\nobligation.{index}.location.line={location_line}\nobligation.{index}.location.column={location_column}\nobligation.{index}.native-origin={native_origin}\nobligation.{index}.tmir-source-span={tmir_source_span}\nobligation.{index}.native-verifier={native_verifier}\nobligation.{index}.native-replay={native_replay}\nobligation.{index}.native-solvers={native_solvers}\nobligation.{index}.tmir-obligation-source={tmir_obligation_source}\nobligation.{index}.proof-context.assumptions={assumptions}\nobligation.{index}.proof-context.assertions={assertions}\nobligation.{index}.proof-context-digest={proof_context_digest}\nobligation.{index}.claim-format={claim_format}\nobligation.{index}.claim-digest={claim_digest}\nobligation.{index}.claim-payload-digest={payload_algorithm}:{payload_value}\nobligation.{index}.summary-count={summary_count}\nobligation.{index}.summary-digest={summary_digest}",
            id = material_text(&obligation.id),
            kind = material_text(&obligation_kind_label(&obligation.kind)),
            function = material_text(&obligation.function),
            location_file = location.file.as_str(),
            location_line = location.line.as_str(),
            location_column = location.column.as_str(),
            native_origin = native_origin.as_str(),
            tmir_source_span = tmir_source_span.as_str(),
            native_verifier = native_verifier.as_str(),
            native_replay = native_replay.as_str(),
            native_solvers = native_solvers.as_str(),
            tmir_obligation_source = tmir_obligation_source.as_str(),
            assumptions = obligation.metadata.proof_context.assumptions.len(),
            assertions = obligation.metadata.proof_context.assertions.len(),
            proof_context_digest = proof_context_digest.as_str(),
            claim_format = material_text(claim_format_label(&obligation.claim.format)),
            claim_digest = digest_material(obligation.claim.digest.as_ref()),
            payload_algorithm = payload_digest.algorithm.as_str(),
            payload_value = payload_digest.value.as_str(),
            summary_count = obligation.summary_facts.len(),
            summary_digest = summary_digest_line.as_str(),
        );
    }

    material
}

fn timeout_material(timeout_ms: Option<u64>) -> String {
    timeout_ms.map_or_else(|| "none".to_string(), |timeout_ms| timeout_ms.to_string())
}

fn summary_facts_material(summary_facts: &[BundleSummaryFact]) -> String {
    let mut facts = summary_facts.iter().collect::<Vec<_>>();
    facts.sort_by(|left, right| left.id.cmp(&right.id));

    let mut material = format!(
        "api={api}\nevidence-schema={evidence_schema}\nsummary-count={summary_count}\n",
        api = VERIFY_BUNDLE_API_VERSION,
        evidence_schema = PROOF_EVIDENCE_SCHEMA_VERSION,
        summary_count = facts.len(),
    );
    for (index, fact) in facts.into_iter().enumerate() {
        let _ = writeln!(
            material,
            "summary.{index}.id={id}\nsummary.{index}.producer={producer}\nsummary.{index}.source-crate={source_crate}\nsummary.{index}.source-item={source_item}\nsummary.{index}.kind={kind}\nsummary.{index}.digest={algorithm}:{value}",
            id = fact.id.as_str(),
            producer = fact.producer.as_str(),
            source_crate = fact.source_crate.as_str(),
            source_item = fact.source_item.as_str(),
            kind = fact.kind.as_str(),
            algorithm = fact.digest.algorithm.as_str(),
            value = fact.digest.value.as_str(),
        );
        if let Some(endpoints) = summary_fact_endpoints(fact) {
            let (left, right) = match endpoints {
                SummaryFactEndpoints::Textual { left, right }
                | SummaryFactEndpoints::Binding { left, right } => (left, right),
            };
            let _ = writeln!(
                material,
                "summary.{index}.left={left}\nsummary.{index}.right={right}",
            );
        }
    }
    material
}

fn stable_digest(material: &str) -> BundleDigest {
    let mut hasher = Sha256::new();
    hasher.update(material.as_bytes());
    BundleDigest::new("sha256", hex_bytes(&hasher.finalize()))
}

fn hex_bytes(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    // Formatting rather than a lookup table. The table indices are provably
    // 0..=15 and the capacity product provably fits for any real slice, but
    // both are obligations this function cannot discharge from its own body:
    // the shift/mask range and the length bound belong to the caller. `{:02x}`
    // has neither an index nor a product and emits the identical lowercase
    // two-digit hex.
    let mut encoded = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        // Writing to a String cannot fail.
        let _ = write!(encoded, "{byte:02x}");
    }
    encoded
}

fn obligation_kind_label(kind: &BundleObligationKind) -> String {
    match kind {
        BundleObligationKind::Precondition { callee } => format!("precondition:{callee}"),
        BundleObligationKind::Postcondition => "postcondition".to_string(),
        BundleObligationKind::Assertion { message } => format!("assertion:{message}"),
        BundleObligationKind::LoopInvariant => "loop-invariant".to_string(),
        BundleObligationKind::Termination => "termination".to_string(),
        BundleObligationKind::MemorySafety => "memory-safety".to_string(),
        BundleObligationKind::ArithmeticSafety => "arithmetic-safety".to_string(),
        BundleObligationKind::TranslationValidation { pass } => {
            format!("translation-validation:{pass}")
        }
        BundleObligationKind::Other(kind) => format!("other:{kind}"),
    }
}

fn claim_format_label(format: &BundleClaimFormat) -> &str {
    format.as_str()
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TruthValue {
    True { rule: &'static str },
    False { rule: &'static str },
    Unknown { reason: String },
}

#[derive(Debug, Clone, Copy)]
struct NativeReplayContext<'a> {
    summary_facts: &'a [BundleSummaryFact],
}

impl TruthValue {
    fn from_bool(value: bool, rule: &'static str) -> Self {
        if value {
            Self::True { rule }
        } else {
            Self::False { rule }
        }
    }

    fn unknown(reason: impl Into<String>) -> Self {
        Self::Unknown {
            reason: reason.into(),
        }
    }
}

/// The truth native replay proves of an elaborated predicate: every name in
/// it carries its sort (`formula::elaborate`), which the rules below read.
fn prove_bool(expr: &PureExpr, context: &NativeReplayContext<'_>) -> TruthValue {
    match expr {
        PureExpr::Bool(value) => TruthValue::from_bool(*value, "bool-literal"),
        PureExpr::UnOp(UnOp::Not, inner) => match prove_bool(inner, context) {
            TruthValue::True { .. } => TruthValue::False { rule: "not-true" },
            TruthValue::False { .. } => TruthValue::True { rule: "not-false" },
            TruthValue::Unknown { reason } => TruthValue::Unknown { reason },
        },
        PureExpr::BinOp(left, op, right) => prove_binary_bool(left, *op, right, context),
        PureExpr::Ite(cond, then_expr, else_expr) => prove_ite(cond, then_expr, else_expr, context),
        PureExpr::Forall {
            var,
            var_sort,
            body,
            ..
        } => {
            let domain = match replay_binder_domain(var, var_sort.as_ref()) {
                Ok(domain) => domain,
                Err(unknown) => return unknown,
            };
            match prove_bool(body, context) {
                TruthValue::True { .. } => TruthValue::True {
                    rule: "forall-true-body",
                },
                // A false body refutes `forall` only at a value of the
                // domain: over an empty one the claim holds vacuously.
                TruthValue::False { .. } if domain == BinderDomain::Inhabited => {
                    TruthValue::False {
                        rule: "forall-false-body",
                    }
                }
                TruthValue::False { .. } => TruthValue::unknown(format!(
                    "`forall` binder `{var}` ranges over a sort not known to be inhabited, so a \
                     false body does not refute it"
                )),
                TruthValue::Unknown { reason } => TruthValue::Unknown { reason },
            }
        }
        PureExpr::Exists {
            var,
            var_sort,
            body,
            ..
        } => {
            let domain = match replay_binder_domain(var, var_sort.as_ref()) {
                Ok(domain) => domain,
                Err(unknown) => return unknown,
            };
            match prove_bool(body, context) {
                // A true body proves `exists` only with a value to witness
                // it: over an empty domain the claim is false.
                TruthValue::True { .. } if domain == BinderDomain::Inhabited => TruthValue::True {
                    rule: "exists-true-body",
                },
                TruthValue::True { .. } => TruthValue::unknown(format!(
                    "`exists` binder `{var}` ranges over a sort not known to be inhabited, so a \
                     true body does not prove it"
                )),
                TruthValue::False { .. } => TruthValue::False {
                    rule: "exists-false-body",
                },
                TruthValue::Unknown { reason } => TruthValue::Unknown { reason },
            }
        }
        PureExpr::LetAssume { assumption, body } => {
            prove_binary_bool(assumption, BinOp::Implies, body, context)
        }
        PureExpr::LetObligation { obligation, body } => {
            prove_binary_bool(obligation, BinOp::And, body, context)
        }
        PureExpr::Let { var, value, body } => {
            let Some(inlined) = inline_let_binding_for_native_replay(var, value, body) else {
                return TruthValue::unknown(
                    "let binding crosses an old-state boundary outside the native replay fragment",
                );
            };
            prove_bool(&inlined, context)
        }
        PureExpr::Closure { .. }
        | PureExpr::Int(_)
        | PureExpr::Float(_)
        | PureExpr::Var(_, _)
        | PureExpr::UnOp(UnOp::Neg | UnOp::BitNot, _)
        | PureExpr::Old(_)
        | PureExpr::Deref(_)
        | PureExpr::Final(_)
        | PureExpr::View(_)
        | PureExpr::MethodCall { .. }
        | PureExpr::Match { .. }
        | PureExpr::LogicFnCall { .. } => {
            TruthValue::unknown("predicate is outside the native replay fragment")
        }
    }
}

/// What native replay knows of the values a quantifier binder ranges over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BinderDomain {
    /// `Int` or `Bool`: every body the binder reads is decided over a
    /// non-empty range, so a body that is false (true) everywhere refutes
    /// `forall` (proves `exists`).
    Inhabited,
    /// A reference: pointer replay models its values, but a reference to an
    /// uninhabited type has none, so no witness exists.
    MaybeEmpty,
}

/// The domain of a binder native replay models, or the `Unknown` refusing
/// one it does not: a type parameter could be any type, a sequence is not a
/// value the replay rules read, and an elided sort names no range at all.
/// Each of these was read as an integer by the arithmetic rules.
fn replay_binder_domain(
    var: &str,
    var_sort: Option<&ExprSort>,
) -> Result<BinderDomain, TruthValue> {
    match var_sort {
        Some(ExprSort::Int | ExprSort::Bool) => Ok(BinderDomain::Inhabited),
        Some(ExprSort::Ref(_) | ExprSort::MutRef(_)) => Ok(BinderDomain::MaybeEmpty),
        Some(
            sort @ (ExprSort::Seq
            | ExprSort::Unit
            | ExprSort::Datatype(_)
            | ExprSort::FMap
            | ExprSort::Tuple(_)
            | ExprSort::TypeParam(_)
            | ExprSort::Float(_)),
        ) => Err(TruthValue::unknown(format!(
            "quantifier binder `{var}` ranges over sort {sort}, which native replay does not model"
        ))),
        None => Err(TruthValue::unknown(format!(
            "quantifier binder `{var}` has no sort, so native replay has no range to read it over"
        ))),
    }
}

fn inline_let_binding_for_native_replay(
    var: &str,
    value: &PureExpr,
    body: &PureExpr,
) -> Option<PureExpr> {
    // A formula-level let evaluates `value` in the surrounding state. Moving
    // that expression beneath `old(...)` would instead evaluate its free
    // program variables in the entry state. Until replay carries explicit
    // state-indexed let values, reject this beta reduction rather than silently
    // changing `let t = x in old(t)` into `old(x)`.
    if body.any_recursive(|candidate| {
        matches!(candidate, PureExpr::Old(inner) if inner.any_free_var(|name, _| name == var))
    }) {
        return None;
    }
    let mut substitutions = HashMap::new();
    substitutions.insert(var.to_string(), value.clone());
    Some(body.substitute_capture_avoiding(&substitutions, &CaptureAvoidingSubstOptions::default()))
}

fn prove_binary_bool(
    left: &PureExpr,
    op: BinOp,
    right: &PureExpr,
    context: &NativeReplayContext<'_>,
) -> TruthValue {
    match op {
        BinOp::And => prove_and(left, right, context),
        BinOp::Or => prove_or(left, right, context),
        BinOp::Implies => prove_implies(left, right, context),
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            // Preserve the guard of a conditional operand instead of asking
            // the comparison prover to reason about an opaque value.  This is
            // the exact semantics of a total `if`: both guarded comparisons
            // must discharge independently.
            if let Some(rewritten) = split_comparison_ite(left, op, right) {
                prove_bool(&rewritten, context)
            } else {
                prove_comparison(left, op, right, context)
            }
        }
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::Div
        | BinOp::Mod
        | BinOp::DivTrunc
        | BinOp::RemTrunc
        | BinOp::Shl
        | BinOp::Shr
        | BinOp::BitAnd
        | BinOp::BitXor
        | BinOp::BitOr => TruthValue::unknown("arithmetic expression is not a predicate"),
    }
}

fn prove_and(left: &PureExpr, right: &PureExpr, context: &NativeReplayContext<'_>) -> TruthValue {
    match (prove_bool(left, context), prove_bool(right, context)) {
        (TruthValue::True { .. }, TruthValue::True { .. }) => TruthValue::True { rule: "and-true" },
        (TruthValue::False { .. }, _) | (_, TruthValue::False { .. }) => {
            TruthValue::False { rule: "and-false" }
        }
        (TruthValue::Unknown { reason }, _) | (_, TruthValue::Unknown { reason }) => {
            TruthValue::Unknown { reason }
        }
    }
}

fn prove_or(left: &PureExpr, right: &PureExpr, context: &NativeReplayContext<'_>) -> TruthValue {
    match (prove_bool(left, context), prove_bool(right, context)) {
        (TruthValue::True { .. }, _) | (_, TruthValue::True { .. }) => {
            TruthValue::True { rule: "or-true" }
        }
        (TruthValue::False { .. }, TruthValue::False { .. }) => {
            TruthValue::False { rule: "or-false" }
        }
        (TruthValue::Unknown { reason }, _) | (_, TruthValue::Unknown { reason }) => {
            TruthValue::Unknown { reason }
        }
    }
}

fn prove_implies(
    left: &PureExpr,
    right: &PureExpr,
    context: &NativeReplayContext<'_>,
) -> TruthValue {
    if assumption_entails_predicate(left, right) {
        return TruthValue::True {
            rule: "assumption-projection",
        };
    }

    match (prove_bool(left, context), prove_bool(right, context)) {
        (TruthValue::False { .. }, _) | (_, TruthValue::True { .. }) => TruthValue::True {
            rule: "implies-true",
        },
        (TruthValue::True { .. }, TruthValue::False { .. }) => TruthValue::False {
            rule: "implies-false",
        },
        (TruthValue::Unknown { reason }, _) | (_, TruthValue::Unknown { reason }) => {
            prove_int_arithmetic_implication(left, right)
                .or_else(|| prove_linear_implication(left, right))
                .unwrap_or(TruthValue::Unknown { reason })
        }
    }
}

fn assumption_entails_predicate(assumption: &PureExpr, predicate: &PureExpr) -> bool {
    if predicates_equivalent(assumption, predicate) {
        return true;
    }

    if let PureExpr::BinOp(left, BinOp::And, right) = predicate {
        return assumption_entails_predicate(assumption, left)
            && assumption_entails_predicate(assumption, right);
    }

    assumption_contains_predicate(assumption, predicate)
}

fn assumption_contains_predicate(assumption: &PureExpr, predicate: &PureExpr) -> bool {
    if predicates_equivalent(assumption, predicate) {
        return true;
    }

    if let Some(normalized) = denegate_ordered_integer_comparison(assumption) {
        if predicates_equivalent(&normalized, predicate) {
            return true;
        }
    }

    match assumption {
        PureExpr::BinOp(left, BinOp::And, right) => {
            assumption_contains_predicate(left, predicate)
                || assumption_contains_predicate(right, predicate)
        }
        _ => false,
    }
}

fn predicates_equivalent(left: &PureExpr, right: &PureExpr) -> bool {
    left == right || symmetric_comparison_equivalent(left, right)
}

fn symmetric_comparison_equivalent(left: &PureExpr, right: &PureExpr) -> bool {
    let PureExpr::BinOp(left_lhs, left_op, left_rhs) = left else {
        return false;
    };
    let PureExpr::BinOp(right_lhs, right_op, right_rhs) = right else {
        return false;
    };

    left_lhs == right_rhs
        && left_rhs == right_lhs
        && comparison_reverse(*left_op) == Some(*right_op)
}

fn comparison_reverse(op: BinOp) -> Option<BinOp> {
    match op {
        BinOp::Eq => Some(BinOp::Eq),
        BinOp::Ne => Some(BinOp::Ne),
        BinOp::Lt => Some(BinOp::Gt),
        BinOp::Le => Some(BinOp::Ge),
        BinOp::Gt => Some(BinOp::Lt),
        BinOp::Ge => Some(BinOp::Le),
        _ => None,
    }
}

/// Negate an ordered comparison without swapping its operands.
///
/// This is deliberately separate from [`comparison_reverse`].  It is valid
/// only over a total order and therefore remains gated by
/// [`is_int_sorted`] at its call site.
fn negate_ordered_comparison(op: BinOp) -> Option<BinOp> {
    match op {
        BinOp::Lt => Some(BinOp::Ge),
        BinOp::Gt => Some(BinOp::Le),
        BinOp::Le => Some(BinOp::Gt),
        BinOp::Ge => Some(BinOp::Lt),
        BinOp::Eq | BinOp::Ne => None,
        _ => None,
    }
}

/// Whether native replay knows `expr` to be an integer: a literal, a name
/// its elaboration makes an `Int` (or leaves unsorted), `*e` or
/// `^e` of a reference to an `Int`, the view `e@` of an integer `e` (the view
/// of any other sort is not modeled), and integer arithmetic, `old`, `if`
/// branches and `let` bodies over those. Every integer rule below reads an
/// operand as an integer only when this holds: a shape rule proves nothing
/// about a value that is not an integer, and `e + k > e` was proved of `*p`
/// for a `p: &bool`, a `&T` and a `&[Int]`.
fn is_int_sorted(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Int(_) => true,
        PureExpr::Var(_, sort) => sort.as_ref().is_none_or(|sort| *sort == ExprSort::Int),
        PureExpr::UnOp(UnOp::Neg | UnOp::BitNot, inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => is_int_sorted(inner),
        PureExpr::BinOp(left, op, right) => {
            matches!(
                op,
                BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Mod
                    | BinOp::DivTrunc
                    | BinOp::RemTrunc
                    | BinOp::Shl
                    | BinOp::Shr
                    | BinOp::BitAnd
                    | BinOp::BitXor
                    | BinOp::BitOr
            ) && is_int_sorted(left)
                && is_int_sorted(right)
        }
        PureExpr::Ite(_, then_expr, else_expr) => {
            is_int_sorted(then_expr) && is_int_sorted(else_expr)
        }
        PureExpr::Deref(operand) => {
            dereferenced(operand, Dereference::Current).referent() == Some(ExprSort::Int)
        }
        PureExpr::Final(operand) => {
            dereferenced(operand, Dereference::Final).referent() == Some(ExprSort::Int)
        }
        PureExpr::Let { body, .. } => is_int_sorted(body),
        PureExpr::Bool(_)
        | PureExpr::Float(_)
        | PureExpr::UnOp(UnOp::Not, _)
        | PureExpr::MethodCall { .. }
        | PureExpr::Forall { .. }
        | PureExpr::Exists { .. }
        | PureExpr::Match { .. }
        | PureExpr::LogicFnCall { .. }
        | PureExpr::LetAssume { .. }
        | PureExpr::LetObligation { .. }
        | PureExpr::Closure { .. } => false,
    }
}

/// `Int` when native replay reads `expr` as an integer ([`is_int_sorted`]),
/// `Bool` when the claim fixes it as a boolean ([`sort_of`]) or it is a
/// comparison, connective or quantifier, else `None`.
fn scalar_sort(expr: &PureExpr) -> Option<ExprSort> {
    if is_int_sorted(expr) {
        return Some(ExprSort::Int);
    }
    let boolean = sort_of(expr) == Some(ExprSort::Bool)
        || matches!(
            expr,
            PureExpr::BinOp(
                _,
                BinOp::Eq
                    | BinOp::Ne
                    | BinOp::Lt
                    | BinOp::Le
                    | BinOp::Gt
                    | BinOp::Ge
                    | BinOp::And
                    | BinOp::Or
                    | BinOp::Implies,
                _,
            ) | PureExpr::UnOp(UnOp::Not, _)
                | PureExpr::Forall { .. }
                | PureExpr::Exists { .. }
        );
    boolean.then_some(ExprSort::Bool)
}

/// Rewrite `!(a op b)` to the equivalent ordered integer comparison.
///
/// Equality and disequality are intentionally excluded: their negations do not
/// project to one ordered comparison. Float and other explicitly non-integer
/// sorts are also excluded, so this helper can only add a total-order integer
/// fact.
fn denegate_ordered_integer_comparison(expr: &PureExpr) -> Option<PureExpr> {
    let PureExpr::UnOp(UnOp::Not, inner) = expr else {
        return None;
    };
    let PureExpr::BinOp(left, op, right) = &**inner else {
        return None;
    };
    let negated = negate_ordered_comparison(*op)?;
    if !is_int_sorted(left) || !is_int_sorted(right) {
        return None;
    }
    Some(PureExpr::BinOp(
        Arc::clone(left),
        negated,
        Arc::clone(right),
    ))
}

fn ite_comparison_cases(cond: &PureExpr, then_cmp: PureExpr, else_cmp: PureExpr) -> PureExpr {
    let then_case = PureExpr::BinOp(Arc::new(cond.clone()), BinOp::Implies, Arc::new(then_cmp));
    let negated_cond = PureExpr::UnOp(UnOp::Not, Arc::new(cond.clone()));
    let else_case = PureExpr::BinOp(Arc::new(negated_cond), BinOp::Implies, Arc::new(else_cmp));
    PureExpr::BinOp(Arc::new(then_case), BinOp::And, Arc::new(else_case))
}

/// Split one conditional comparison operand into two guarded comparisons.
///
/// `(if c { t } else { e }) op rhs` is definitionally equivalent to
/// `(c -> t op rhs) && (!c -> e op rhs)`.  Recursion through the ordinary
/// boolean prover handles nested conditionals one layer at a time.  Splitting
/// the left operand first makes the rewrite deterministic when both sides are
/// conditional.
fn split_comparison_ite(left: &PureExpr, op: BinOp, right: &PureExpr) -> Option<PureExpr> {
    if let PureExpr::Ite(cond, then_arm, else_arm) = left {
        return Some(ite_comparison_cases(
            cond,
            PureExpr::BinOp(Arc::clone(then_arm), op, Arc::new(right.clone())),
            PureExpr::BinOp(Arc::clone(else_arm), op, Arc::new(right.clone())),
        ));
    }
    if let PureExpr::Ite(cond, then_arm, else_arm) = right {
        return Some(ite_comparison_cases(
            cond,
            PureExpr::BinOp(Arc::new(left.clone()), op, Arc::clone(then_arm)),
            PureExpr::BinOp(Arc::new(left.clone()), op, Arc::clone(else_arm)),
        ));
    }
    None
}

fn prove_ite(
    cond: &PureExpr,
    then_expr: &PureExpr,
    else_expr: &PureExpr,
    context: &NativeReplayContext<'_>,
) -> TruthValue {
    match prove_bool(cond, context) {
        TruthValue::True { .. } => prove_bool(then_expr, context),
        TruthValue::False { .. } => prove_bool(else_expr, context),
        TruthValue::Unknown { reason } => {
            let then_truth = prove_bool(then_expr, context);
            let else_truth = prove_bool(else_expr, context);
            match (then_truth, else_truth) {
                (TruthValue::True { .. }, TruthValue::True { .. }) => TruthValue::True {
                    rule: "ite-branches-true",
                },
                (TruthValue::False { .. }, TruthValue::False { .. }) => TruthValue::False {
                    rule: "ite-branches-false",
                },
                _ => TruthValue::Unknown { reason },
            }
        }
    }
}

fn prove_comparison(
    left: &PureExpr,
    op: BinOp,
    right: &PureExpr,
    context: &NativeReplayContext<'_>,
) -> TruthValue {
    if let Some(reason) =
        checked_bitwise_replay_diagnostic(left).or_else(|| checked_bitwise_replay_diagnostic(right))
    {
        return TruthValue::unknown(reason);
    }

    if left == right {
        return match op {
            BinOp::Eq | BinOp::Le | BinOp::Ge => TruthValue::True {
                rule: "reflexive-comparison",
            },
            BinOp::Ne | BinOp::Lt | BinOp::Gt => TruthValue::False {
                rule: "irreflexive-comparison",
            },
            _ => unreachable!("comparison operators handled by caller"),
        };
    }

    if let Some(result) = prove_pointer_summary_comparison(left, op, right, context) {
        return result;
    }

    if let Some(reason) = pointer_replay_diagnostic(left, right) {
        return TruthValue::unknown(reason);
    }

    if let Some(result) = prove_bitwise_comparison(left, op, right) {
        return result;
    }

    match (eval_value(left), eval_value(right)) {
        (Some(left), Some(right)) => compare_known_values(left, op, right),
        _ => match (constant_int(left), constant_int(right)) {
            (Some(first), Some(second)) if is_int_sorted(left) && is_int_sorted(right) => {
                // Direct comparison never negates MIN. Values exist only when
                // their closed integer constructors completed checked arithmetic.
                compare_integer_constants(first, op, second, "checked-wide-int-constant-comparison")
            }
            _ => prove_linear_comparison(left, op, right)
                .or_else(|| prove_boolean_scalar_comparison(left, op, right, context))
                .unwrap_or_else(|| {
                    TruthValue::unknown("comparison contains symbolic or unsupported operands")
                }),
        },
    }
}

/// Boolean operands may contain exact integer comparisons too wide for the
/// small constant evaluator. Reuse the ordinary proof rules on each smaller
/// operand; a validity counterexample is never used as an operand's truth.
fn prove_boolean_scalar_comparison(
    left: &PureExpr,
    op: BinOp,
    right: &PureExpr,
    context: &NativeReplayContext<'_>,
) -> Option<TruthValue> {
    if !matches!(op, BinOp::Eq | BinOp::Ne)
        || scalar_sort(left) != Some(ExprSort::Bool)
        || scalar_sort(right) != Some(ExprSort::Bool)
    {
        return None;
    }
    let contains_integer = |expr: &PureExpr| {
        expr.any_recursive(|node| {
            matches!(
                node,
                PureExpr::Int(_) | PureExpr::Var(_, Some(ExprSort::Int))
            )
        })
    };
    // Preserve the existing pure-Boolean case-split trace, including goals
    // whose smaller operands the structural prover can decide independently.
    if !contains_integer(left) && !contains_integer(right) {
        return None;
    }
    let truth = |expr| match prove_bool(expr, context) {
        TruthValue::True { .. } => Some(true),
        TruthValue::False { .. } => Some(false),
        TruthValue::Unknown { .. } => None,
    };
    let equal = truth(left)? == truth(right)?;
    Some(TruthValue::from_bool(
        equal == (op == BinOp::Eq),
        "boolean-scalar-comparison",
    ))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum PointerReplayKind {
    Thin,
    Fat,
}

fn prove_pointer_summary_comparison(
    left: &PureExpr,
    op: BinOp,
    right: &PureExpr,
    context: &NativeReplayContext<'_>,
) -> Option<TruthValue> {
    let pointer_kind = pointer_kind_for_expr(left).max(pointer_kind_for_expr(right))?;
    let relation = context.summary_facts.iter().find_map(|fact| {
        let relation = pointer_summary_relation(fact, pointer_kind)?;
        summary_fact_matches_terms(fact, left, right).then_some(relation)
    })?;

    match (relation, op) {
        (PointerSummaryRelation::Equal, BinOp::Eq)
        | (PointerSummaryRelation::Disjoint, BinOp::Ne) => Some(TruthValue::True {
            rule: relation.rule(pointer_kind),
        }),
        (PointerSummaryRelation::Equal, BinOp::Ne)
        | (PointerSummaryRelation::Disjoint, BinOp::Eq) => Some(TruthValue::False {
            rule: relation.rule(pointer_kind),
        }),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PointerSummaryRelation {
    Equal,
    Disjoint,
}

impl PointerSummaryRelation {
    const fn rule(self, pointer_kind: PointerReplayKind) -> &'static str {
        match (self, pointer_kind) {
            (Self::Equal, PointerReplayKind::Thin) => "pointer-provenance-summary-equality",
            (Self::Equal, PointerReplayKind::Fat) => "fat-pointer-metadata-summary-equality",
            (Self::Disjoint, PointerReplayKind::Thin) => "pointer-provenance-summary-disjointness",
            (Self::Disjoint, PointerReplayKind::Fat) => "fat-pointer-metadata-summary-disjointness",
        }
    }
}

fn pointer_summary_relation(
    fact: &BundleSummaryFact,
    pointer_kind: PointerReplayKind,
) -> Option<PointerSummaryRelation> {
    match (&fact.kind, pointer_kind) {
        (
            BundleSummaryFactKind::PointerProvenanceEq { .. }
            | BundleSummaryFactKind::PointerProvenanceEqBinding { .. },
            PointerReplayKind::Thin,
        )
        | (
            BundleSummaryFactKind::FatPointerMetadataEq { .. }
            | BundleSummaryFactKind::FatPointerMetadataEqBinding { .. },
            PointerReplayKind::Fat,
        ) => Some(PointerSummaryRelation::Equal),
        (
            BundleSummaryFactKind::PointerProvenanceDisjointBinding { .. },
            PointerReplayKind::Thin,
        )
        | (
            BundleSummaryFactKind::FatPointerMetadataDisjointBinding { .. },
            PointerReplayKind::Fat,
        ) => Some(PointerSummaryRelation::Disjoint),
        _ => None,
    }
}

/// The names `summary_facts` relate: a binding fact's two names, and every
/// name free in a textual fact's endpoints. The claim decoder binds these to
/// the binders the claim opens with as written
/// ([`crate::formula::elaborate::bind_facts_to_the_written_prefix`]), so a
/// fact matched by name here meets only the value it is about.
pub(super) fn summary_fact_names(summary_facts: &[BundleSummaryFact]) -> HashSet<String> {
    let mut named: HashSet<String> = HashSet::new();
    for fact in summary_facts {
        match summary_fact_endpoints(fact) {
            Some(SummaryFactEndpoints::Binding { left, right }) => {
                named.insert(left.to_string());
                named.insert(right.to_string());
            }
            Some(SummaryFactEndpoints::Textual { left, right }) => {
                for text in [left, right] {
                    if let Ok(endpoint) = parse_contract(text.trim()) {
                        named.extend(endpoint.free_vars());
                    }
                }
            }
            None => {}
        }
    }
    named
}

fn summary_fact_matches_terms(fact: &BundleSummaryFact, left: &PureExpr, right: &PureExpr) -> bool {
    let Some(endpoints) = summary_fact_endpoints(fact) else {
        return false;
    };
    match endpoints {
        SummaryFactEndpoints::Textual {
            left: fact_left,
            right: fact_right,
        } => {
            let Ok(fact_left) = parse_contract(fact_left.trim()) else {
                return false;
            };
            let Ok(fact_right) = parse_contract(fact_right.trim()) else {
                return false;
            };
            // The fact's endpoints are text, parsed with no sorts: the terms
            // are compared as written, not as elaborated.
            let (left, right) = (&unsorted(left), &unsorted(right));
            (left == &fact_left && right == &fact_right)
                || (left == &fact_right && right == &fact_left)
        }
        SummaryFactEndpoints::Binding {
            left: fact_left,
            right: fact_right,
        } => {
            (expr_matches_summary_binding(left, fact_left)
                && expr_matches_summary_binding(right, fact_right))
                || (expr_matches_summary_binding(left, fact_right)
                    && expr_matches_summary_binding(right, fact_left))
        }
    }
}

/// `expr` with no name annotated.
fn unsorted(expr: &PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::Var(name, Some(_)) => PureExpr::Var(name, None),
        node => node,
    })
}

fn expr_matches_summary_binding(expr: &PureExpr, binding: &str) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == binding)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SummaryFactEndpoints<'a> {
    Textual { left: &'a str, right: &'a str },
    Binding { left: &'a str, right: &'a str },
}

fn summary_fact_endpoints(fact: &BundleSummaryFact) -> Option<SummaryFactEndpoints<'_>> {
    match &fact.kind {
        BundleSummaryFactKind::PointerProvenanceEq { left, right }
        | BundleSummaryFactKind::FatPointerMetadataEq { left, right } => {
            Some(SummaryFactEndpoints::Textual { left, right })
        }
        BundleSummaryFactKind::PointerProvenanceEqBinding { left, right }
        | BundleSummaryFactKind::PointerProvenanceDisjointBinding { left, right }
        | BundleSummaryFactKind::FatPointerMetadataEqBinding { left, right }
        | BundleSummaryFactKind::FatPointerMetadataDisjointBinding { left, right } => {
            Some(SummaryFactEndpoints::Binding { left, right })
        }
        BundleSummaryFactKind::Other { .. } => None,
    }
}

fn pointer_replay_diagnostic(left: &PureExpr, right: &PureExpr) -> Option<String> {
    let kind = pointer_kind_for_expr(left).max(pointer_kind_for_expr(right))?;
    match kind {
        PointerReplayKind::Thin => Some(
            "pointer replay requires alias/provenance summary evidence before non-reflexive pointer comparison can be checked"
                .to_string(),
        ),
        PointerReplayKind::Fat => Some(
            "fat-pointer metadata replay requires data-address and metadata summary evidence before non-reflexive pointer comparison can be checked"
                .to_string(),
        ),
    }
}

/// The pointer kind of the value `expr` denotes, which a summary fact must
/// match: a name at its elaborated sort, `*e` and `^e` at the sort `e`
/// references (`^p` of a `p: &mut &[Int]` is a fat pointer, and of a
/// `p: &mut Int` no pointer at all: a thin fact about it proved `^p == ^q`
/// of two integers), and `old(e)` at `e`'s. A view is no pointer: the view
/// of a value is not the value, so a fact about pointers says nothing of it.
fn pointer_kind_for_expr(expr: &PureExpr) -> Option<PointerReplayKind> {
    match expr {
        PureExpr::Var(_, sort) => sort.as_ref().and_then(pointer_kind_from_sort),
        PureExpr::Deref(operand) => dereferenced(operand, Dereference::Current)
            .referent()
            .as_ref()
            .and_then(pointer_kind_from_sort),
        PureExpr::Final(operand) => dereferenced(operand, Dereference::Final)
            .referent()
            .as_ref()
            .and_then(pointer_kind_from_sort),
        PureExpr::Old(inner) => pointer_kind_for_expr(inner),
        PureExpr::Ite(_, then_expr, else_expr) => {
            pointer_kind_for_expr(then_expr).max(pointer_kind_for_expr(else_expr))
        }
        PureExpr::Let { body, .. } => pointer_kind_for_expr(body),
        PureExpr::Bool(_)
        | PureExpr::Int(_)
        | PureExpr::Float(_)
        | PureExpr::BinOp(_, _, _)
        | PureExpr::UnOp(_, _)
        | PureExpr::View(_)
        | PureExpr::MethodCall { .. }
        | PureExpr::Forall { .. }
        | PureExpr::Exists { .. }
        | PureExpr::Match { .. }
        | PureExpr::LogicFnCall { .. }
        | PureExpr::LetAssume { .. }
        | PureExpr::LetObligation { .. }
        | PureExpr::Closure { .. } => None,
    }
}

fn pointer_kind_from_sort(sort: &ExprSort) -> Option<PointerReplayKind> {
    match sort {
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => {
            Some(pointer_kind_from_referent_sort(inner))
        }
        _ => None,
    }
}

fn pointer_kind_from_referent_sort(sort: &ExprSort) -> PointerReplayKind {
    match sort {
        ExprSort::Seq | ExprSort::FMap => PointerReplayKind::Fat,
        _ => PointerReplayKind::Thin,
    }
}

fn prove_linear_implication(antecedent: &PureExpr, consequent: &PureExpr) -> Option<TruthValue> {
    let (goal, strict_goal) = linear_goal_from_comparison(consequent)?;
    if let Some(minimum) =
        goal.minimum_with_linear_constraints(&linear_constraints_from_assumption(antecedent))
    {
        let proved = if strict_goal {
            minimum > 0
        } else {
            minimum >= 0
        };
        if proved {
            return Some(TruthValue::True {
                rule: "linear-int-implication",
            });
        }
    }

    integer_bounds_from_assumption(antecedent)?
        .into_iter()
        .find_map(|bound| {
            let minimum = goal.minimum_with_bound(&bound)?;
            let proved = if strict_goal {
                minimum > 0
            } else {
                minimum >= 0
            };
            proved.then_some(TruthValue::True {
                rule: "linear-int-implication",
            })
        })
}

fn prove_linear_comparison(left: &PureExpr, op: BinOp, right: &PureExpr) -> Option<TruthValue> {
    if matches!(op, BinOp::Eq | BinOp::Ne) && is_int_sorted(left) && is_int_sorted(right) {
        let difference = LinearInt::from_expr(left)?.sub(LinearInt::from_expr(right)?)?;
        let value = difference.constant_value()?;
        return Some(TruthValue::from_bool(
            (value == 0) == (op == BinOp::Eq),
            "linear-int-comparison",
        ));
    }
    let (difference, strict) = linear_goal(left, op, right)?;
    if !difference.terms.is_empty() {
        return None;
    }

    let proved = if strict {
        difference.constant > 0
    } else {
        difference.constant >= 0
    };
    Some(TruthValue::from_bool(proved, "linear-int-comparison"))
}

fn prove_int_arithmetic_implication(
    antecedent: &PureExpr,
    consequent: &PureExpr,
) -> Option<TruthValue> {
    let constraints = linear_constraints_from_assumption(antecedent);
    if constraints.is_empty() {
        return None;
    }

    let consequent = substitute_equalities_from_assumption(antecedent, consequent);
    prove_int_arithmetic_predicate_with_constraints(
        &consequent,
        &constraints,
        &[(antecedent, true)],
    )
}

fn prove_int_arithmetic_predicate_with_constraints(
    expr: &PureExpr,
    constraints: &[LinearConstraint],
    guards: &[(&PureExpr, bool)],
) -> Option<TruthValue> {
    // This is proof search over the existing typed formula, not evaluation at
    // selected integers. Every branch retains its enclosing linear premises.
    prove_guarded_integer_predicate(expr, true, constraints, guards, &mut 4096)?;
    Some(TruthValue::True {
        rule: "int-arithmetic-implication",
    })
}

fn prove_guarded_integer_predicate(
    expr: &PureExpr,
    expected: bool,
    constraints: &[LinearConstraint],
    guards: &[(&PureExpr, bool)],
    remaining: &mut usize,
) -> Option<()> {
    *remaining = remaining.checked_sub(1)?;
    match expr {
        PureExpr::Bool(value) => (*value == expected).then_some(()),
        PureExpr::UnOp(UnOp::Not, inner) => {
            prove_guarded_integer_predicate(inner, !expected, constraints, guards, remaining)
        }
        PureExpr::BinOp(left, op @ (BinOp::And | BinOp::Or), right) => {
            let both = expected == (*op == BinOp::And);
            if both {
                prove_guarded_integer_predicate(left, expected, constraints, guards, remaining)?;
                prove_guarded_integer_predicate(right, expected, constraints, guards, remaining)
            } else {
                prove_guarded_integer_predicate(left, expected, constraints, guards, remaining)
                    .or_else(|| {
                        prove_guarded_integer_predicate(
                            right,
                            expected,
                            constraints,
                            guards,
                            remaining,
                        )
                    })
            }
        }
        PureExpr::BinOp(guard, BinOp::Implies, conclusion) if expected => {
            let mut extended = constraints.to_vec();
            collect_guard_constraints(guard, true, &mut extended, &mut 4096);
            if matches!(eval_value(conclusion), Some(KnownValue::Bool(false)))
                && newly_contradictory_guard(&extended, constraints.len(), remaining).is_some()
            {
                return Some(());
            }
            let mut scoped = guards.to_vec();
            scoped.push((guard.as_ref(), true));
            prove_guarded_integer_predicate(conclusion, true, &extended, &scoped, remaining)
        }
        PureExpr::BinOp(left, op @ (BinOp::Eq | BinOp::Ne), right) => {
            // A Boolean equality to a literal is exactly its operand or its
            // negation. Other Boolean equalities remain outside this rule.
            let literal = match (&**left, &**right) {
                (PureExpr::Bool(value), other) | (other, PureExpr::Bool(value)) => {
                    Some((*value, other))
                }
                _ => None,
            };
            if let Some((value, other)) = literal {
                return prove_guarded_integer_predicate(
                    other,
                    expected == (value == (*op == BinOp::Eq)),
                    constraints,
                    guards,
                    remaining,
                );
            }
            if !is_int_sorted(left) || !is_int_sorted(right) {
                return None;
            }
            if expected == (*op == BinOp::Eq) {
                prove_int_arithmetic_comparison_with_constraints(
                    left,
                    BinOp::Le,
                    right,
                    constraints,
                )?;
                prove_int_arithmetic_comparison_with_constraints(
                    left,
                    BinOp::Ge,
                    right,
                    constraints,
                )?;
                Some(())
            } else {
                prove_int_arithmetic_comparison_with_constraints(
                    left,
                    BinOp::Lt,
                    right,
                    constraints,
                )
                .or_else(|| {
                    prove_int_arithmetic_comparison_with_constraints(
                        left,
                        BinOp::Gt,
                        right,
                        constraints,
                    )
                })
                .map(|_| ())
            }
        }
        PureExpr::BinOp(left, op, right)
            if matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) =>
        {
            let op = if expected {
                *op
            } else {
                negate_ordered_comparison(*op)?
            };
            if let Some(rewritten) = split_comparison_ite(left, op, right) {
                prove_guarded_integer_predicate(&rewritten, true, constraints, guards, remaining)
            } else {
                prove_int_arithmetic_comparison_with_constraints(left, op, right, constraints)
                    .map(|_| ())
                    .or_else(|| {
                        prove_ordered_from_guard_disequality(
                            left,
                            op,
                            right,
                            constraints,
                            guards,
                            remaining,
                        )
                    })
            }
        }
        _ => None,
    }
}

/// A closed false conclusion needs an actually impossible path. Check only
/// exact pairs of the existing integer constraints, charging the same search
/// budget and preserving strictness; a false conclusion alone proves nothing.
fn newly_contradictory_guard(
    constraints: &[LinearConstraint],
    first_new: usize,
    remaining: &mut usize,
) -> Option<()> {
    for constraint in constraints.get(first_new..)? {
        *remaining = remaining.checked_sub(1)?;
        let required = i128::from(constraint.strict);
        if constraint
            .expr
            .constant_value()
            .is_some_and(|value| value < required)
        {
            return Some(());
        }
        let Some(negative) = constraint.expr.clone().neg() else {
            continue;
        };
        for other in constraints {
            *remaining = remaining.checked_sub(1)?;
            let maximum = negative
                .minimum_with_linear_constraint(other)
                .and_then(i128::checked_neg);
            if maximum.is_some_and(|value| value < required) {
                return Some(());
            }
        }
    }
    None
}

/// Keep nonlinear path terms at their original syntax. A positive quotient
/// need not become a new linear variable: its actual nonzero guard and an
/// independently proved weak order suffice. No owed conjunct is an assumption.
fn prove_ordered_from_guard_disequality(
    left: &PureExpr,
    op: BinOp,
    right: &PureExpr,
    constraints: &[LinearConstraint],
    guards: &[(&PureExpr, bool)],
    remaining: &mut usize,
) -> Option<()> {
    let (greater, lesser) = match op {
        BinOp::Gt | BinOp::Ge => (left, right),
        BinOp::Lt | BinOp::Le => (right, left),
        _ => return None,
    };
    if !is_int_sorted(greater)
        || !is_int_sorted(lesser)
        || !lower_bound_int_difference(greater, lesser, constraints)
            .is_some_and(|minimum| minimum >= 0)
    {
        return None;
    }
    fn guarded_unequal(
        guard: &PureExpr,
        expected: bool,
        greater: &PureExpr,
        lesser: &PureExpr,
        remaining: &mut usize,
    ) -> Option<()> {
        *remaining = remaining.checked_sub(1)?;
        match guard {
            PureExpr::UnOp(UnOp::Not, inner) => {
                guarded_unequal(inner, !expected, greater, lesser, remaining)
            }
            PureExpr::BinOp(left, op @ (BinOp::And | BinOp::Or), right)
                if expected == (*op == BinOp::And) =>
            {
                guarded_unequal(left, expected, greater, lesser, remaining)
                    .or_else(|| guarded_unequal(right, expected, greater, lesser, remaining))
            }
            PureExpr::BinOp(left, op @ (BinOp::Eq | BinOp::Ne), right) => {
                if let (PureExpr::Bool(value), other) | (other, PureExpr::Bool(value)) =
                    (left.as_ref(), right.as_ref())
                {
                    return guarded_unequal(
                        other,
                        expected == (*value == (*op == BinOp::Eq)),
                        greater,
                        lesser,
                        remaining,
                    );
                }
                (expected != (*op == BinOp::Eq)
                    && ((left.as_ref() == greater && right.as_ref() == lesser)
                        || (right.as_ref() == greater && left.as_ref() == lesser)))
                    .then_some(())
            }
            _ => None,
        }
    }
    guards
        .iter()
        .find_map(|(guard, expected)| guarded_unequal(guard, *expected, greater, lesser, remaining))
}

/// Add only necessary consequences of the guard. Unsupported/disjunctive
/// facts contribute nothing; they never become assumed alternatives.
fn collect_guard_constraints(
    expr: &PureExpr,
    expected: bool,
    constraints: &mut Vec<LinearConstraint>,
    remaining: &mut usize,
) {
    let Some(next) = remaining.checked_sub(1) else {
        return;
    };
    *remaining = next;
    match expr {
        PureExpr::UnOp(UnOp::Not, inner) => {
            collect_guard_constraints(inner, !expected, constraints, remaining);
        }
        PureExpr::BinOp(left, op @ (BinOp::And | BinOp::Or), right)
            if expected == (*op == BinOp::And) =>
        {
            collect_guard_constraints(left, expected, constraints, remaining);
            collect_guard_constraints(right, expected, constraints, remaining);
        }
        PureExpr::BinOp(left, op @ (BinOp::Eq | BinOp::Ne), right) => match (&**left, &**right) {
            (PureExpr::Bool(value), other) | (other, PureExpr::Bool(value)) => {
                collect_guard_constraints(
                    other,
                    expected == (*value == (*op == BinOp::Eq)),
                    constraints,
                    remaining,
                );
            }
            _ if expected == (*op == BinOp::Eq) && is_int_sorted(left) && is_int_sorted(right) => {
                for op in [BinOp::Le, BinOp::Ge] {
                    if let Some((expr, strict)) = linear_goal(left, op, right) {
                        constraints.push(LinearConstraint { expr, strict });
                    }
                }
            }
            _ if is_int_sorted(left) && is_int_sorted(right) => {
                // A disequality chooses no order by itself. Refine only an
                // order independently established by the enclosing guards.
                let ordered = if lower_bound_int_difference(left, right, constraints)
                    .is_some_and(|minimum| minimum >= 0)
                {
                    Some((left, right))
                } else if lower_bound_int_difference(right, left, constraints)
                    .is_some_and(|minimum| minimum >= 0)
                {
                    Some((right, left))
                } else {
                    None
                };
                if let Some((greater, lesser)) = ordered {
                    if let Some((expr, strict)) = linear_goal(greater, BinOp::Gt, lesser) {
                        constraints.push(LinearConstraint { expr, strict });
                    }
                }
            }
            _ => {}
        },
        PureExpr::BinOp(left, op, right) if is_int_sorted(left) && is_int_sorted(right) => {
            let op = if expected {
                Some(*op)
            } else {
                negate_ordered_comparison(*op)
            };
            if let Some((expr, strict)) = op.and_then(|op| linear_goal(left, op, right)) {
                constraints.push(LinearConstraint { expr, strict });
            }
        }
        _ => {}
    }
}

fn prove_int_arithmetic_comparison_with_constraints(
    left: &PureExpr,
    op: BinOp,
    right: &PureExpr,
    constraints: &[LinearConstraint],
) -> Option<TruthValue> {
    let (minimum, strict) = match op {
        BinOp::Gt => (lower_bound_int_difference(left, right, constraints)?, true),
        BinOp::Ge => (lower_bound_int_difference(left, right, constraints)?, false),
        BinOp::Lt => (lower_bound_int_difference(right, left, constraints)?, true),
        BinOp::Le => (lower_bound_int_difference(right, left, constraints)?, false),
        _ => return None,
    };
    let proved = if strict { minimum > 0 } else { minimum >= 0 };
    proved.then_some(TruthValue::True {
        rule: "int-arithmetic-implication",
    })
}

fn substitute_equalities_from_assumption(assumption: &PureExpr, expr: &PureExpr) -> PureExpr {
    // `old(x)` denotes the entry-state value of the program variable, not an
    // application of an ordinary congruent function to its current-state
    // value. Consequently an antecedent equality such as `x == 0` must not
    // rewrite `old(x)` to `old(0)`. Keep the whole consequent opaque to this
    // current-state substitution pass when it contains an entry-state term;
    // the linear prover can still reason about explicit `old(x)` constraints
    // because `LinearInt` gives those variables a distinct namespace.
    if expr.any_recursive(|candidate| matches!(candidate, PureExpr::Old(_))) {
        return expr.clone();
    }
    let mut substitutions = HashMap::new();
    collect_equality_substitutions(assumption, &mut substitutions);
    if substitutions.is_empty() {
        expr.clone()
    } else {
        expr.substitute_capture_avoiding(&substitutions, &CaptureAvoidingSubstOptions::default())
    }
}

fn collect_equality_substitutions(expr: &PureExpr, substitutions: &mut HashMap<String, PureExpr>) {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_equality_substitutions(left, substitutions);
            collect_equality_substitutions(right, substitutions);
        }
        PureExpr::BinOp(left, BinOp::Eq, right) => {
            insert_equality_substitution(left, right, substitutions);
            insert_equality_substitution(right, left, substitutions);
        }
        _ => {}
    }
}

/// Record `candidate_var := replacement` for an equality the assumption
/// states. Only an `Int` or `Bool` name is replaced, and only by a value of
/// that same sort. Replacing a `bool` binder by an integer (`v == x` for
/// `forall<v: bool>`), or a `&bool` by a `&Int` (`p == q`), handed the
/// integer rules a goal about a value they must not read; and `==` of two
/// references does not say which: the pointer rules read it as the same
/// address, whose final values (`^p`, `^q`) need not agree.
fn insert_equality_substitution(
    candidate_var: &PureExpr,
    replacement: &PureExpr,
    substitutions: &mut HashMap<String, PureExpr>,
) {
    let PureExpr::Var(name, _) = candidate_var else {
        return;
    };
    let Some(sort) = scalar_sort(candidate_var) else {
        return;
    };
    if scalar_sort(replacement) != Some(sort) {
        return;
    }
    if contains_var(replacement, name) {
        return;
    }
    match substitutions.get(name) {
        Some(existing) if existing == replacement => {}
        Some(_) => {
            substitutions.remove(name);
        }
        None => {
            substitutions.insert(name.clone(), replacement.clone());
        }
    }
}

fn contains_var(expr: &PureExpr, name: &str) -> bool {
    match expr {
        PureExpr::Var(candidate, _) => candidate == name,
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => contains_var(inner, name),
        PureExpr::BinOp(left, _, right) => contains_var(left, name) || contains_var(right, name),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            contains_var(cond, name)
                || contains_var(then_expr, name)
                || contains_var(else_expr, name)
        }
        PureExpr::Let { var, value, body } => {
            contains_var(value, name) || (var != name && contains_var(body, name))
        }
        PureExpr::Forall { var, body, .. } | PureExpr::Exists { var, body, .. } => {
            var != name && contains_var(body, name)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            contains_var(receiver, name) || args.iter().any(|arg| contains_var(arg, name))
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(|arg| contains_var(arg, name)),
        PureExpr::Match { scrutinee, arms } => {
            contains_var(scrutinee, name) || arms.iter().any(|arm| contains_var(&arm.body, name))
        }
        PureExpr::LetAssume { assumption, body } => {
            contains_var(assumption, name) || contains_var(body, name)
        }
        PureExpr::LetObligation { obligation, body } => {
            contains_var(obligation, name) || contains_var(body, name)
        }
        PureExpr::Closure { body, .. } => contains_var(body, name),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => false,
    }
}

fn upper_bound_int_expr(expr: &PureExpr, constraints: &[LinearConstraint]) -> Option<i128> {
    if !is_int_sorted(expr) {
        return None;
    }
    if let Some(linear) = LinearInt::from_expr(expr) {
        return linear.maximum_with_linear_constraints(constraints);
    }

    match expr {
        PureExpr::BinOp(left, BinOp::Add, right) => Some(
            upper_bound_int_expr(left, constraints)?
                .checked_add(upper_bound_int_expr(right, constraints)?)?,
        ),
        PureExpr::BinOp(left, BinOp::Sub, right) => {
            upper_bound_int_difference(left, right, constraints)
        }
        PureExpr::BinOp(dividend, BinOp::Div | BinOp::DivTrunc, divisor) => {
            // `dividend_max / divisor_min` (toward zero) bounds both Euclidean
            // `Div` and truncated `DivTrunc` above when divisor > 0 and the
            // dividend's max is non-negative (for a < 0, a/b <= 0 <= the bound).
            let divisor_min = lower_bound_int_expr(divisor, constraints)?;
            let dividend_max = upper_bound_int_expr(dividend, constraints)?;
            if divisor_min > 0 && dividend_max >= 0 {
                return Some(dividend_max / divisor_min);
            }
            None
        }
        PureExpr::BinOp(_dividend, BinOp::Mod | BinOp::RemTrunc, divisor) => {
            // `(a mod b) <= b - 1` whenever `b >= 1`, for *any* dividend. This
            // holds under both SMT-LIB Euclidean `(mod a b)` and truncated
            // remainder (`a % b` lies in `(-b, b)`), so it is sound on the
            // native evaluator and the SMT backend alike. With a known divisor
            // maximum this yields a concrete upper bound.
            let divisor_min = lower_bound_int_expr(divisor, constraints)?;
            let divisor_max = upper_bound_int_expr(divisor, constraints)?;
            if divisor_min >= 1 {
                return divisor_max.checked_sub(1);
            }
            None
        }
        _ => None,
    }
}

fn upper_bound_int_difference(
    left: &PureExpr,
    right: &PureExpr,
    constraints: &[LinearConstraint],
) -> Option<i128> {
    if !is_int_sorted(left) || !is_int_sorted(right) {
        return None;
    }
    if left == right {
        return Some(0);
    }

    let difference = PureExpr::BinOp(Arc::new(left.clone()), BinOp::Sub, Arc::new(right.clone()));
    if let Some(linear) = LinearInt::from_expr(&difference) {
        return linear.maximum_with_linear_constraints(constraints);
    }

    let left_max = upper_bound_int_expr(left, constraints)?;
    let right_min = lower_bound_int_expr(right, constraints)?;
    left_max.checked_sub(right_min)
}

fn lower_bound_int_difference(
    left: &PureExpr,
    right: &PureExpr,
    constraints: &[LinearConstraint],
) -> Option<i128> {
    if !is_int_sorted(left) || !is_int_sorted(right) {
        return None;
    }
    if left == right {
        return Some(0);
    }

    let difference = PureExpr::BinOp(Arc::new(left.clone()), BinOp::Sub, Arc::new(right.clone()));
    if let Some(linear) = LinearInt::from_expr(&difference) {
        return linear.minimum_with_linear_constraints(constraints);
    }

    // For a nonnegative integer a and positive integer b, a / b <= a.
    // Keep both domain checks explicit; neither division nor a disequality
    // alone supplies positivity, including for truncated division.
    if let PureExpr::BinOp(dividend, BinOp::Div | BinOp::DivTrunc, divisor) = right {
        if left == dividend.as_ref()
            && lower_bound_int_expr(dividend, constraints).is_some_and(|minimum| minimum >= 0)
            && lower_bound_int_expr(divisor, constraints).is_some_and(|minimum| minimum >= 1)
        {
            return Some(0);
        }
    }

    // `left - (dividend % divisor)`. Under `BinOp::Mod`, `(a mod b) <= b - 1`
    // whenever `b >= 1`, so `left - (dividend % divisor) >= (left - divisor) + 1`
    // for a positive divisor. This holds under both Euclidean `(mod a b)` and
    // truncated remainder (`a % b` lies in `(-b, b)`), so it is sound on the
    // native evaluator and the SMT backend alike. Discharges the keystone
    // `(ring_head + base) % len < len` under `len >= 1`.
    if let PureExpr::BinOp(_dividend, BinOp::Mod | BinOp::RemTrunc, divisor) = right {
        let divisor_min = lower_bound_int_expr(divisor, constraints)?;
        if divisor_min >= 1 {
            let left_minus_divisor = lower_bound_int_difference(left, divisor, constraints)?;
            return left_minus_divisor.checked_add(1);
        }
    }

    if let Some(right_constant) = constant_int(right) {
        return lower_bound_int_expr(left, constraints)?.checked_sub(right_constant);
    }
    if let Some(left_constant) = constant_int(left) {
        return left_constant.checked_sub(upper_bound_int_expr(right, constraints)?);
    }

    if let PureExpr::BinOp(add_left, BinOp::Add, add_right) = left {
        if add_left.as_ref() == right {
            return lower_bound_int_expr(add_right, constraints);
        }
        if add_right.as_ref() == right {
            return lower_bound_int_expr(add_left, constraints);
        }
    }

    if let PureExpr::BinOp(r_left, BinOp::Add, r_right) = right {
        if r_left.as_ref() == left {
            return upper_bound_int_expr(r_right, constraints).and_then(i128::checked_neg);
        }
        if r_right.as_ref() == left {
            return upper_bound_int_expr(r_left, constraints).and_then(i128::checked_neg);
        }
        // Handle hi - (lo + (hi - lo) / 2)
        if let Some(linear_diff) = LinearInt::from_expr(&PureExpr::BinOp(
            Arc::new(left.clone()),
            BinOp::Sub,
            r_left.clone(),
        )) {
            if let PureExpr::BinOp(dividend, BinOp::Div | BinOp::DivTrunc, divisor) =
                r_right.as_ref()
            {
                if let Some(linear_dividend) = LinearInt::from_expr(dividend) {
                    if linear_diff == linear_dividend {
                        let x_min = linear_diff.minimum_with_linear_constraints(constraints)?;
                        let k_min = lower_bound_int_expr(divisor, constraints)?;
                        if x_min >= 0 && k_min >= 1 {
                            return Some(0);
                        }
                    }
                }
            }
        }
    }

    None
}

fn lower_bound_int_expr(expr: &PureExpr, constraints: &[LinearConstraint]) -> Option<i128> {
    if !is_int_sorted(expr) {
        return None;
    }
    if let Some(linear) = LinearInt::from_expr(expr) {
        return linear.minimum_with_linear_constraints(constraints);
    }

    match expr {
        PureExpr::BinOp(left, BinOp::Add, right) => lower_bound_int_expr(left, constraints)?
            .checked_add(lower_bound_int_expr(right, constraints)?),
        PureExpr::BinOp(left, BinOp::Sub, right) => {
            lower_bound_int_difference(left, right, constraints)
        }
        PureExpr::BinOp(left, BinOp::Mul, right) => {
            if let Some(factor) = constant_int(left) {
                return lower_bound_scaled_expr(factor, right, constraints);
            }
            if let Some(factor) = constant_int(right) {
                return lower_bound_scaled_expr(factor, left, constraints);
            }
            None
        }
        PureExpr::BinOp(dividend, BinOp::Div | BinOp::DivTrunc, divisor) => {
            // `a / b >= 0` for a non-negative dividend and positive divisor —
            // true for both Euclidean and truncated (toward-zero) division.
            let divisor_min = lower_bound_int_expr(divisor, constraints)?;
            let dividend_min = lower_bound_int_expr(dividend, constraints)?;
            (divisor_min > 0 && dividend_min >= 0).then_some(0)
        }
        PureExpr::BinOp(dividend, BinOp::Mod | BinOp::RemTrunc, divisor) => {
            // `a % b >= 0` for a non-negative dividend and positive divisor —
            // true for both Euclidean and truncated (sign-of-dividend) remainder.
            let divisor_min = lower_bound_int_expr(divisor, constraints)?;
            let dividend_min = lower_bound_int_expr(dividend, constraints)?;
            (divisor_min > 0 && dividend_min >= 0).then_some(0)
        }
        PureExpr::Let { var, value, body } => lower_bound_int_expr(
            &inline_let_binding_for_native_replay(var, value, body)?,
            constraints,
        ),
        // A compound entry-state expression must not inherit bounds on its
        // current-state variables. `LinearInt::from_expr` above deliberately
        // supports the sound atomic `old(x)` case with a distinct symbol; all
        // other `old(...)` shapes remain outside this native bound fragment.
        PureExpr::Old(_) => None,
        _ => None,
    }
}

fn lower_bound_scaled_expr(
    factor: i128,
    expr: &PureExpr,
    constraints: &[LinearConstraint],
) -> Option<i128> {
    if factor < 0 {
        return None;
    }
    lower_bound_int_expr(expr, constraints)?.checked_mul(factor)
}

fn constant_int(expr: &PureExpr) -> Option<i128> {
    if let Some(value) = LinearInt::from_expr(expr).and_then(|linear| linear.constant_value()) {
        return Some(value);
    }
    match eval_value(expr)? {
        KnownValue::Int(value) => Some(i128::from(value)),
        KnownValue::Bool(_) => None,
    }
}

fn linear_goal_from_comparison(expr: &PureExpr) -> Option<(LinearInt, bool)> {
    let PureExpr::BinOp(left, op, right) = expr else {
        return None;
    };
    linear_goal(left, *op, right)
}

fn linear_goal(left: &PureExpr, op: BinOp, right: &PureExpr) -> Option<(LinearInt, bool)> {
    if !is_int_sorted(left) || !is_int_sorted(right) {
        return None;
    }
    match op {
        BinOp::Gt => Some((
            LinearInt::from_expr(left)?.sub(LinearInt::from_expr(right)?)?,
            true,
        )),
        BinOp::Ge => Some((
            LinearInt::from_expr(left)?.sub(LinearInt::from_expr(right)?)?,
            false,
        )),
        BinOp::Lt => Some((
            LinearInt::from_expr(right)?.sub(LinearInt::from_expr(left)?)?,
            true,
        )),
        BinOp::Le => Some((
            LinearInt::from_expr(right)?.sub(LinearInt::from_expr(left)?)?,
            false,
        )),
        _ => None,
    }
}

fn integer_bound_from_comparison(expr: &PureExpr) -> Option<IntegerBound> {
    let (goal, strict) = linear_goal_from_comparison(expr)?;
    let (var, coefficient) = single_linear_term(&goal.terms)?;
    match coefficient {
        1 => {
            let mut value = goal.constant.checked_neg()?;
            if strict {
                value = value.checked_add(1)?;
            }
            Some(IntegerBound {
                var: var.to_string(),
                kind: IntegerBoundKind::Lower,
                value,
            })
        }
        -1 => {
            let mut value = goal.constant;
            if strict {
                value = value.checked_sub(1)?;
            }
            Some(IntegerBound {
                var: var.to_string(),
                kind: IntegerBoundKind::Upper,
                value,
            })
        }
        _ => None,
    }
}

fn integer_bounds_from_assumption(expr: &PureExpr) -> Option<Vec<IntegerBound>> {
    if let PureExpr::BinOp(left, BinOp::And, right) = expr {
        let mut bounds = Vec::new();
        collect_integer_bounds(left, &mut bounds);
        collect_integer_bounds(right, &mut bounds);
        (!bounds.is_empty()).then_some(bounds)
    } else {
        let normalized = denegate_ordered_integer_comparison(expr);
        integer_bound_from_comparison(normalized.as_ref().unwrap_or(expr)).map(|bound| vec![bound])
    }
}

fn collect_integer_bounds(expr: &PureExpr, bounds: &mut Vec<IntegerBound>) {
    match expr {
        PureExpr::BinOp(left, BinOp::And, right) => {
            collect_integer_bounds(left, bounds);
            collect_integer_bounds(right, bounds);
        }
        _ => {
            if let Some(normalized) = denegate_ordered_integer_comparison(expr) {
                collect_integer_bounds(&normalized, bounds);
            } else if let Some(bound) = integer_bound_from_comparison(expr) {
                bounds.push(bound);
            }
        }
    }
}

fn linear_constraints_from_assumption(expr: &PureExpr) -> Vec<LinearConstraint> {
    let mut constraints = Vec::new();
    collect_linear_constraints(expr, &mut constraints);
    constraints
}

fn collect_linear_constraints(expr: &PureExpr, constraints: &mut Vec<LinearConstraint>) {
    collect_guard_constraints(expr, true, constraints, &mut 4096);
}

fn single_linear_term(terms: &BTreeMap<String, i128>) -> Option<(&str, i128)> {
    let mut iter = terms.iter();
    let (var, coefficient) = iter.next()?;
    iter.next()
        .is_none()
        .then_some((var.as_str(), *coefficient))
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LinearConstraint {
    expr: LinearInt,
    strict: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct IntegerBound {
    var: String,
    kind: IntegerBoundKind,
    value: i128,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IntegerBoundKind {
    Lower,
    Upper,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LinearInt {
    constant: i128,
    terms: BTreeMap<String, i128>,
}

impl LinearInt {
    fn constant(value: i128) -> Self {
        Self {
            constant: value,
            terms: BTreeMap::new(),
        }
    }

    fn var(name: String) -> Self {
        let mut terms = BTreeMap::new();
        terms.insert(name, 1);
        Self { constant: 0, terms }
    }

    fn from_expr(expr: &PureExpr) -> Option<Self> {
        match expr {
            PureExpr::Int(value) => Some(Self::constant(i128::from(*value))),
            PureExpr::Var(name, sort)
                if sort
                    .as_ref()
                    .is_none_or(|sort| *sort == crate::formula::ExprSort::Int) =>
            {
                Some(Self::var(name.clone()))
            }
            PureExpr::UnOp(UnOp::Neg, inner) => Self::from_expr(inner)?.neg(),
            PureExpr::BinOp(left, BinOp::Add, right) => {
                Self::from_expr(left)?.add(Self::from_expr(right)?)
            }
            PureExpr::BinOp(left, BinOp::Sub, right) => {
                Self::from_expr(left)?.sub(Self::from_expr(right)?)
            }
            PureExpr::BinOp(left, BinOp::Mul, right) => {
                let left = Self::from_expr(left)?;
                let right = Self::from_expr(right)?;
                if let Some(factor) = left.constant_value() {
                    right.mul_constant(factor)
                } else if let Some(factor) = right.constant_value() {
                    left.mul_constant(factor)
                } else {
                    None
                }
            }
            PureExpr::BinOp(left, BinOp::Div | BinOp::DivTrunc, right)
                if constant_int(right) == Some(1) =>
            {
                Self::from_expr(left)
            }
            PureExpr::Old(inner) => match inner.as_ref() {
                PureExpr::Var(name, sort)
                    if sort
                        .as_ref()
                        .is_none_or(|sort| *sort == crate::formula::ExprSort::Int) =>
                {
                    Some(Self::var(format!("old({name})")))
                }
                _ => None,
            },
            PureExpr::Let { var, value, body } => {
                Self::from_expr(&inline_let_binding_for_native_replay(var, value, body)?)
            }
            _ => None,
        }
    }

    fn constant_value(&self) -> Option<i128> {
        self.terms.is_empty().then_some(self.constant)
    }

    fn add(self, other: Self) -> Option<Self> {
        let mut result = Self {
            constant: self.constant.checked_add(other.constant)?,
            terms: self.terms,
        };
        for (var, coefficient) in other.terms {
            result.add_term(var, coefficient)?;
        }
        Some(result)
    }

    fn sub(self, other: Self) -> Option<Self> {
        self.add(other.neg()?)
    }

    fn neg(mut self) -> Option<Self> {
        self.constant = self.constant.checked_neg()?;
        for coefficient in self.terms.values_mut() {
            *coefficient = coefficient.checked_neg()?;
        }
        Some(self)
    }

    fn add_term(&mut self, var: String, coefficient: i128) -> Option<()> {
        let updated = self
            .terms
            .get(&var)
            .copied()
            .unwrap_or(0)
            .checked_add(coefficient)?;
        if updated == 0 {
            self.terms.remove(&var);
        } else {
            self.terms.insert(var, updated);
        }
        Some(())
    }

    fn mul_constant(mut self, factor: i128) -> Option<Self> {
        self.constant = self.constant.checked_mul(factor)?;
        for coefficient in self.terms.values_mut() {
            *coefficient = coefficient.checked_mul(factor)?;
        }
        self.terms.retain(|_, coefficient| *coefficient != 0);
        Some(self)
    }

    fn minimum_with_bound(&self, bound: &IntegerBound) -> Option<i128> {
        let (var, coefficient) = single_linear_term(&self.terms)?;
        if var != bound.var {
            return None;
        }

        let uses_bound = match bound.kind {
            IntegerBoundKind::Lower => coefficient > 0,
            IntegerBoundKind::Upper => coefficient < 0,
        };
        if !uses_bound {
            return None;
        }

        coefficient
            .checked_mul(bound.value)?
            .checked_add(self.constant)
    }

    fn maximum_with_linear_constraints(&self, constraints: &[LinearConstraint]) -> Option<i128> {
        if self.terms.is_empty() {
            return Some(self.constant);
        }
        let mut neg = self.clone();
        neg.constant = neg.constant.checked_neg()?;
        for val in neg.terms.values_mut() {
            *val = (*val).checked_neg()?;
        }
        neg.minimum_with_linear_constraints(constraints)
            .and_then(i128::checked_neg)
    }

    fn minimum_with_linear_constraints(&self, constraints: &[LinearConstraint]) -> Option<i128> {
        if self.terms.is_empty() {
            return Some(self.constant);
        }
        let direct = constraints
            .iter()
            .filter_map(|constraint| self.minimum_with_linear_constraint(constraint))
            .max();
        direct
            .into_iter()
            .chain(self.minimum_with_constraint_combinations(constraints, &mut 4096, 0))
            .max()
    }

    /// Derive bounds by nonnegative integer combinations of the original
    /// constraints. Each step preserves `self = scale * constraint + residual`.
    /// A failed search proves nothing about satisfiability or a lower bound.
    fn minimum_with_constraint_combinations(
        &self,
        constraints: &[LinearConstraint],
        remaining: &mut usize,
        depth: usize,
    ) -> Option<i128> {
        if self.terms.is_empty() {
            return Some(self.constant);
        }
        if depth >= 64 {
            return None;
        }
        let mut best = None;
        for constraint in constraints {
            let Some(next) = remaining.checked_sub(1) else {
                return best;
            };
            *remaining = next;
            if let Some(bound) = self.minimum_with_linear_constraint(constraint) {
                best = best.into_iter().chain(Some(bound)).max();
            }
        }
        for constraint in constraints {
            for (name, coefficient) in &self.terms {
                let Some(next) = remaining.checked_sub(1) else {
                    return best;
                };
                *remaining = next;
                let Some(divisor) = constraint.expr.terms.get(name) else {
                    continue;
                };
                if coefficient.checked_rem(*divisor) != Some(0) {
                    continue;
                }
                let Some(scale) = coefficient.checked_div(*divisor).filter(|scale| *scale > 0)
                else {
                    continue;
                };
                let Some(residual) = constraint
                    .expr
                    .clone()
                    .mul_constant(scale)
                    .and_then(|scaled| self.clone().sub(scaled))
                else {
                    continue;
                };
                let Some(bound) = residual
                    .minimum_with_constraint_combinations(constraints, remaining, depth + 1)
                    .and_then(|bound| {
                        bound.checked_add(scale.checked_mul(i128::from(constraint.strict))?)
                    })
                else {
                    continue;
                };
                best = best.into_iter().chain(Some(bound)).max();
            }
        }
        best
    }

    fn minimum_with_linear_constraint(&self, constraint: &LinearConstraint) -> Option<i128> {
        let factor = positive_term_scale(&self.terms, &constraint.expr.terms)?;
        let residual = self
            .constant
            .checked_sub(constraint.expr.constant.checked_mul(factor)?)?;
        let constraint_min = i128::from(constraint.strict);
        factor.checked_mul(constraint_min)?.checked_add(residual)
    }
}

fn positive_term_scale(
    goal_terms: &BTreeMap<String, i128>,
    constraint_terms: &BTreeMap<String, i128>,
) -> Option<i128> {
    if constraint_terms.is_empty() || goal_terms.len() != constraint_terms.len() {
        return None;
    }

    let mut scale = None;
    for (var, constraint_coefficient) in constraint_terms {
        if *constraint_coefficient == 0 {
            return None;
        }
        let goal_coefficient = *goal_terms.get(var)?;
        if goal_coefficient.checked_rem(*constraint_coefficient)? != 0 {
            return None;
        }
        let candidate = goal_coefficient.checked_div(*constraint_coefficient)?;
        if candidate <= 0 {
            return None;
        }
        match scale {
            Some(scale) if scale != candidate => return None,
            Some(_) => {}
            None => scale = Some(candidate),
        }
    }
    scale
}

fn prove_bitwise_comparison(left: &PureExpr, op: BinOp, right: &PureExpr) -> Option<TruthValue> {
    if !matches!(op, BinOp::Eq | BinOp::Ne) {
        return None;
    }
    if !is_int_sorted(left) || !is_int_sorted(right) {
        return None;
    }
    if !contains_bitwise_expr(left) && !contains_bitwise_expr(right) {
        return None;
    }

    let left = normalize_bitwise_identities(left);
    let right = normalize_bitwise_identities(right);
    if left == right {
        return Some(TruthValue::from_bool(
            op == BinOp::Eq,
            "checked-bitwise-identity",
        ));
    }

    match (eval_value(&left), eval_value(&right)) {
        (Some(left), Some(right)) => Some(compare_known_values_with_int_rule(
            left,
            op,
            right,
            "checked-bitwise-constant-comparison",
        )),
        _ => None,
    }
}

fn checked_bitwise_replay_diagnostic(expr: &PureExpr) -> Option<String> {
    match expr {
        PureExpr::BinOp(left, BinOp::Shl | BinOp::Shr, right) => {
            if checked_shift_amount_from_expr(right).is_none() {
                return Some(
                    "bitwise shift count is not a known checked i64 shift amount".to_string(),
                );
            }
            checked_bitwise_replay_diagnostic(left)
                .or_else(|| checked_bitwise_replay_diagnostic(right))
        }
        PureExpr::BinOp(left, _, right) => checked_bitwise_replay_diagnostic(left)
            .or_else(|| checked_bitwise_replay_diagnostic(right)),
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => checked_bitwise_replay_diagnostic(inner),
        PureExpr::Ite(cond, then_expr, else_expr) => checked_bitwise_replay_diagnostic(cond)
            .or_else(|| checked_bitwise_replay_diagnostic(then_expr))
            .or_else(|| checked_bitwise_replay_diagnostic(else_expr)),
        PureExpr::Forall { body, .. }
        | PureExpr::Exists { body, .. }
        | PureExpr::Closure { body, .. } => checked_bitwise_replay_diagnostic(body),
        PureExpr::Let { value, body, .. } => checked_bitwise_replay_diagnostic(value)
            .or_else(|| checked_bitwise_replay_diagnostic(body)),
        PureExpr::LetAssume { assumption, body } => checked_bitwise_replay_diagnostic(assumption)
            .or_else(|| checked_bitwise_replay_diagnostic(body)),
        PureExpr::LetObligation { obligation, body } => {
            checked_bitwise_replay_diagnostic(obligation)
                .or_else(|| checked_bitwise_replay_diagnostic(body))
        }
        PureExpr::Match { scrutinee, arms } => checked_bitwise_replay_diagnostic(scrutinee)
            .or_else(|| {
                arms.iter()
                    .find_map(|arm| checked_bitwise_replay_diagnostic(&arm.body))
            }),
        PureExpr::MethodCall { receiver, args, .. } => checked_bitwise_replay_diagnostic(receiver)
            .or_else(|| args.iter().find_map(checked_bitwise_replay_diagnostic)),
        PureExpr::LogicFnCall { args, .. } => {
            args.iter().find_map(checked_bitwise_replay_diagnostic)
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => None,
    }
}

fn checked_shift_amount_from_expr(expr: &PureExpr) -> Option<u32> {
    match eval_value(expr)? {
        KnownValue::Int(amount) => checked_shift_amount(amount),
        KnownValue::Bool(_) => None,
    }
}

fn checked_shift_amount(amount: i64) -> Option<u32> {
    u32::try_from(amount)
        .ok()
        .filter(|amount| *amount < i64::BITS)
}

fn contains_bitwise_expr(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::BinOp(left, op, right) => {
            matches!(
                op,
                BinOp::Shl | BinOp::Shr | BinOp::BitAnd | BinOp::BitXor | BinOp::BitOr
            ) || contains_bitwise_expr(left)
                || contains_bitwise_expr(right)
        }
        PureExpr::UnOp(UnOp::BitNot, _) => true,
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => contains_bitwise_expr(inner),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            contains_bitwise_expr(cond)
                || contains_bitwise_expr(then_expr)
                || contains_bitwise_expr(else_expr)
        }
        PureExpr::Forall { body, .. }
        | PureExpr::Exists { body, .. }
        | PureExpr::Closure { body, .. } => contains_bitwise_expr(body),
        PureExpr::Let { value, body, .. } => {
            contains_bitwise_expr(value) || contains_bitwise_expr(body)
        }
        PureExpr::LetAssume { assumption, body } => {
            contains_bitwise_expr(assumption) || contains_bitwise_expr(body)
        }
        PureExpr::LetObligation { obligation, body } => {
            contains_bitwise_expr(obligation) || contains_bitwise_expr(body)
        }
        PureExpr::Match { scrutinee, arms } => {
            contains_bitwise_expr(scrutinee)
                || arms.iter().any(|arm| contains_bitwise_expr(&arm.body))
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            contains_bitwise_expr(receiver) || args.iter().any(contains_bitwise_expr)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(contains_bitwise_expr),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => false,
    }
}

fn normalize_bitwise_identities(expr: &PureExpr) -> PureExpr {
    if let Some(KnownValue::Int(value)) = eval_value(expr) {
        return PureExpr::Int(value);
    }

    match expr {
        PureExpr::BinOp(left, op, right) => {
            let left = normalize_bitwise_identities(left);
            let right = normalize_bitwise_identities(right);
            normalize_bitwise_binary(left, *op, right)
        }
        PureExpr::UnOp(UnOp::BitNot, inner) => {
            let inner = normalize_bitwise_identities(inner);
            if let PureExpr::UnOp(UnOp::BitNot, nested) = &inner {
                return nested.as_ref().clone();
            }
            PureExpr::UnOp(UnOp::BitNot, Arc::new(inner))
        }
        PureExpr::UnOp(op, inner) => {
            PureExpr::UnOp(*op, Arc::new(normalize_bitwise_identities(inner)))
        }
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(normalize_bitwise_identities(cond)),
            Arc::new(normalize_bitwise_identities(then_expr)),
            Arc::new(normalize_bitwise_identities(else_expr)),
        ),
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var: var.clone(),
            value: Arc::new(normalize_bitwise_identities(value)),
            body: Arc::new(normalize_bitwise_identities(body)),
        },
        _ => expr.clone(),
    }
}

fn normalize_bitwise_binary(left: PureExpr, op: BinOp, right: PureExpr) -> PureExpr {
    match op {
        BinOp::BitAnd => {
            if is_int_literal(&left, 0) || is_int_literal(&right, 0) {
                return PureExpr::Int(0);
            }
            if is_int_literal(&left, -1) {
                return right;
            }
            if is_int_literal(&right, -1) || left == right {
                return left;
            }
        }
        BinOp::BitOr => {
            if is_int_literal(&left, -1) || is_int_literal(&right, -1) {
                return PureExpr::Int(-1);
            }
            if is_int_literal(&left, 0) {
                return right;
            }
            if is_int_literal(&right, 0) || left == right {
                return left;
            }
        }
        BinOp::BitXor => {
            if left == right {
                return PureExpr::Int(0);
            }
            if is_int_literal(&left, 0) {
                return right;
            }
            if is_int_literal(&right, 0) {
                return left;
            }
        }
        BinOp::Shl | BinOp::Shr if is_int_literal(&right, 0) => {
            return left;
        }
        _ => {}
    }

    PureExpr::BinOp(Arc::new(left), op, Arc::new(right))
}

fn is_int_literal(expr: &PureExpr, value: i64) -> bool {
    matches!(expr, PureExpr::Int(candidate) if *candidate == value)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum KnownValue {
    Bool(bool),
    Int(i64),
}

fn eval_value(expr: &PureExpr) -> Option<KnownValue> {
    match expr {
        PureExpr::Bool(value) => Some(KnownValue::Bool(*value)),
        PureExpr::Int(value) => Some(KnownValue::Int(*value)),
        PureExpr::UnOp(UnOp::Not, inner) => match eval_value(inner)? {
            KnownValue::Bool(value) => Some(KnownValue::Bool(!value)),
            KnownValue::Int(_) => None,
        },
        PureExpr::UnOp(UnOp::Neg, inner) => match eval_value(inner)? {
            KnownValue::Int(value) => value.checked_neg().map(KnownValue::Int),
            KnownValue::Bool(_) => None,
        },
        PureExpr::UnOp(UnOp::BitNot, inner) => match eval_value(inner)? {
            KnownValue::Int(value) => Some(KnownValue::Int(!value)),
            KnownValue::Bool(_) => None,
        },
        PureExpr::BinOp(left, op, right) => eval_binary_value(left, *op, right),
        PureExpr::Ite(cond, then_expr, else_expr) => match eval_value(cond)? {
            KnownValue::Bool(true) => eval_value(then_expr),
            KnownValue::Bool(false) => eval_value(else_expr),
            KnownValue::Int(_) => None,
        },
        PureExpr::Let { var, value, body } => {
            eval_value(&inline_let_binding_for_native_replay(var, value, body)?)
        }
        PureExpr::Old(inner) => eval_value(inner),
        PureExpr::Float(_)
        | PureExpr::Var(_, _)
        | PureExpr::Deref(_)
        | PureExpr::Final(_)
        | PureExpr::View(_)
        | PureExpr::MethodCall { .. }
        | PureExpr::Forall { .. }
        | PureExpr::Exists { .. }
        | PureExpr::Match { .. }
        | PureExpr::LogicFnCall { .. }
        | PureExpr::LetAssume { .. }
        | PureExpr::LetObligation { .. }
        | PureExpr::Closure { .. } => None,
    }
}

fn eval_binary_value(left: &PureExpr, op: BinOp, right: &PureExpr) -> Option<KnownValue> {
    match op {
        BinOp::Add => eval_int_binop(left, right, i64::checked_add),
        BinOp::Sub => eval_int_binop(left, right, i64::checked_sub),
        BinOp::Mul => eval_int_binop(left, right, i64::checked_mul),
        // `Div`/`Mod` are EUCLIDEAN; only the `*Trunc` ops truncate.
        BinOp::Div => eval_int_binop(left, right, i64::checked_div_euclid),
        BinOp::Mod => eval_int_binop(left, right, i64::checked_rem_euclid),
        // Truncated machine ops: Rust's `/`/`%` are exactly i64 checked_div/rem
        // (toward-zero, remainder takes the dividend's sign).
        BinOp::DivTrunc => eval_int_binop(left, right, i64::checked_div),
        BinOp::RemTrunc => eval_int_binop(left, right, i64::checked_rem),
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            let left = eval_value(left)?;
            let right = eval_value(right)?;
            match compare_known_values(left, op, right) {
                TruthValue::True { .. } => Some(KnownValue::Bool(true)),
                TruthValue::False { .. } => Some(KnownValue::Bool(false)),
                TruthValue::Unknown { .. } => None,
            }
        }
        BinOp::And | BinOp::Or | BinOp::Implies => {
            let left = eval_value(left)?;
            let right = eval_value(right)?;
            eval_bool_binop(left, op, right)
        }
        BinOp::Shl => eval_shift_binop(left, right, i64::checked_shl),
        BinOp::Shr => eval_shift_binop(left, right, i64::checked_shr),
        BinOp::BitAnd => eval_int_binop(left, right, |left, right| Some(left & right)),
        BinOp::BitXor => eval_int_binop(left, right, |left, right| Some(left ^ right)),
        BinOp::BitOr => eval_int_binop(left, right, |left, right| Some(left | right)),
    }
}

fn eval_int_binop(
    left: &PureExpr,
    right: &PureExpr,
    op: fn(i64, i64) -> Option<i64>,
) -> Option<KnownValue> {
    match (eval_value(left)?, eval_value(right)?) {
        (KnownValue::Int(left), KnownValue::Int(right)) => op(left, right).map(KnownValue::Int),
        _ => None,
    }
}

fn eval_shift_binop(
    left: &PureExpr,
    right: &PureExpr,
    op: fn(i64, u32) -> Option<i64>,
) -> Option<KnownValue> {
    match (eval_value(left)?, eval_value(right)?) {
        (KnownValue::Int(left), KnownValue::Int(right)) => {
            op(left, checked_shift_amount(right)?).map(KnownValue::Int)
        }
        _ => None,
    }
}

fn eval_bool_binop(left: KnownValue, op: BinOp, right: KnownValue) -> Option<KnownValue> {
    let (KnownValue::Bool(left), KnownValue::Bool(right)) = (left, right) else {
        return None;
    };
    let value = match op {
        BinOp::And => left && right,
        BinOp::Or => left || right,
        BinOp::Implies => !left || right,
        _ => return None,
    };
    Some(KnownValue::Bool(value))
}

fn compare_known_values(left: KnownValue, op: BinOp, right: KnownValue) -> TruthValue {
    compare_known_values_with_int_rule(left, op, right, "int-constant-comparison")
}

fn compare_known_values_with_int_rule(
    left: KnownValue,
    op: BinOp,
    right: KnownValue,
    int_rule: &'static str,
) -> TruthValue {
    match (left, right) {
        (KnownValue::Bool(left), KnownValue::Bool(right)) => match op {
            BinOp::Eq => TruthValue::from_bool(left == right, "bool-eq"),
            BinOp::Ne => TruthValue::from_bool(left != right, "bool-ne"),
            _ => TruthValue::unknown("non-equality comparison over boolean constants"),
        },
        (KnownValue::Int(left), KnownValue::Int(right)) => {
            compare_integer_constants(i128::from(left), op, i128::from(right), int_rule)
        }
        _ => TruthValue::unknown("comparison mixes incompatible constant sorts"),
    }
}

fn compare_integer_constants(left: i128, op: BinOp, right: i128, rule: &'static str) -> TruthValue {
    let value = match op {
        BinOp::Eq => left == right,
        BinOp::Ne => left != right,
        BinOp::Lt => left < right,
        BinOp::Le => left <= right,
        BinOp::Gt => left > right,
        BinOp::Ge => left >= right,
        _ => unreachable!("comparison operators handled by caller"),
    };
    TruthValue::from_bool(value, rule)
}

#[cfg(test)]
mod guarded_ite_comparison_tests {
    use super::*;
    use crate::formula::FloatBits;

    fn int_var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), Some(ExprSort::Int))
    }

    fn bool_var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), Some(ExprSort::Bool))
    }

    fn bin(left: PureExpr, op: BinOp, right: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(left), op, Arc::new(right))
    }

    fn not(expr: PureExpr) -> PureExpr {
        PureExpr::UnOp(UnOp::Not, Arc::new(expr))
    }

    fn ite(cond: PureExpr, then_expr: PureExpr, else_expr: PureExpr) -> PureExpr {
        PureExpr::Ite(Arc::new(cond), Arc::new(then_expr), Arc::new(else_expr))
    }

    fn verified(predicate: &PureExpr) -> bool {
        matches!(
            prove_native_pure_predicate(predicate, NativeClaimFormat::TrustWpPureExprV1, &[],),
            NativePureProofOutcome::Verified(_)
        )
    }

    fn clamp(candidate: PureExpr, lo: PureExpr, hi: PureExpr) -> PureExpr {
        ite(
            bin(candidate.clone(), BinOp::Lt, lo.clone()),
            lo,
            ite(bin(candidate.clone(), BinOp::Gt, hi.clone()), hi, candidate),
        )
    }

    #[test]
    fn proves_total_ite_comparison_only_when_both_arms_hold() {
        let condition = bool_var("condition");
        let true_predicate = bin(
            ite(condition.clone(), PureExpr::Int(1), PureExpr::Int(2)),
            BinOp::Ge,
            PureExpr::Int(1),
        );
        assert!(verified(&true_predicate));

        let false_predicate = bin(
            ite(condition, PureExpr::Int(1), PureExpr::Int(0)),
            BinOp::Ge,
            PureExpr::Int(1),
        );
        assert!(
            !verified(&false_predicate),
            "one false conditional arm must keep the result non-authoritative"
        );

        let right_operand_predicate = bin(
            PureExpr::Int(2),
            BinOp::Le,
            ite(
                bool_var("right_condition"),
                PureExpr::Int(2),
                PureExpr::Int(3),
            ),
        );
        assert!(
            verified(&right_operand_predicate),
            "the symmetric right-operand rewrite must retain both guards"
        );
    }

    #[test]
    fn proves_nested_clamp_bounds_under_the_enclosing_precondition() {
        let candidate = int_var("candidate");
        let lo = int_var("lo");
        let hi = int_var("hi");
        let result = clamp(candidate, lo.clone(), hi.clone());
        let postcondition = bin(
            bin(lo.clone(), BinOp::Le, result.clone()),
            BinOp::And,
            bin(result, BinOp::Le, hi.clone()),
        );
        let predicate = bin(bin(lo, BinOp::Le, hi), BinOp::Implies, postcondition);

        assert!(
            verified(&predicate),
            "the enclosing bound and each dominating branch guard prove the clamp range"
        );
    }

    #[test]
    fn rejects_a_false_strict_clamp_bound() {
        let candidate = int_var("candidate");
        let lo = int_var("lo");
        let hi = int_var("hi");
        let result = clamp(candidate, lo.clone(), hi.clone());
        let predicate = bin(
            bin(lo, BinOp::Le, hi.clone()),
            BinOp::Implies,
            bin(result, BinOp::Lt, hi),
        );

        assert!(
            !verified(&predicate),
            "the upper clamp arm equals `hi`, so a strict upper bound is false"
        );
    }

    #[test]
    fn projects_negated_order_only_for_the_integer_fragment() {
        let x = int_var("x");
        let lo = int_var("lo");
        let integer_predicate = bin(
            not(bin(x.clone(), BinOp::Lt, lo.clone())),
            BinOp::Implies,
            bin(lo, BinOp::Le, x),
        );
        assert!(verified(&integer_predicate));

        let float_x = PureExpr::Var(
            "float_x".to_string(),
            Some(ExprSort::Float(crate::formula::FloatWidth::F64)),
        );
        let float_y = PureExpr::Var(
            "float_y".to_string(),
            Some(ExprSort::Float(crate::formula::FloatWidth::F64)),
        );
        let float_predicate = bin(
            not(bin(float_x.clone(), BinOp::Lt, float_y.clone())),
            BinOp::Implies,
            bin(float_x, BinOp::Ge, float_y),
        );
        assert!(
            !verified(&float_predicate),
            "ordered-negation projection is intentionally integer-only"
        );
    }

    #[test]
    fn rejects_equality_negation_and_nan_order_projection() {
        let x = int_var("x");
        let y = int_var("y");
        let equality_predicate = bin(
            not(bin(x.clone(), BinOp::Eq, y.clone())),
            BinOp::Implies,
            bin(x, BinOp::Lt, y),
        );
        assert!(
            !verified(&equality_predicate),
            "disequality does not choose either direction of an integer order"
        );

        assert_eq!(negate_ordered_comparison(BinOp::Lt), Some(BinOp::Ge));
        assert_eq!(negate_ordered_comparison(BinOp::Gt), Some(BinOp::Le));
        assert_eq!(negate_ordered_comparison(BinOp::Le), Some(BinOp::Gt));
        assert_eq!(negate_ordered_comparison(BinOp::Ge), Some(BinOp::Lt));
        assert_eq!(negate_ordered_comparison(BinOp::Eq), None);
        assert_eq!(negate_ordered_comparison(BinOp::Ne), None);

        let nan = PureExpr::Float(FloatBits::from_f64(f64::NAN));
        let zero = PureExpr::Float(FloatBits::from_f64(0.0));
        let nan_predicate = bin(
            not(bin(nan.clone(), BinOp::Lt, zero.clone())),
            BinOp::Implies,
            bin(nan, BinOp::Ge, zero),
        );
        assert!(
            !verified(&nan_predicate),
            "the direct replay API must not turn a NaN negated order into its converse"
        );
    }
}

#[cfg(test)]
mod modulo_upper_bound_tests {
    use super::*;

    fn prove(text: &str) -> NativePureProofOutcome {
        let predicate = parse_contract(text).expect("parse contract predicate");
        prove_native_pure_predicate(&predicate, NativeClaimFormat::TrustWpPureExprV1, &[])
    }

    fn is_verified(outcome: &NativePureProofOutcome) -> bool {
        matches!(outcome, NativePureProofOutcome::Verified(_))
    }

    #[test]
    fn does_not_apply_current_bound_inside_compound_old_expression() {
        let outcome = prove("x >= 0 ==> old(x + 1) >= 1");
        assert!(
            !is_verified(&outcome),
            "a current-state bound must not constrain entry-state `old(x)`, got {outcome:?}"
        );
    }

    #[test]
    fn does_not_substitute_current_equality_inside_old_expression() {
        let outcome = prove("(x == 0 && x >= 0) ==> old(x) >= 0");
        assert!(
            !is_verified(&outcome),
            "a current-state equality must not rewrite entry-state `old(x)`, got {outcome:?}"
        );
    }

    #[test]
    fn does_not_beta_reduce_current_let_value_across_old_boundary() {
        let outcome = prove("{ let t = x; old(t) == old(x) }");
        assert!(
            !is_verified(&outcome),
            "a current-state let value must not be moved beneath `old`, got {outcome:?}"
        );
    }

    #[test]
    fn preserves_explicit_old_variable_linear_reasoning() {
        let outcome = prove("old(x) >= 0 ==> old(x) + 1 >= 1");
        assert!(
            is_verified(&outcome),
            "an explicit entry-state bound should still constrain the same `old(x)`, got {outcome:?}"
        );
    }

    // Keystone: `(ring_head + base) % len < len` under `len >= 1`.
    #[test]
    fn proves_row_index_modulo_upper_bound() {
        let outcome = prove("len >= 1 ==> (ring_head + base) % len < len");
        assert!(is_verified(&outcome), "expected Verified, got {outcome:?}");
    }

    // Simplest form: `n % m < m` under `m >= 1`.
    #[test]
    fn proves_simple_modulo_upper_bound() {
        let outcome = prove("m >= 1 ==> n % m < m");
        assert!(is_verified(&outcome), "expected Verified, got {outcome:?}");
    }

    // `<=` form: `n % m <= m - 1` under `m >= 1`.
    #[test]
    fn proves_modulo_upper_bound_le() {
        let outcome = prove("m >= 1 ==> n % m <= m - 1");
        assert!(is_verified(&outcome), "expected Verified, got {outcome:?}");
    }

    // Soundness guard: without a positive-divisor assumption the upper bound
    // must NOT be claimed, so this stays non-Verified.
    #[test]
    fn does_not_prove_modulo_upper_bound_without_positive_divisor() {
        let outcome = prove("n % m < m");
        assert!(
            !is_verified(&outcome),
            "must not prove a modulo bound without a positive divisor, got {outcome:?}"
        );
    }

    // Soundness guard: a genuinely false modulo bound must not be proved.
    // `n % m < m - 1` is false e.g. for n=1, m=2 (1 % 2 = 1, not < 1).
    #[test]
    fn does_not_prove_false_modulo_strict_upper_bound() {
        let outcome = prove("m >= 1 ==> n % m < m - 1");
        assert!(
            !is_verified(&outcome),
            "must not prove a false modulo bound, got {outcome:?}"
        );
    }

    // Soundness guard: equality against the divisor is false in general.
    #[test]
    fn does_not_prove_modulo_equals_divisor() {
        let outcome = prove("m >= 1 ==> n % m == m");
        assert!(
            !is_verified(&outcome),
            "must not prove `n % m == m`, got {outcome:?}"
        );
    }

    // Soundness guard: the native constant evaluator uses TRUNCATED remainder
    // (`-1 % 5 == -1`), so `n % m >= 0` must NOT be proved for a symbolic
    // dividend even under `m >= 1` — proving it would contradict the prover's
    // own ground evaluation. The non-negativity rule in `lower_bound_int_expr`
    // is therefore deliberately gated on a non-negative dividend.
    #[test]
    fn does_not_prove_modulo_nonneg_for_symbolic_dividend() {
        let outcome = prove("m >= 1 ==> n % m >= 0");
        assert!(
            !is_verified(&outcome),
            "must not prove n % m >= 0 for symbolic n (truncated rem can be negative), got {outcome:?}"
        );
    }
}

#[cfg(test)]
mod truncated_bound_tests {
    use super::*;

    fn v(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }
    fn bin(l: PureExpr, op: BinOp, r: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(l), op, Arc::new(r))
    }
    fn verified(pred: &PureExpr) -> bool {
        matches!(
            prove_native_pure_predicate(pred, NativeClaimFormat::TrustWpPureExprV1, &[]),
            NativePureProofOutcome::Verified(_)
        )
    }

    // Keystone for the truncated remainder: exercises the extended
    // lower_bound_int_difference / upper-bound rules for BinOp::RemTrunc.
    // `len >= 1 ==> (ring_head + base) %trunc len < len`.
    #[test]
    fn native_proves_remtrunc_keystone() {
        let pred = bin(
            bin(v("len"), BinOp::Ge, PureExpr::Int(1)),
            BinOp::Implies,
            bin(
                bin(
                    bin(v("ring_head"), BinOp::Add, v("base")),
                    BinOp::RemTrunc,
                    v("len"),
                ),
                BinOp::Lt,
                v("len"),
            ),
        );
        assert!(
            verified(&pred),
            "len>=1 ==> (ring_head+base) %trunc len < len"
        );
    }

    // `m >= 1 ==> n %trunc m < m`.
    #[test]
    fn native_proves_remtrunc_simple_upper_bound() {
        let pred = bin(
            bin(v("m"), BinOp::Ge, PureExpr::Int(1)),
            BinOp::Implies,
            bin(bin(v("n"), BinOp::RemTrunc, v("m")), BinOp::Lt, v("m")),
        );
        assert!(verified(&pred), "m>=1 ==> n %trunc m < m");
    }

    // SOUNDNESS: the truncated remainder takes the dividend's sign, so for a
    // possibly-negative symbolic dividend `n %trunc m >= 0` must NOT be proved.
    #[test]
    fn native_does_not_prove_remtrunc_nonneg_for_symbolic_dividend() {
        let pred = bin(
            bin(v("m"), BinOp::Ge, PureExpr::Int(1)),
            BinOp::Implies,
            bin(
                bin(v("n"), BinOp::RemTrunc, v("m")),
                BinOp::Ge,
                PureExpr::Int(0),
            ),
        );
        assert!(
            !verified(&pred),
            "must NOT prove n %trunc m >= 0 for possibly-negative symbolic n"
        );
    }

    // With a non-negative dividend (literal 7), `7 %trunc m >= 0` IS provable —
    // exercises the extended lower_bound_int_expr RemTrunc arm (>= 0 for a
    // non-negative dividend and positive divisor). A literal dividend keeps this
    // to a single antecedent the native prover gathers. (The nested-antecedent
    // `n>=0 ==> m>=1 ==> ...` form fails for both Mod and RemTrunc — a pre-
    // existing prover premise-gathering limitation, not a div/mod issue.)
    #[test]
    fn native_proves_remtrunc_nonneg_for_nonnegative_dividend() {
        let pred = bin(
            bin(v("m"), BinOp::Ge, PureExpr::Int(1)),
            BinOp::Implies,
            bin(
                bin(PureExpr::Int(7), BinOp::RemTrunc, v("m")),
                BinOp::Ge,
                PureExpr::Int(0),
            ),
        );
        assert!(verified(&pred), "m>=1 ==> 7 %trunc m >= 0");
    }

    // DivTrunc lower bound: `m >= 1 ==> 7 /trunc m >= 0`.
    #[test]
    fn native_proves_divtrunc_nonneg_for_nonnegative_dividend() {
        let pred = bin(
            bin(v("m"), BinOp::Ge, PureExpr::Int(1)),
            BinOp::Implies,
            bin(
                bin(PureExpr::Int(7), BinOp::DivTrunc, v("m")),
                BinOp::Ge,
                PureExpr::Int(0),
            ),
        );
        assert!(verified(&pred), "m>=1 ==> 7 /trunc m >= 0");
    }
}

#[cfg(test)]
mod binder_domain_tests {
    use super::*;

    fn quantifier(exists: bool, var: &str, sort: ExprSort, body: PureExpr) -> PureExpr {
        let (var, var_sort, body, triggers) =
            (var.to_string(), Some(sort), Arc::new(body), Vec::new());
        if exists {
            PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers,
            }
        } else {
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            }
        }
    }

    fn not(expr: PureExpr) -> PureExpr {
        PureExpr::UnOp(UnOp::Not, Arc::new(expr))
    }

    fn type_param(name: &str) -> ExprSort {
        ExprSort::TypeParam(crate::formula::intern_sort_name(name))
    }

    fn v_plus_one_gt_v() -> PureExpr {
        let v = || Arc::new(PureExpr::Var("v".to_string(), None));
        PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(v(), BinOp::Add, Arc::new(PureExpr::Int(1)))),
            BinOp::Gt,
            v(),
        )
    }

    fn outcome(expr: &PureExpr) -> TruthValue {
        prove_bool(expr, &NativeReplayContext { summary_facts: &[] })
    }

    /// Measured: `exists<p: &T> true` and `!(forall<p: &T> false)` verified,
    /// and each is false when `T` is uninhabited (so is `&T`). A rule that
    /// needs a value of the binder's sort fires over `Int` and `Bool` only.
    #[test]
    fn a_witness_is_assumed_only_over_a_sort_known_inhabited() {
        let reference = ExprSort::Ref(Box::new(type_param("T")));
        for (label, expr) in [
            (
                "exists<p: &T> true",
                quantifier(true, "p", reference.clone(), PureExpr::Bool(true)),
            ),
            (
                "!(forall<p: &T> false)",
                not(quantifier(
                    false,
                    "p",
                    reference.clone(),
                    PureExpr::Bool(false),
                )),
            ),
            (
                "forall<p: &mut T> false",
                quantifier(
                    false,
                    "p",
                    ExprSort::MutRef(Box::new(type_param("T"))),
                    PureExpr::Bool(false),
                ),
            ),
        ] {
            assert!(
                matches!(outcome(&expr), TruthValue::Unknown { ref reason } if reason.contains("not known to be inhabited")),
                "{label}: {:?}",
                outcome(&expr)
            );
        }
        // Controls: over `Int` and `Bool` a witness exists.
        for sort in [ExprSort::Int, ExprSort::Bool] {
            assert!(matches!(
                outcome(&quantifier(true, "v", sort.clone(), PureExpr::Bool(true))),
                TruthValue::True {
                    rule: "exists-true-body"
                }
            ));
            assert!(matches!(
                outcome(&quantifier(false, "v", sort.clone(), PureExpr::Bool(false))),
                TruthValue::False {
                    rule: "forall-false-body"
                }
            ));
        }
        // A true `forall` body and a false `exists` body need no witness.
        assert!(matches!(
            outcome(&quantifier(
                false,
                "p",
                reference.clone(),
                PureExpr::Bool(true)
            )),
            TruthValue::True {
                rule: "forall-true-body"
            }
        ));
        assert!(matches!(
            outcome(&quantifier(true, "p", reference, PureExpr::Bool(false))),
            TruthValue::False {
                rule: "exists-false-body"
            }
        ));
    }

    /// Measured: `forall<v: T> v + 1 > v` and `forall<s: [Int]> s + 1 > s`
    /// verified, the binder read as an integer. A binder over a sort native
    /// replay does not model decides nothing.
    #[test]
    fn a_binder_over_an_unmodeled_sort_decides_nothing() {
        for sort in [
            type_param("T"),
            ExprSort::Seq,
            ExprSort::Unit,
            ExprSort::Float(crate::formula::FloatWidth::F64),
            ExprSort::Float(crate::formula::FloatWidth::F32),
        ] {
            for exists in [false, true] {
                for body in [
                    v_plus_one_gt_v(),
                    PureExpr::Bool(true),
                    PureExpr::Bool(false),
                ] {
                    let expr = quantifier(exists, "v", sort.clone(), body);
                    assert!(
                        matches!(outcome(&expr), TruthValue::Unknown { ref reason } if reason.contains("does not model")),
                        "{expr}: {:?}",
                        outcome(&expr)
                    );
                }
            }
        }
        let untyped = PureExpr::Forall {
            var: "v".to_string(),
            var_sort: None,
            body: Arc::new(v_plus_one_gt_v()),
            triggers: Vec::new(),
        };
        assert!(matches!(outcome(&untyped), TruthValue::Unknown { .. }));
        // Control: over `Int` it proves.
        assert!(matches!(
            outcome(&quantifier(false, "v", ExprSort::Int, v_plus_one_gt_v())),
            TruthValue::True {
                rule: "forall-true-body"
            }
        ));
    }
}

#[cfg(test)]
mod guarded_unsigned_tests {
    use super::*;
    fn proved(text: &str) -> bool {
        let expr = parse_contract(text).expect("typed scalar predicate");
        matches!(
            prove_native_pure_predicate(&expr, NativeClaimFormat::TrustWpPureExprV1, &[]),
            NativePureProofOutcome::Verified(_)
        )
    }
    #[test]
    fn literal_boolean_guards_preserve_integer_equality() {
        assert!(proved("(x >= 0 && x <= 4294967295) ==> (((x == 8) == false) ==> 0 <= x) && (!((x == 8) == false) ==> 7 <= x)"));
        assert!(proved(
            "(x >= 0 && y >= 0) ==> ((x == 8 && y == 32) ==> (24 <= y && x <= 32))"
        ));
        assert!(proved(
            "(x >= 0 && x <= 4294967295) ==> ((x >= 0 && x <= 4294967295) || (!(x >= 0) && false))"
        ));
        // This unbounded tautology also needs complementary inequality case
        // splitting. A sufficient rule may leave it unsupported, never false.
        let unbounded = parse_contract(
            "x >= 0 ==> ((x >= 0 && x <= 4294967295) || (!(x >= 0) && false)) || x > 4294967295",
        )
        .unwrap();
        assert!(!matches!(
            prove_native_pure_predicate(&unbounded, NativeClaimFormat::TrustWpPureExprV1, &[]),
            NativePureProofOutcome::Failed(_)
        ));
        for guard in [
            "true == (x == 8)",
            "(x == 8) == true",
            "false != (x == 8)",
            "(x == 8) != false",
            "!(false == (x == 8))",
            "!(true != (x == 8))",
        ] {
            assert!(proved(&format!("x >= 0 ==> ({guard} ==> x >= 8)")));
            assert!(!proved(&format!("x >= 0 ==> ({guard} ==> x >= 9)")));
        }
    }
    #[test]
    fn stronger_later_constraint_and_exhausted_search() {
        assert!(proved("(x >= 0 && x >= 8) ==> x >= 7"));
        assert!(proved("(x >= 8 && x >= 0) ==> x >= 7"));
        assert!(!proved("(x >= 0 && x >= 8) ==> x >= 9"));
        let expr = parse_contract("x >= 8").unwrap();
        assert!(prove_guarded_integer_predicate(&expr, true, &[], &[], &mut 0).is_none());
        let mut constraints = Vec::new();
        collect_guard_constraints(&expr, true, &mut constraints, &mut 0);
        assert!(constraints.is_empty());
    }

    #[test]
    fn false_arms_and_disequalities_do_not_become_premises() {
        for goal in [
            "x >= 0 ==> ((x == 0) ==> 1 <= x)",
            "x >= 0 ==> ((x != 8) ==> x >= 9)",
            "x >= 0 ==> ((x == 8 || x == 0) ==> x >= 8)",
            "x >= 0 ==> ((x == 8) ==> false)",
            "(x >= 0 && y >= 0) ==> ((x == 8 && y == 32) ==> x >= 9)",
        ] {
            assert!(!proved(goal), "{goal}");
        }
    }

    #[test]
    fn unsigned_division_bounds_require_the_actual_enclosing_domain() {
        for goal in [
            "x / 1 == x",
            "x + 0 == x",
            "(x >= 0 && x <= 4294967295) ==> x / 1048576 <= 4095",
            "(x >= 0 && y >= 1) ==> x / y <= x",
            "(x >= 0 && y >= 0) ==> (y != 0 ==> x / y <= x)",
            "(x >= 0 && y >= 0) ==> (((y == 0) == false) ==> x / y <= x)",
            "x >= 0 ==> (x != 0 ==> x >= 1)",
            "x <= 0 ==> (x != 0 ==> x <= -1)",
            "(x >= 0 && y >= 1) ==> (x / y != 0 ==> x / y > 0)",
            "(x >= 0 && y >= 1) ==> (((x / y == 0) == false) ==> (x >= 0 ==> x / y > 0))",
            "(x >= 0 && y >= 1) ==> (0 != x / y ==> !(x / y <= 0))",
            "x >= 0 ==> (x == 0 ==> (x > 0 ==> 0 > 0))",
            "x == 0 ==> (x > 0 ==> false)",
            "x > 0 ==> (x == 0 ==> false)",
        ] {
            assert!(proved(goal), "{goal}");
        }
        for goal in [
            "x / 1 != x",
            "x + 1 == x",
            "x / 2 == x",
            "(x >= 0 && x <= 4294967295) ==> x / 1048576 <= 4094",
            "y >= 1 ==> x / y <= x",
            "x >= 0 ==> x / y <= x",
            "(x >= 0 && y != 0) ==> x / y >= 0",
            "(x >= 1 && y <= -1) ==> x / y >= 0",
            "(x >= 0 && y >= 1) ==> x / y < x",
            "(x >= 0 && y >= 1) ==> x / y == x",
            "x != 0 ==> x >= 1",
            "x >= 0 ==> (x != 8 ==> x >= 9)",
            "x >= 0 ==> ((x != 0 || true) ==> x >= 1)",
            "(x >= 0 && y >= 1) ==> ((x / y != 0 || true) ==> x / y > 0)",
            "(x >= 0 && y >= 1) ==> ((x / y != 0 && false) || x / y > 0)",
            "y >= 1 ==> (x / y != 0 ==> x / y > 0)",
            "(x >= 0 && y <= -1) ==> (x / y != 0 ==> x / y > 0)",
            "(x >= 0 && y >= 1) ==> (old(x / y) != 0 ==> x / y > 0)",
            "(x >= 0 && y >= 1) ==> (x / y != 0 ==> old(x / y) > 0)",
            "x >= 0 ==> (x > 0 ==> 0 > 0)",
            "x >= 0 ==> (x >= 0 ==> (x > 0 ==> false))",
            "x == 0 ==> (old(x) > 0 ==> false)",
            "x >= 0 ==> (x < 0 && false)",
        ] {
            assert!(!proved(goal), "{goal}");
        }
        let quotient = parse_contract("(x : int) / (y : int)").unwrap();
        let nonnegative = parse_contract("x >= 0 && y >= 1").unwrap();
        let nonzero = PureExpr::BinOp(
            Arc::new(quotient.clone()),
            BinOp::Ne,
            Arc::new(PureExpr::Int(0)),
        );
        assert!(prove_ordered_from_guard_disequality(
            &quotient,
            BinOp::Gt,
            &PureExpr::Int(0),
            &linear_constraints_from_assumption(&nonnegative),
            &[(&nonzero, true)],
            &mut 0
        )
        .is_none());
        let impossible = parse_contract("x == 0 && x > 0").unwrap();
        assert!(newly_contradictory_guard(
            &linear_constraints_from_assumption(&impossible),
            0,
            &mut 0
        )
        .is_none());
    }
}
