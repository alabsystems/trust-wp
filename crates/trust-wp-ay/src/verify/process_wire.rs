// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Private process-isolation wire types.
//!
//! These DTOs intentionally do not add serde derives to the public verification
//! API. They cover the outcome/provenance surface that has to cross the fork
//! boundary when hard-timeout worker threads are killed with the child process.

use std::{collections::HashMap, str::FromStr, time::Duration};

use ay_dpll::api::{FpSpecialKind, ModelValue};
use num_bigint::BigInt;
use num_rational::BigRational;
use serde::{Deserialize, Serialize};

use super::{
    types::{
        Counterexample, CounterexampleValue, PostconditionInfo, ProofAssertSliceCertificate,
        ProofAssertSliceDerivation, ProofCertificateSummary, SolveEvidenceSnapshot,
        SolveLimitKindSnapshot, SolveResourceSnapshot, SolveStatisticsSnapshot,
        SolveVerificationLevelSnapshot, SolveVerificationSnapshot, StrictProofReplayObservation,
        UnknownReason, VarOrigin, VerificationOutcome, VerificationProvenance, VerificationResult,
    },
    LoopVerificationOutcome,
};
use crate::{
    encoder::unsoundness::{self, UnsoundnessCategory},
    error::EncodingError,
    span::SourceSpan,
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) enum WireChildMessage {
    Outcome {
        outcome: WireVerificationOutcome,
        delta: WireUnsoundnessDelta,
    },
    Error {
        error: WireEncodingError,
        delta: WireUnsoundnessDelta,
    },
    Panic {
        message: String,
        delta: WireUnsoundnessDelta,
    },
}

impl WireChildMessage {
    pub(crate) fn from_result(
        result: Result<VerificationOutcome, EncodingError>,
        baseline: &unsoundness::Snapshot,
    ) -> Self {
        let delta = WireUnsoundnessDelta::from_snapshots(baseline, &unsoundness::snapshot());
        match result {
            Ok(outcome) => match WireVerificationOutcome::from_outcome(&outcome) {
                Ok(outcome) => Self::Outcome { outcome, delta },
                Err(message) => Self::Error {
                    error: WireEncodingError::Unsupported {
                        message,
                        span: None,
                        contract_text: None,
                    },
                    delta,
                },
            },
            Err(error) => Self::Error {
                error: WireEncodingError::from_error(&error),
                delta,
            },
        }
    }

    pub(crate) fn from_panic(
        message: String,
        baseline: &unsoundness::Snapshot,
    ) -> WireChildMessage {
        Self::Panic {
            message,
            delta: WireUnsoundnessDelta::from_snapshots(baseline, &unsoundness::snapshot()),
        }
    }

    pub(crate) fn delta(&self) -> Result<unsoundness::Snapshot, String> {
        match self {
            Self::Outcome { delta, .. } | Self::Error { delta, .. } | Self::Panic { delta, .. } => {
                delta.to_snapshot()
            }
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) enum WireLoopChildMessage {
    Outcome {
        outcome: WireLoopVerificationOutcome,
        delta: WireUnsoundnessDelta,
    },
    Error {
        error: WireEncodingError,
        delta: WireUnsoundnessDelta,
    },
    Panic {
        message: String,
        delta: WireUnsoundnessDelta,
    },
}

impl WireLoopChildMessage {
    pub(crate) fn from_result(
        result: Result<LoopVerificationOutcome, EncodingError>,
        baseline: &unsoundness::Snapshot,
    ) -> Self {
        let delta = WireUnsoundnessDelta::from_snapshots(baseline, &unsoundness::snapshot());
        match result {
            Ok(outcome) => match WireLoopVerificationOutcome::from_outcome(&outcome) {
                Ok(outcome) => Self::Outcome { outcome, delta },
                Err(message) => Self::Error {
                    error: WireEncodingError::Unsupported {
                        message,
                        span: None,
                        contract_text: None,
                    },
                    delta,
                },
            },
            Err(error) => Self::Error {
                error: WireEncodingError::from_error(&error),
                delta,
            },
        }
    }

    pub(crate) fn from_panic(
        message: String,
        baseline: &unsoundness::Snapshot,
    ) -> WireLoopChildMessage {
        Self::Panic {
            message,
            delta: WireUnsoundnessDelta::from_snapshots(baseline, &unsoundness::snapshot()),
        }
    }

    pub(crate) fn delta(&self) -> Result<unsoundness::Snapshot, String> {
        match self {
            Self::Outcome { delta, .. } | Self::Error { delta, .. } | Self::Panic { delta, .. } => {
                delta.to_snapshot()
            }
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct WireUnsoundnessDelta {
    counts: Vec<(String, usize)>,
}

impl WireUnsoundnessDelta {
    fn from_snapshots(baseline: &unsoundness::Snapshot, after: &unsoundness::Snapshot) -> Self {
        let mut counts = Vec::new();
        for category in UnsoundnessCategory::ALL {
            let before_count = baseline.get(category).copied().unwrap_or(0);
            let after_count = after.get(category).copied().unwrap_or(0);
            if after_count > before_count {
                counts.push((category.to_string(), after_count - before_count));
            }
        }
        Self { counts }
    }

    fn to_snapshot(&self) -> Result<unsoundness::Snapshot, String> {
        let mut snapshot = HashMap::new();
        for (name, count) in &self.counts {
            let category = category_from_wire_name(name)
                .ok_or_else(|| format!("unknown unsoundness category from child: {name}"))?;
            snapshot.insert(category, *count);
        }
        Ok(snapshot)
    }
}

fn category_from_wire_name(name: &str) -> Option<UnsoundnessCategory> {
    UnsoundnessCategory::ALL
        .iter()
        .copied()
        .find(|category| category.to_string() == name)
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct WireVerificationOutcome {
    result: WireVerificationResult,
    provenance: Option<WireVerificationProvenance>,
}

impl WireVerificationOutcome {
    fn from_outcome(outcome: &VerificationOutcome) -> Result<Self, String> {
        Ok(Self {
            result: WireVerificationResult::from_result(&outcome.result)?,
            provenance: outcome
                .provenance
                .as_ref()
                .map(WireVerificationProvenance::from_provenance),
        })
    }

    pub(crate) fn into_outcome(self) -> Result<VerificationOutcome, String> {
        Ok(VerificationOutcome::new(
            self.result.into_result()?,
            self.provenance
                .map(WireVerificationProvenance::into_provenance)
                .transpose()?,
        ))
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct WireLoopVerificationOutcome {
    initialization: WireVerificationOutcome,
    preservation: WireVerificationOutcome,
    postcondition: WireVerificationOutcome,
    variant_nonneg: Option<WireVerificationOutcome>,
    variant_decrease: Option<WireVerificationOutcome>,
    entry_may_execute: Option<WireVerificationOutcome>,
}

impl WireLoopVerificationOutcome {
    fn from_outcome(outcome: &LoopVerificationOutcome) -> Result<Self, String> {
        Ok(Self {
            initialization: WireVerificationOutcome::from_outcome(&outcome.initialization)?,
            preservation: WireVerificationOutcome::from_outcome(&outcome.preservation)?,
            postcondition: WireVerificationOutcome::from_outcome(&outcome.postcondition)?,
            variant_nonneg: outcome
                .variant_nonneg
                .as_ref()
                .map(WireVerificationOutcome::from_outcome)
                .transpose()?,
            variant_decrease: outcome
                .variant_decrease
                .as_ref()
                .map(WireVerificationOutcome::from_outcome)
                .transpose()?,
            entry_may_execute: outcome
                .entry_may_execute
                .as_ref()
                .map(WireVerificationOutcome::from_outcome)
                .transpose()?,
        })
    }

    pub(crate) fn into_outcome(self) -> Result<LoopVerificationOutcome, String> {
        Ok(LoopVerificationOutcome {
            initialization: self.initialization.into_outcome()?,
            preservation: self.preservation.into_outcome()?,
            postcondition: self.postcondition.into_outcome()?,
            variant_nonneg: self
                .variant_nonneg
                .map(WireVerificationOutcome::into_outcome)
                .transpose()?,
            variant_decrease: self
                .variant_decrease
                .map(WireVerificationOutcome::into_outcome)
                .transpose()?,
            entry_may_execute: self
                .entry_may_execute
                .map(WireVerificationOutcome::into_outcome)
                .transpose()?,
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum WireVerificationResult {
    Verified(Option<WireProofCertificateSummary>),
    Assumed(String),
    Failed(WireCounterexample),
    Unknown(WireUnknownReason),
}

impl WireVerificationResult {
    fn from_result(result: &VerificationResult) -> Result<Self, String> {
        Ok(match result {
            VerificationResult::Verified(summary) => Self::Verified(
                summary
                    .as_ref()
                    .map(WireProofCertificateSummary::from_summary),
            ),
            VerificationResult::Assumed(reason) => Self::Assumed(reason.clone()),
            VerificationResult::Failed(counterexample) => {
                Self::Failed(WireCounterexample::from_counterexample(counterexample)?)
            }
            VerificationResult::Unknown(reason) => {
                Self::Unknown(WireUnknownReason::from_reason(reason))
            }
        })
    }

    fn into_result(self) -> Result<VerificationResult, String> {
        Ok(match self {
            Self::Verified(summary) => {
                VerificationResult::Verified(summary.map(WireProofCertificateSummary::into_summary))
            }
            Self::Assumed(reason) => VerificationResult::Assumed(reason),
            Self::Failed(counterexample) => {
                VerificationResult::Failed(counterexample.into_counterexample()?)
            }
            Self::Unknown(reason) => VerificationResult::Unknown(reason.into_reason()),
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct WireProofCertificateSummary {
    strict_verified: bool,
    restricted_rule_subset: bool,
    trust_count: u32,
    #[serde(default)]
    trust_fallback_count: u32,
    #[serde(default)]
    hole_count: u32,
    #[serde(default)]
    theory_lemma_count: u32,
    resolution_count: u32,
    #[serde(default)]
    farkas_certificate_count: u32,
    #[serde(default)]
    lrat_present: bool,
    #[serde(default)]
    alethe_text: Option<String>,
}

impl WireProofCertificateSummary {
    fn from_summary(summary: &ProofCertificateSummary) -> Self {
        Self {
            strict_verified: summary.strict_verified,
            restricted_rule_subset: summary.restricted_rule_subset,
            trust_count: summary.trust_count,
            trust_fallback_count: summary.trust_fallback_count,
            hole_count: summary.hole_count,
            theory_lemma_count: summary.theory_lemma_count,
            resolution_count: summary.resolution_count,
            farkas_certificate_count: summary.farkas_certificate_count,
            lrat_present: summary.lrat_present,
            alethe_text: summary.alethe_text.clone(),
        }
    }

    fn into_summary(self) -> ProofCertificateSummary {
        ProofCertificateSummary {
            strict_verified: self.strict_verified,
            restricted_rule_subset: self.restricted_rule_subset,
            trust_count: self.trust_count,
            trust_fallback_count: self.trust_fallback_count,
            hole_count: self.hole_count,
            theory_lemma_count: self.theory_lemma_count,
            resolution_count: self.resolution_count,
            farkas_certificate_count: self.farkas_certificate_count,
            lrat_present: self.lrat_present,
            alethe_text: self.alethe_text,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct WireCounterexample {
    values: Vec<WireCounterexampleValue>,
    violated_postcondition: Option<WirePostconditionInfo>,
}

impl WireCounterexample {
    fn from_counterexample(counterexample: &Counterexample) -> Result<Self, String> {
        Ok(Self {
            values: counterexample
                .values
                .iter()
                .map(WireCounterexampleValue::from_value)
                .collect::<Result<Vec<_>, _>>()?,
            violated_postcondition: counterexample
                .violated_postcondition
                .as_ref()
                .map(WirePostconditionInfo::from_info),
        })
    }

    fn into_counterexample(self) -> Result<Counterexample, String> {
        Ok(Counterexample {
            values: self
                .values
                .into_iter()
                .map(WireCounterexampleValue::into_value)
                .collect::<Result<Vec<_>, _>>()?,
            violated_postcondition: self
                .violated_postcondition
                .map(WirePostconditionInfo::into_info)
                .transpose()?,
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct WireCounterexampleValue {
    name: String,
    value: WireModelValue,
    origin: Option<WireVarOrigin>,
}

impl WireCounterexampleValue {
    fn from_value(value: &CounterexampleValue) -> Result<Self, String> {
        Ok(Self {
            name: value.name.clone(),
            value: WireModelValue::from_model_value(&value.value)?,
            origin: value.origin.as_ref().map(WireVarOrigin::from_origin),
        })
    }

    fn into_value(self) -> Result<CounterexampleValue, String> {
        Ok(CounterexampleValue {
            name: self.name,
            value: self.value.into_model_value()?,
            origin: self.origin.map(WireVarOrigin::into_origin).transpose()?,
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum WireVarOrigin {
    Parameter {
        name: String,
        span: Option<WireSourceSpan>,
    },
    Precondition {
        contract_idx: usize,
        span: Option<WireSourceSpan>,
    },
    Postcondition {
        contract_idx: usize,
        span: Option<WireSourceSpan>,
    },
    Invariant {
        span: Option<WireSourceSpan>,
    },
    MirLocal {
        local: u32,
        span: Option<WireSourceSpan>,
    },
    ReturnValue,
    Internal,
}

impl WireVarOrigin {
    fn from_origin(origin: &VarOrigin) -> Self {
        match origin {
            VarOrigin::Parameter { name, span } => Self::Parameter {
                name: name.clone(),
                span: span.as_ref().map(WireSourceSpan::from_span),
            },
            VarOrigin::Precondition { contract_idx, span } => Self::Precondition {
                contract_idx: *contract_idx,
                span: span.as_ref().map(WireSourceSpan::from_span),
            },
            VarOrigin::Postcondition { contract_idx, span } => Self::Postcondition {
                contract_idx: *contract_idx,
                span: span.as_ref().map(WireSourceSpan::from_span),
            },
            VarOrigin::Invariant { span } => Self::Invariant {
                span: span.as_ref().map(WireSourceSpan::from_span),
            },
            VarOrigin::MirLocal { local, span } => Self::MirLocal {
                local: *local,
                span: span.as_ref().map(WireSourceSpan::from_span),
            },
            VarOrigin::ReturnValue => Self::ReturnValue,
            VarOrigin::Internal => Self::Internal,
        }
    }

    fn into_origin(self) -> Result<VarOrigin, String> {
        Ok(match self {
            Self::Parameter { name, span } => VarOrigin::Parameter {
                name,
                span: span.map(WireSourceSpan::into_span).transpose()?,
            },
            Self::Precondition { contract_idx, span } => VarOrigin::Precondition {
                contract_idx,
                span: span.map(WireSourceSpan::into_span).transpose()?,
            },
            Self::Postcondition { contract_idx, span } => VarOrigin::Postcondition {
                contract_idx,
                span: span.map(WireSourceSpan::into_span).transpose()?,
            },
            Self::Invariant { span } => VarOrigin::Invariant {
                span: span.map(WireSourceSpan::into_span).transpose()?,
            },
            Self::MirLocal { local, span } => VarOrigin::MirLocal {
                local,
                span: span.map(WireSourceSpan::into_span).transpose()?,
            },
            Self::ReturnValue => VarOrigin::ReturnValue,
            Self::Internal => VarOrigin::Internal,
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct WirePostconditionInfo {
    clause_idx: usize,
    contract_text: String,
    span: Option<WireSourceSpan>,
}

impl WirePostconditionInfo {
    fn from_info(info: &PostconditionInfo) -> Self {
        Self {
            clause_idx: info.clause_idx,
            contract_text: info.contract_text.clone(),
            span: info.span.as_ref().map(WireSourceSpan::from_span),
        }
    }

    fn into_info(self) -> Result<PostconditionInfo, String> {
        Ok(PostconditionInfo {
            clause_idx: self.clause_idx,
            contract_text: self.contract_text,
            span: self.span.map(WireSourceSpan::into_span).transpose()?,
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum WireModelValue {
    Bool(bool),
    Int(String),
    Real {
        numerator: String,
        denominator: String,
    },
    BitVec {
        value: String,
        width: u32,
    },
    String(String),
    Uninterpreted(String),
    ArraySmtlib(String),
    Array {
        default: Box<WireModelValue>,
        stores: Vec<(WireModelValue, WireModelValue)>,
    },
    FloatingPoint {
        sign: bool,
        exponent: u64,
        significand: u64,
        eb: u32,
        sb: u32,
    },
    FloatingPointSpecial {
        kind: WireFpSpecialKind,
        eb: u32,
        sb: u32,
    },
    Datatype {
        constructor: String,
        args: Vec<WireModelValue>,
    },
    Seq(Vec<WireModelValue>),
    Unknown,
}

impl WireModelValue {
    fn from_model_value(value: &ModelValue) -> Result<Self, String> {
        Ok(match value {
            ModelValue::Bool(value) => Self::Bool(*value),
            ModelValue::Int(value) => Self::Int(value.to_string()),
            ModelValue::Real(value) => Self::Real {
                numerator: value.numer().to_string(),
                denominator: value.denom().to_string(),
            },
            ModelValue::BitVec { value, width } => Self::BitVec {
                value: value.to_string(),
                width: *width,
            },
            ModelValue::String(value) => Self::String(value.clone()),
            ModelValue::Uninterpreted(value) => Self::Uninterpreted(value.clone()),
            ModelValue::ArraySmtlib(value) => Self::ArraySmtlib(value.clone()),
            ModelValue::Array { default, stores } => Self::Array {
                default: Box::new(Self::from_model_value(default)?),
                stores: stores
                    .iter()
                    .map(|(index, value)| {
                        Ok((
                            Self::from_model_value(index)?,
                            Self::from_model_value(value)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, String>>()?,
            },
            ModelValue::FloatingPoint {
                sign,
                exponent,
                significand,
                eb,
                sb,
            } => Self::FloatingPoint {
                sign: *sign,
                exponent: *exponent,
                significand: *significand,
                eb: *eb,
                sb: *sb,
            },
            ModelValue::FloatingPointSpecial { kind, eb, sb } => Self::FloatingPointSpecial {
                kind: WireFpSpecialKind::from_kind(kind),
                eb: *eb,
                sb: *sb,
            },
            ModelValue::Datatype { constructor, args } => Self::Datatype {
                constructor: constructor.clone(),
                args: args
                    .iter()
                    .map(Self::from_model_value)
                    .collect::<Result<Vec<_>, _>>()?,
            },
            ModelValue::Seq(values) => Self::Seq(
                values
                    .iter()
                    .map(Self::from_model_value)
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            ModelValue::Unknown => Self::Unknown,
            _ => return Err("model value has no lossless process wire representation".into()),
        })
    }

    fn into_model_value(self) -> Result<ModelValue, String> {
        Ok(match self {
            Self::Bool(value) => ModelValue::Bool(value),
            Self::Int(value) => ModelValue::Int(parse_bigint(&value)?),
            Self::Real {
                numerator,
                denominator,
            } => {
                let numerator = parse_bigint(&numerator)?;
                let denominator = parse_bigint(&denominator)?;
                // BigRational::new PANICS on a zero denominator. These values
                // arrive over the wire from the solver child process, so this
                // is reachable input rather than an invariant of this function
                // — a child that emits "0" here would take the parent down.
                if denominator == BigInt::from(0) {
                    return Err("child model Real has a zero denominator".to_string());
                }
                ModelValue::Real(BigRational::new(numerator, denominator))
            }
            Self::BitVec { value, width } => ModelValue::BitVec {
                value: parse_bigint(&value)?,
                width,
            },
            Self::String(value) => ModelValue::String(value),
            Self::Uninterpreted(value) => ModelValue::Uninterpreted(value),
            Self::ArraySmtlib(value) => ModelValue::ArraySmtlib(value),
            Self::Array { default, stores } => ModelValue::Array {
                default: Box::new(default.into_model_value()?),
                stores: stores
                    .into_iter()
                    .map(|(index, value)| {
                        Ok((index.into_model_value()?, value.into_model_value()?))
                    })
                    .collect::<Result<Vec<_>, String>>()?,
            },
            Self::FloatingPoint {
                sign,
                exponent,
                significand,
                eb,
                sb,
            } => ModelValue::FloatingPoint {
                sign,
                exponent,
                significand,
                eb,
                sb,
            },
            Self::FloatingPointSpecial { kind, eb, sb } => ModelValue::FloatingPointSpecial {
                kind: kind.into_kind(),
                eb,
                sb,
            },
            Self::Datatype { constructor, args } => ModelValue::Datatype {
                constructor,
                args: args
                    .into_iter()
                    .map(WireModelValue::into_model_value)
                    .collect::<Result<Vec<_>, _>>()?,
            },
            Self::Seq(values) => ModelValue::Seq(
                values
                    .into_iter()
                    .map(WireModelValue::into_model_value)
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            Self::Unknown => ModelValue::Unknown,
        })
    }
}

fn parse_bigint(value: &str) -> Result<BigInt, String> {
    BigInt::from_str(value).map_err(|err| format!("invalid child BigInt {value:?}: {err}"))
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum WireFpSpecialKind {
    PosZero,
    NegZero,
    PosInf,
    NegInf,
    NaN,
}

impl WireFpSpecialKind {
    fn from_kind(kind: &FpSpecialKind) -> Self {
        match kind {
            FpSpecialKind::PosZero => Self::PosZero,
            FpSpecialKind::NegZero => Self::NegZero,
            FpSpecialKind::PosInf => Self::PosInf,
            FpSpecialKind::NegInf => Self::NegInf,
            FpSpecialKind::NaN => Self::NaN,
            _ => Self::NaN,
        }
    }

    fn into_kind(self) -> FpSpecialKind {
        match self {
            Self::PosZero => FpSpecialKind::PosZero,
            Self::NegZero => FpSpecialKind::NegZero,
            Self::PosInf => FpSpecialKind::PosInf,
            Self::NegInf => FpSpecialKind::NegInf,
            Self::NaN => FpSpecialKind::NaN,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) enum WireUnknownReason {
    Timeout,
    ResourceOut,
    Incomplete,
    Quantifiers,
    QuantifierRoundLimit,
    QuantifierDeferred,
    QuantifierUnhandled,
    QuantifierCegqiIncomplete,
    QuantifierEmatchingExistsIncomplete,
    SatModel,
    MemoryOut,
    Interrupted,
    Unsupported,
    UnsupportedArithmetic,
    UnsupportedMixedCollection,
    InternalError,
    SelfCheckRejected,
    ProofTrusted,
    Demoted(String),
    SolverPanic(String),
    SolverMessage(String),
    Unspecified,
}

impl WireUnknownReason {
    fn from_reason(reason: &UnknownReason) -> Self {
        match reason {
            UnknownReason::Timeout => Self::Timeout,
            UnknownReason::ResourceOut => Self::ResourceOut,
            UnknownReason::Incomplete => Self::Incomplete,
            UnknownReason::Quantifiers => Self::Quantifiers,
            UnknownReason::QuantifierRoundLimit => Self::QuantifierRoundLimit,
            UnknownReason::QuantifierDeferred => Self::QuantifierDeferred,
            UnknownReason::QuantifierUnhandled => Self::QuantifierUnhandled,
            UnknownReason::QuantifierCegqiIncomplete => Self::QuantifierCegqiIncomplete,
            UnknownReason::QuantifierEmatchingExistsIncomplete => {
                Self::QuantifierEmatchingExistsIncomplete
            }
            UnknownReason::SatModel => Self::SatModel,
            UnknownReason::MemoryOut => Self::MemoryOut,
            UnknownReason::Interrupted => Self::Interrupted,
            UnknownReason::Unsupported => Self::Unsupported,
            UnknownReason::UnsupportedArithmetic => Self::UnsupportedArithmetic,
            UnknownReason::UnsupportedMixedCollection => Self::UnsupportedMixedCollection,
            UnknownReason::InternalError => Self::InternalError,
            UnknownReason::SelfCheckRejected => Self::SelfCheckRejected,
            UnknownReason::ProofTrusted => Self::ProofTrusted,
            UnknownReason::Demoted(message) => Self::Demoted(message.clone()),
            UnknownReason::SolverPanic(message) => Self::SolverPanic(message.clone()),
            UnknownReason::SolverMessage(message) => Self::SolverMessage(message.clone()),
            UnknownReason::Unspecified => Self::Unspecified,
        }
    }

    fn into_reason(self) -> UnknownReason {
        match self {
            Self::Timeout => UnknownReason::Timeout,
            Self::ResourceOut => UnknownReason::ResourceOut,
            Self::Incomplete => UnknownReason::Incomplete,
            Self::Quantifiers => UnknownReason::Quantifiers,
            Self::QuantifierRoundLimit => UnknownReason::QuantifierRoundLimit,
            Self::QuantifierDeferred => UnknownReason::QuantifierDeferred,
            Self::QuantifierUnhandled => UnknownReason::QuantifierUnhandled,
            Self::QuantifierCegqiIncomplete => UnknownReason::QuantifierCegqiIncomplete,
            Self::QuantifierEmatchingExistsIncomplete => {
                UnknownReason::QuantifierEmatchingExistsIncomplete
            }
            Self::SatModel => UnknownReason::SatModel,
            Self::MemoryOut => UnknownReason::MemoryOut,
            Self::Interrupted => UnknownReason::Interrupted,
            Self::Unsupported => UnknownReason::Unsupported,
            Self::UnsupportedArithmetic => UnknownReason::UnsupportedArithmetic,
            Self::UnsupportedMixedCollection => UnknownReason::UnsupportedMixedCollection,
            Self::InternalError => UnknownReason::InternalError,
            Self::SelfCheckRejected => UnknownReason::SelfCheckRejected,
            Self::ProofTrusted => UnknownReason::ProofTrusted,
            Self::Demoted(message) => UnknownReason::Demoted(message),
            Self::SolverPanic(message) => UnknownReason::SolverPanic(message),
            Self::SolverMessage(message) => UnknownReason::SolverMessage(message),
            Self::Unspecified => UnknownReason::Unspecified,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct WireVerificationProvenance {
    vc_hash: [u8; 32],
    solve_time_nanos: u64,
    assertion_count: u64,
    solver_timeout_ms: Option<u64>,
    random_seed: Option<u64>,
    solver_statistics: Option<WireSolveStatisticsSnapshot>,
    solve_evidence: Option<WireSolveEvidenceSnapshot>,
    unknown_reason: Option<WireUnknownReason>,
    executor_error: Option<String>,
    replay_artifact: Option<String>,
    native_replay_json: Option<String>,
    #[serde(default)]
    proof_assert_slice_certificates: Vec<WireProofAssertSliceCertificate>,
    /// Diagnostics-only strict-replay observation. `#[serde(default)]` so a
    /// worker built before this field existed still deserializes (it simply
    /// reports "no strict replay observed").
    #[serde(default)]
    strict_proof_replay: Option<WireStrictProofReplayObservation>,
    /// Diagnostics-only count of observations refused for scope mismatch.
    /// `#[serde(default)]` for the same reason as the field above.
    #[serde(default)]
    strict_proof_replay_unbound: u32,
    /// The structural refutation shape that also refuted this
    /// obligation. `#[serde(default)]` so a worker built before the field
    /// existed deserializes as "no shape", which is the fail-closed reading.
    #[serde(default)]
    refutation_structural_shape: Option<String>,
}

/// Wire form of [`StrictProofReplayObservation`]. Diagnostics only — no gate,
/// verdict, or acceptance path reads it on either side of the boundary.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct WireStrictProofReplayObservation {
    evidence: WireSolveEvidenceSnapshot,
    statistics: WireSolveStatisticsSnapshot,
    authority_accepted: bool,
    unsat_proof_decline: Option<String>,
    /// `#[serde(default)]` so a worker built before these fields existed still
    /// deserializes — it simply reports no recorded reason, which is exactly
    /// what it measured.
    #[serde(default)]
    unknown_reason: Option<String>,
    #[serde(default)]
    unknown_detail: Option<String>,
}

impl WireStrictProofReplayObservation {
    fn from_observation(observation: &StrictProofReplayObservation) -> Self {
        Self {
            evidence: WireSolveEvidenceSnapshot::from_snapshot(&observation.evidence),
            statistics: WireSolveStatisticsSnapshot::from_snapshot(&observation.statistics),
            authority_accepted: observation.authority_accepted,
            unsat_proof_decline: observation.unsat_proof_decline.clone(),
            unknown_reason: observation.unknown_reason.clone(),
            unknown_detail: observation.unknown_detail.clone(),
        }
    }

    fn into_observation(self) -> Result<StrictProofReplayObservation, String> {
        Ok(StrictProofReplayObservation {
            evidence: self.evidence.into_snapshot()?,
            statistics: self.statistics.into_snapshot(),
            authority_accepted: self.authority_accepted,
            unsat_proof_decline: self.unsat_proof_decline,
            unknown_reason: self.unknown_reason,
            unknown_detail: self.unknown_detail,
        })
    }
}

impl WireVerificationProvenance {
    fn from_provenance(provenance: &VerificationProvenance) -> Self {
        Self {
            vc_hash: provenance.vc_hash,
            solve_time_nanos: duration_to_nanos(provenance.solve_time),
            assertion_count: provenance.assertion_count,
            solver_timeout_ms: provenance.solver_timeout_ms,
            random_seed: provenance.random_seed,
            solver_statistics: provenance
                .solver_statistics
                .as_ref()
                .map(WireSolveStatisticsSnapshot::from_snapshot),
            solve_evidence: provenance
                .solve_evidence
                .as_ref()
                .map(WireSolveEvidenceSnapshot::from_snapshot),
            unknown_reason: provenance
                .unknown_reason
                .as_ref()
                .map(WireUnknownReason::from_reason),
            executor_error: provenance.executor_error.clone(),
            replay_artifact: provenance.replay_artifact.clone(),
            native_replay_json: provenance.native_replay_json.clone(),
            proof_assert_slice_certificates: provenance
                .proof_assert_slice_certificates
                .iter()
                .map(WireProofAssertSliceCertificate::from_certificate)
                .collect(),
            strict_proof_replay: provenance
                .strict_proof_replay
                .as_ref()
                .map(WireStrictProofReplayObservation::from_observation),
            strict_proof_replay_unbound: provenance.strict_proof_replay_unbound,
            refutation_structural_shape: provenance.refutation_structural_shape.clone(),
        }
    }

    fn into_provenance(self) -> Result<VerificationProvenance, String> {
        Ok(VerificationProvenance {
            vc_hash: self.vc_hash,
            solve_time: Duration::from_nanos(self.solve_time_nanos),
            assertion_count: self.assertion_count,
            solver_timeout_ms: self.solver_timeout_ms,
            random_seed: self.random_seed,
            solver_statistics: self
                .solver_statistics
                .map(WireSolveStatisticsSnapshot::into_snapshot),
            solve_evidence: self
                .solve_evidence
                .map(WireSolveEvidenceSnapshot::into_snapshot)
                .transpose()?,
            unknown_reason: self.unknown_reason.map(WireUnknownReason::into_reason),
            executor_error: self.executor_error,
            replay_artifact: self.replay_artifact,
            native_replay_json: self.native_replay_json,
            proof_assert_slice_certificates: self
                .proof_assert_slice_certificates
                .into_iter()
                .map(WireProofAssertSliceCertificate::into_certificate)
                .collect::<Result<Vec<_>, _>>()?,
            strict_proof_replay: self
                .strict_proof_replay
                .map(WireStrictProofReplayObservation::into_observation)
                .transpose()?,
            strict_proof_replay_unbound: self.strict_proof_replay_unbound,
            refutation_structural_shape: self.refutation_structural_shape,
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct WireProofAssertSliceCertificate {
    ordinal: u64,
    derivation: WireProofAssertSliceDerivation,
    prepared_claim: String,
    prepared_claim_hash: [u8; 32],
    normalized_claim: String,
    normalized_claim_hash: [u8; 32],
    native_problem_json: String,
    problem_hash: [u8; 32],
    solve_evidence: WireSolveEvidenceSnapshot,
    solver_statistics: WireSolveStatisticsSnapshot,
}

impl WireProofAssertSliceCertificate {
    fn from_certificate(certificate: &ProofAssertSliceCertificate) -> Self {
        Self {
            ordinal: certificate.ordinal,
            derivation: WireProofAssertSliceDerivation::from_derivation(certificate.derivation),
            prepared_claim: certificate.prepared_claim.clone(),
            prepared_claim_hash: certificate.prepared_claim_hash,
            normalized_claim: certificate.normalized_claim.clone(),
            normalized_claim_hash: certificate.normalized_claim_hash,
            native_problem_json: certificate.native_problem_json.clone(),
            problem_hash: certificate.problem_hash,
            solve_evidence: WireSolveEvidenceSnapshot::from_snapshot(&certificate.solve_evidence),
            solver_statistics: WireSolveStatisticsSnapshot::from_snapshot(
                &certificate.solver_statistics,
            ),
        }
    }

    fn into_certificate(self) -> Result<ProofAssertSliceCertificate, String> {
        Ok(ProofAssertSliceCertificate::new(
            self.ordinal,
            self.derivation.into_derivation(),
            self.prepared_claim,
            self.prepared_claim_hash,
            self.normalized_claim,
            self.normalized_claim_hash,
            self.native_problem_json,
            self.problem_hash,
            self.solve_evidence.into_snapshot()?,
            self.solver_statistics.into_snapshot(),
        ))
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
enum WireProofAssertSliceDerivation {
    NativeEncoded,
    SyntacticTruth,
    ExactPreparedPremise,
}

impl WireProofAssertSliceDerivation {
    fn from_derivation(derivation: ProofAssertSliceDerivation) -> Self {
        match derivation {
            ProofAssertSliceDerivation::NativeEncoded => Self::NativeEncoded,
            ProofAssertSliceDerivation::SyntacticTruth => Self::SyntacticTruth,
            ProofAssertSliceDerivation::ExactPreparedPremise => Self::ExactPreparedPremise,
        }
    }

    fn into_derivation(self) -> ProofAssertSliceDerivation {
        match self {
            Self::NativeEncoded => ProofAssertSliceDerivation::NativeEncoded,
            Self::SyntacticTruth => ProofAssertSliceDerivation::SyntacticTruth,
            Self::ExactPreparedPremise => ProofAssertSliceDerivation::ExactPreparedPremise,
        }
    }
}

fn duration_to_nanos(duration: Duration) -> u64 {
    duration.as_nanos().min(u128::from(u64::MAX)) as u64
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct WireSolveStatisticsSnapshot {
    decisions: u64,
    conflicts: u64,
    propagations: u64,
    restarts: u64,
    theory_conflicts: u64,
    theory_propagations: u64,
    theory_unknown_count: u64,
    partial_clause_count: u64,
    model_validation_skips: u64,
    model_validation_failures: u64,
    proof_clause_count: u64,
    proof_complete: bool,
    ematching_rounds_completed: u64,
    ematching_instances_created: u64,
    term_bytes: u64,
    term_count: u64,
    refinement_count: u64,
    rlimit_count: u64,
    num_vars: u64,
    num_clauses: u64,
    num_assertions: u64,
    extra_ints: Vec<(String, u64)>,
}

impl WireSolveStatisticsSnapshot {
    fn from_snapshot(snapshot: &SolveStatisticsSnapshot) -> Self {
        Self {
            decisions: snapshot.decisions,
            conflicts: snapshot.conflicts,
            propagations: snapshot.propagations,
            restarts: snapshot.restarts,
            theory_conflicts: snapshot.theory_conflicts,
            theory_propagations: snapshot.theory_propagations,
            theory_unknown_count: snapshot.theory_unknown_count,
            partial_clause_count: snapshot.partial_clause_count,
            model_validation_skips: snapshot.model_validation_skips,
            model_validation_failures: snapshot.model_validation_failures,
            proof_clause_count: snapshot.proof_clause_count,
            proof_complete: snapshot.proof_complete,
            ematching_rounds_completed: snapshot.ematching_rounds_completed,
            ematching_instances_created: snapshot.ematching_instances_created,
            term_bytes: snapshot.term_bytes,
            term_count: snapshot.term_count,
            refinement_count: snapshot.refinement_count,
            rlimit_count: snapshot.rlimit_count,
            num_vars: snapshot.num_vars,
            num_clauses: snapshot.num_clauses,
            num_assertions: snapshot.num_assertions,
            extra_ints: snapshot.extra_ints.clone(),
        }
    }

    fn into_snapshot(self) -> SolveStatisticsSnapshot {
        SolveStatisticsSnapshot {
            decisions: self.decisions,
            conflicts: self.conflicts,
            propagations: self.propagations,
            restarts: self.restarts,
            theory_conflicts: self.theory_conflicts,
            theory_propagations: self.theory_propagations,
            theory_unknown_count: self.theory_unknown_count,
            partial_clause_count: self.partial_clause_count,
            model_validation_skips: self.model_validation_skips,
            model_validation_failures: self.model_validation_failures,
            proof_clause_count: self.proof_clause_count,
            proof_complete: self.proof_complete,
            ematching_rounds_completed: self.ematching_rounds_completed,
            ematching_instances_created: self.ematching_instances_created,
            term_bytes: self.term_bytes,
            term_count: self.term_count,
            refinement_count: self.refinement_count,
            rlimit_count: self.rlimit_count,
            num_vars: self.num_vars,
            num_clauses: self.num_clauses,
            num_assertions: self.num_assertions,
            extra_ints: self.extra_ints,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct WireSolveEvidenceSnapshot {
    result: String,
    model_validated: bool,
    accepted_for_consumer: bool,
    consumer_rejection: Option<String>,
    verification: WireSolveVerificationSnapshot,
    verification_level: WireSolveVerificationLevelSnapshot,
    resource_usage: WireSolveResourceSnapshot,
}

impl WireSolveEvidenceSnapshot {
    fn from_snapshot(snapshot: &SolveEvidenceSnapshot) -> Self {
        Self {
            result: snapshot.result.clone(),
            model_validated: snapshot.model_validated,
            accepted_for_consumer: snapshot.accepted_for_consumer,
            consumer_rejection: snapshot.consumer_rejection.clone(),
            verification: WireSolveVerificationSnapshot::from_snapshot(&snapshot.verification),
            verification_level: WireSolveVerificationLevelSnapshot::from_snapshot(
                snapshot.verification_level,
            ),
            resource_usage: WireSolveResourceSnapshot::from_snapshot(&snapshot.resource_usage),
        }
    }

    fn into_snapshot(self) -> Result<SolveEvidenceSnapshot, String> {
        Ok(SolveEvidenceSnapshot {
            result: self.result,
            model_validated: self.model_validated,
            accepted_for_consumer: self.accepted_for_consumer,
            consumer_rejection: self.consumer_rejection,
            verification: self.verification.into_snapshot(),
            verification_level: self.verification_level.into_snapshot(),
            resource_usage: self.resource_usage.into_snapshot(),
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct WireSolveVerificationSnapshot {
    sat_model_validated: bool,
    unsat_proof_available: bool,
    unsat_proof_checker_failures: u64,
    sat_independent_checks: u64,
    sat_delegated_checks: u64,
    sat_incomplete_checks: u64,
}

impl WireSolveVerificationSnapshot {
    fn from_snapshot(snapshot: &SolveVerificationSnapshot) -> Self {
        Self {
            sat_model_validated: snapshot.sat_model_validated,
            unsat_proof_available: snapshot.unsat_proof_available,
            unsat_proof_checker_failures: snapshot.unsat_proof_checker_failures,
            sat_independent_checks: snapshot.sat_independent_checks,
            sat_delegated_checks: snapshot.sat_delegated_checks,
            sat_incomplete_checks: snapshot.sat_incomplete_checks,
        }
    }

    fn into_snapshot(self) -> SolveVerificationSnapshot {
        SolveVerificationSnapshot {
            sat_model_validated: self.sat_model_validated,
            unsat_proof_available: self.unsat_proof_available,
            unsat_proof_checker_failures: self.unsat_proof_checker_failures,
            sat_independent_checks: self.sat_independent_checks,
            sat_delegated_checks: self.sat_delegated_checks,
            sat_incomplete_checks: self.sat_incomplete_checks,
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
enum WireSolveVerificationLevelSnapshot {
    Trusted,
    DebugChecked,
    ProofChecked,
    FullyVerified,
    Unknown,
}

impl WireSolveVerificationLevelSnapshot {
    fn from_snapshot(snapshot: SolveVerificationLevelSnapshot) -> Self {
        match snapshot {
            SolveVerificationLevelSnapshot::Trusted => Self::Trusted,
            SolveVerificationLevelSnapshot::DebugChecked => Self::DebugChecked,
            SolveVerificationLevelSnapshot::ProofChecked => Self::ProofChecked,
            SolveVerificationLevelSnapshot::FullyVerified => Self::FullyVerified,
            SolveVerificationLevelSnapshot::Unknown => Self::Unknown,
        }
    }

    fn into_snapshot(self) -> SolveVerificationLevelSnapshot {
        match self {
            Self::Trusted => SolveVerificationLevelSnapshot::Trusted,
            Self::DebugChecked => SolveVerificationLevelSnapshot::DebugChecked,
            Self::ProofChecked => SolveVerificationLevelSnapshot::ProofChecked,
            Self::FullyVerified => SolveVerificationLevelSnapshot::FullyVerified,
            Self::Unknown => SolveVerificationLevelSnapshot::Unknown,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct WireSolveResourceSnapshot {
    rss_bytes: u64,
    term_bytes: u64,
    term_count: u64,
    learned_clause_count: u64,
    wall_time_ms: u64,
    limit_hit: Option<WireSolveLimitKindSnapshot>,
}

impl WireSolveResourceSnapshot {
    fn from_snapshot(snapshot: &SolveResourceSnapshot) -> Self {
        Self {
            rss_bytes: snapshot.rss_bytes,
            term_bytes: snapshot.term_bytes,
            term_count: snapshot.term_count,
            learned_clause_count: snapshot.learned_clause_count,
            wall_time_ms: snapshot.wall_time_ms,
            limit_hit: snapshot
                .limit_hit
                .map(WireSolveLimitKindSnapshot::from_snapshot),
        }
    }

    fn into_snapshot(self) -> SolveResourceSnapshot {
        SolveResourceSnapshot {
            rss_bytes: self.rss_bytes,
            term_bytes: self.term_bytes,
            term_count: self.term_count,
            learned_clause_count: self.learned_clause_count,
            wall_time_ms: self.wall_time_ms,
            limit_hit: self
                .limit_hit
                .map(WireSolveLimitKindSnapshot::into_snapshot),
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
enum WireSolveLimitKindSnapshot {
    Timeout,
    MemoryLimit,
    TermMemoryLimit,
    LearnedClauseLimit,
    ClauseDbBytesLimit,
    Interrupted,
    Unknown,
}

impl WireSolveLimitKindSnapshot {
    fn from_snapshot(snapshot: SolveLimitKindSnapshot) -> Self {
        match snapshot {
            SolveLimitKindSnapshot::Timeout => Self::Timeout,
            SolveLimitKindSnapshot::MemoryLimit => Self::MemoryLimit,
            SolveLimitKindSnapshot::TermMemoryLimit => Self::TermMemoryLimit,
            SolveLimitKindSnapshot::LearnedClauseLimit => Self::LearnedClauseLimit,
            SolveLimitKindSnapshot::ClauseDbBytesLimit => Self::ClauseDbBytesLimit,
            SolveLimitKindSnapshot::Interrupted => Self::Interrupted,
            SolveLimitKindSnapshot::Unknown => Self::Unknown,
        }
    }

    fn into_snapshot(self) -> SolveLimitKindSnapshot {
        match self {
            Self::Timeout => SolveLimitKindSnapshot::Timeout,
            Self::MemoryLimit => SolveLimitKindSnapshot::MemoryLimit,
            Self::TermMemoryLimit => SolveLimitKindSnapshot::TermMemoryLimit,
            Self::LearnedClauseLimit => SolveLimitKindSnapshot::LearnedClauseLimit,
            Self::ClauseDbBytesLimit => SolveLimitKindSnapshot::ClauseDbBytesLimit,
            Self::Interrupted => SolveLimitKindSnapshot::Interrupted,
            Self::Unknown => SolveLimitKindSnapshot::Unknown,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) enum WireEncodingError {
    Unsupported {
        message: String,
        span: Option<WireSourceSpan>,
        contract_text: Option<String>,
    },
    SortInference {
        context: String,
        detail: String,
        span: Option<WireSourceSpan>,
    },
    SortConflict {
        context: String,
        declared_sort: String,
        requested_sort: String,
        span: Option<WireSourceSpan>,
    },
    SolverError {
        message: String,
        span: Option<WireSourceSpan>,
    },
}

impl WireEncodingError {
    fn from_error(error: &EncodingError) -> Self {
        match error {
            EncodingError::Unsupported {
                message,
                span,
                contract_text,
            } => Self::Unsupported {
                message: message.clone(),
                span: span.as_ref().map(WireSourceSpan::from_span),
                contract_text: contract_text.clone(),
            },
            EncodingError::SortInference {
                context,
                detail,
                span,
            } => Self::SortInference {
                context: context.clone(),
                detail: detail.clone(),
                span: span.as_ref().map(WireSourceSpan::from_span),
            },
            EncodingError::SortConflict {
                context,
                declared_sort,
                requested_sort,
                span,
            } => Self::SortConflict {
                context: context.clone(),
                declared_sort: declared_sort.clone(),
                requested_sort: requested_sort.clone(),
                span: span.as_ref().map(WireSourceSpan::from_span),
            },
            EncodingError::SolverError { message, span } => Self::SolverError {
                message: message.clone(),
                span: span.as_ref().map(WireSourceSpan::from_span),
            },
        }
    }

    pub(crate) fn into_error(self) -> Result<EncodingError, String> {
        Ok(match self {
            Self::Unsupported {
                message,
                span,
                contract_text,
            } => EncodingError::Unsupported {
                message,
                span: span.map(WireSourceSpan::into_span).transpose()?,
                contract_text,
            },
            Self::SortInference {
                context,
                detail,
                span,
            } => EncodingError::SortInference {
                context,
                detail,
                span: span.map(WireSourceSpan::into_span).transpose()?,
            },
            Self::SortConflict {
                context,
                declared_sort,
                requested_sort,
                span,
            } => EncodingError::SortConflict {
                context,
                declared_sort,
                requested_sort,
                span: span.map(WireSourceSpan::into_span).transpose()?,
            },
            Self::SolverError { message, span } => EncodingError::SolverError {
                message,
                span: span.map(WireSourceSpan::into_span).transpose()?,
            },
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct WireSourceSpan {
    file: Option<String>,
    start: usize,
    end: usize,
    line: Option<u32>,
    column: Option<u32>,
}

impl WireSourceSpan {
    fn from_span(span: &SourceSpan) -> Self {
        Self {
            file: span.file.clone(),
            start: span.start,
            end: span.end,
            line: span.line,
            column: span.column,
        }
    }

    fn into_span(self) -> Result<SourceSpan, String> {
        Ok(SourceSpan {
            file: self.file,
            start: self.start,
            end: self.end,
            line: self.line,
            column: self.column,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn process_wire_refuses_unsupported_typed_values_instead_of_erasing_them() {
        let wide = ModelValue::FloatingPointWide {
            sign: false,
            exponent: 1,
            significand: 1 << 100,
            eb: 15,
            sb: 113,
        };
        for value in [
            wide.clone(),
            ModelValue::Array {
                default: Box::new(wide.clone()),
                stores: vec![],
            },
            ModelValue::Datatype {
                constructor: "box".into(),
                args: vec![wide.clone()],
            },
            ModelValue::Seq(vec![wide]),
        ] {
            let outcome = VerificationOutcome::without_provenance(VerificationResult::Failed(
                Counterexample {
                    values: vec![CounterexampleValue {
                        name: "value".into(),
                        value,
                        origin: None,
                    }],
                    violated_postcondition: None,
                },
            ));
            assert!(WireVerificationOutcome::from_outcome(&outcome).is_err());
            let baseline = unsoundness::snapshot();
            assert!(matches!(
                WireChildMessage::from_result(Ok(outcome), &baseline),
                WireChildMessage::Error {
                    error: WireEncodingError::Unsupported { .. },
                    ..
                }
            ));
        }
        assert!(matches!(
            WireModelValue::from_model_value(&ModelValue::Unknown),
            Ok(WireModelValue::Unknown)
        ));
    }

    #[test]
    fn process_wire_loop_refuses_a_lossy_optional_counterexample() {
        let verified =
            || VerificationOutcome::without_provenance(VerificationResult::Verified(None));
        let failed =
            VerificationOutcome::without_provenance(VerificationResult::Failed(Counterexample {
                values: vec![CounterexampleValue {
                    name: "wide".into(),
                    value: ModelValue::FloatingPointWide {
                        sign: false,
                        exponent: 1,
                        significand: 1 << 100,
                        eb: 15,
                        sb: 113,
                    },
                    origin: None,
                }],
                violated_postcondition: None,
            }));
        let outcome = LoopVerificationOutcome {
            initialization: verified(),
            preservation: verified(),
            postcondition: verified(),
            variant_nonneg: None,
            variant_decrease: Some(failed),
            entry_may_execute: None,
        };
        let baseline = unsoundness::snapshot();
        assert!(matches!(
            WireLoopChildMessage::from_result(Ok(outcome), &baseline),
            WireLoopChildMessage::Error {
                error: WireEncodingError::Unsupported { .. },
                ..
            }
        ));
    }

    /// `BigRational::new` panics on a zero denominator, and this value is
    /// decoded straight from the solver child's wire message — a child that
    /// emitted "0" took the parent process down with it. It must be an error,
    /// which is what every other malformed field on this path already is.
    #[test]
    fn a_zero_denominator_from_the_child_is_an_error_not_a_panic() {
        let wire = WireModelValue::Real {
            numerator: "1".to_string(),
            denominator: "0".to_string(),
        };
        let error = wire
            .into_model_value()
            .expect_err("a zero denominator must not be accepted");
        assert!(error.contains("zero denominator"), "{error}");

        // A well-formed rational still decodes.
        let ok = WireModelValue::Real {
            numerator: "3".to_string(),
            denominator: "4".to_string(),
        };
        assert!(ok.into_model_value().is_ok());
    }

    #[test]
    fn process_wire_roundtrips_outcome_with_native_replay_json() {
        let provenance = VerificationProvenance::with_solve_time(Duration::from_millis(42))
            .with_assertion_count(7)
            .with_unknown_reason(Some(UnknownReason::Timeout))
            .with_native_replay_json(Some("{\"schema\":\"ay.native-replay.v1\"}".to_string()));
        let outcome = VerificationOutcome::new(
            VerificationResult::Unknown(UnknownReason::Timeout),
            Some(provenance),
        );

        let wire = WireVerificationOutcome::from_outcome(&outcome).unwrap();
        let encoded = serde_json::to_string(&wire).expect("encode wire outcome");
        let decoded: WireVerificationOutcome =
            serde_json::from_str(&encoded).expect("decode wire outcome");
        let roundtrip = decoded.into_outcome().expect("wire outcome conversion");

        assert!(matches!(
            roundtrip.result,
            VerificationResult::Unknown(UnknownReason::Timeout)
        ));
        let provenance = roundtrip.provenance.expect("provenance");
        assert_eq!(provenance.assertion_count, 7);
        assert_eq!(
            provenance.native_replay_json.as_deref(),
            Some("{\"schema\":\"ay.native-replay.v1\"}")
        );
    }

    #[test]
    fn process_wire_roundtrips_self_check_rejection() {
        let outcome = VerificationOutcome::without_provenance(VerificationResult::Unknown(
            UnknownReason::SelfCheckRejected,
        ));

        let wire = WireVerificationOutcome::from_outcome(&outcome).unwrap();
        let encoded = serde_json::to_string(&wire).expect("encode wire outcome");
        let decoded: WireVerificationOutcome =
            serde_json::from_str(&encoded).expect("decode wire outcome");
        let roundtrip = decoded.into_outcome().expect("wire outcome conversion");

        assert!(matches!(
            roundtrip.result,
            VerificationResult::Unknown(UnknownReason::SelfCheckRejected)
        ));
    }

    #[test]
    fn process_wire_roundtrips_failed_counterexample_model_values() {
        let counterexample = Counterexample {
            values: vec![
                CounterexampleValue {
                    name: "i".to_string(),
                    value: ModelValue::Int(BigInt::from(3)),
                    origin: Some(VarOrigin::Parameter {
                        name: "i".to_string(),
                        span: Some(SourceSpan::with_location("demo.rs", 1, 2)),
                    }),
                },
                CounterexampleValue {
                    name: "seq".to_string(),
                    value: ModelValue::Seq(vec![ModelValue::Bool(true)]),
                    origin: None,
                },
            ],
            violated_postcondition: Some(PostconditionInfo {
                clause_idx: 1,
                contract_text: "result > i".to_string(),
                span: Some(SourceSpan::from_contract(2, 9)),
            }),
        };
        let outcome =
            VerificationOutcome::without_provenance(VerificationResult::Failed(counterexample));

        let wire = WireVerificationOutcome::from_outcome(&outcome).unwrap();
        let encoded = serde_json::to_string(&wire).expect("encode wire outcome");
        let decoded: WireVerificationOutcome =
            serde_json::from_str(&encoded).expect("decode wire outcome");
        let roundtrip = decoded.into_outcome().expect("wire outcome conversion");

        let VerificationResult::Failed(counterexample) = roundtrip.result else {
            panic!("expected failed result");
        };
        assert_eq!(counterexample.values.len(), 2);
        assert!(matches!(
            counterexample.values[0].origin,
            Some(VarOrigin::Parameter { .. })
        ));
        assert_eq!(
            counterexample
                .violated_postcondition
                .as_ref()
                .map(|info| info.clause_idx),
            Some(1)
        );
    }

    /// The rendered Alethe proof text survives a JSON round-trip through the
    /// wire layer.
    #[test]
    fn wire_proof_certificate_summary_roundtrips_alethe_text() {
        let proof_text = "(assume h1 (= a b))\n(step t1 (cl (= a b)) :rule assume)".to_string();
        let summary = ProofCertificateSummary {
            strict_verified: true,
            restricted_rule_subset: true,
            trust_count: 0,
            trust_fallback_count: 0,
            hole_count: 0,
            theory_lemma_count: 0,
            resolution_count: 3,
            farkas_certificate_count: 0,
            lrat_present: false,
            alethe_text: Some(proof_text.clone()),
        };
        let outcome = VerificationOutcome::without_provenance(
            VerificationResult::verified_with_proof(summary),
        );

        let wire = WireVerificationOutcome::from_outcome(&outcome).unwrap();
        let encoded = serde_json::to_string(&wire).expect("encode wire outcome");
        let decoded: WireVerificationOutcome =
            serde_json::from_str(&encoded).expect("decode wire outcome");
        let roundtrip = decoded.into_outcome().expect("wire outcome conversion");

        let VerificationResult::Verified(Some(roundtripped)) = roundtrip.result else {
            panic!("expected Verified(Some(...)) after roundtrip");
        };
        assert_eq!(
            roundtripped.alethe_text.as_deref(),
            Some(proof_text.as_str()),
            "alethe_text must roundtrip verbatim through serde wire layer"
        );
    }

    /// The strict replay's recorded WITHHOLDING REASON must survive the worker
    /// process boundary.
    ///
    /// The parent process is where a corpus census actually reads these keys, so
    /// a reason captured in the worker and dropped on the wire is indistinguishable
    /// from one that was never recorded — which is precisely the confusion these
    /// fields exist to end. Pins `unknown_reason`/`unknown_detail` across the
    /// serde boundary alongside `unsat_proof_decline`, whose structural `None`
    /// alone cannot say why the replay was withheld.
    #[test]
    fn wire_strict_proof_replay_roundtrips_the_recorded_unknown_reason() {
        let evidence = SolveEvidenceSnapshot {
            result: "unknown".to_string(),
            model_validated: false,
            accepted_for_consumer: false,
            consumer_rejection: None,
            verification: SolveVerificationSnapshot::default(),
            verification_level: SolveVerificationLevelSnapshot::ProofChecked,
            resource_usage: SolveResourceSnapshot::default(),
        };
        let observation = StrictProofReplayObservation {
            evidence,
            statistics: SolveStatisticsSnapshot::default(),
            authority_accepted: false,
            unsat_proof_decline: None,
            unknown_reason: Some("self_check_rejected".to_string()),
            unknown_detail: Some(
                "computed UNSAT rejected by mandatory strict certification: \
                 step t0 uses unverified trust rule"
                    .to_string(),
            ),
        };
        let provenance = VerificationProvenance::with_solve_time(Duration::from_millis(3))
            .with_strict_proof_replay(Some(observation.clone()));
        let outcome = VerificationOutcome::new(
            VerificationResult::Unknown(UnknownReason::ProofTrusted),
            Some(provenance),
        );

        let wire = WireVerificationOutcome::from_outcome(&outcome).unwrap();
        let encoded = serde_json::to_string(&wire).expect("encode wire outcome");
        let decoded: WireVerificationOutcome =
            serde_json::from_str(&encoded).expect("decode wire outcome");
        let roundtrip = decoded.into_outcome().expect("wire outcome conversion");

        let replayed = roundtrip
            .provenance
            .as_ref()
            .and_then(|provenance| provenance.strict_proof_replay.as_ref())
            .expect("the strict replay observation must survive the wire");
        assert_eq!(
            replayed, &observation,
            "the observation must roundtrip verbatim"
        );
        assert_eq!(
            replayed.unknown_reason.as_deref(),
            Some("self_check_rejected")
        );
        assert!(
            replayed
                .unknown_detail
                .as_deref()
                .is_some_and(|detail| detail.contains("unverified trust rule")),
            "the instance-specific detail names the offending step and must not be \
             truncated to the categorical code"
        );
    }

    /// A worker built before these fields existed still deserializes, reporting
    /// no recorded reason — which is exactly what it measured.
    ///
    /// Built by stripping the two keys from a CURRENT payload rather than by
    /// pasting a frozen legacy document, so the test keeps testing the thing it
    /// names when unrelated wire fields change.
    #[test]
    fn wire_strict_proof_replay_defaults_unknown_reason_when_absent() {
        let observation = StrictProofReplayObservation {
            evidence: SolveEvidenceSnapshot {
                result: "unknown".to_string(),
                model_validated: false,
                accepted_for_consumer: false,
                consumer_rejection: None,
                verification: SolveVerificationSnapshot::default(),
                verification_level: SolveVerificationLevelSnapshot::ProofChecked,
                resource_usage: SolveResourceSnapshot::default(),
            },
            statistics: SolveStatisticsSnapshot::default(),
            authority_accepted: false,
            unsat_proof_decline: None,
            unknown_reason: Some("proof_trusted".to_string()),
            unknown_detail: Some("detail".to_string()),
        };
        let wire = WireStrictProofReplayObservation::from_observation(&observation);
        let mut encoded: serde_json::Value =
            serde_json::to_value(&wire).expect("encode observation");
        let object = encoded
            .as_object_mut()
            .expect("observation is a JSON object");
        assert!(
            object.remove("unknown_reason").is_some() && object.remove("unknown_detail").is_some(),
            "precondition: the current payload carries both keys"
        );

        let decoded: WireStrictProofReplayObservation =
            serde_json::from_value(encoded).expect("a payload without the keys must still decode");
        let roundtrip = decoded
            .into_observation()
            .expect("observation must convert");
        assert!(roundtrip.unknown_reason.is_none());
        assert!(roundtrip.unknown_detail.is_none());
    }

    /// Legacy payloads that omit `alethe_text` deserialize to `None` thanks
    /// to `#[serde(default)]`. Guards forward compatibility for older child
    /// processes that predate the field.
    #[test]
    fn wire_proof_certificate_summary_defaults_alethe_text_when_absent() {
        let legacy_json = r#"{
            "strict_verified": true,
            "restricted_rule_subset": false,
            "trust_count": 0,
            "trust_fallback_count": 0,
            "hole_count": 0,
            "theory_lemma_count": 0,
            "resolution_count": 7,
            "farkas_certificate_count": 0,
            "lrat_present": false
        }"#;
        let decoded: WireProofCertificateSummary =
            serde_json::from_str(legacy_json).expect("legacy payload must decode");
        let summary = decoded.into_summary();
        assert!(
            summary.alethe_text.is_none(),
            "missing alethe_text in payload should deserialize to None"
        );
        assert_eq!(summary.resolution_count, 7);
    }
}
