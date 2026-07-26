// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{borrow::Cow, error::Error, fmt};

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

use super::{
    decode_trust_formula_v1_claim, BundleClaim, BundleClaimFormat, BundleDiagnostic,
    BundleNativeOrigin, BundleNativeToolIdentity, BundleObligation, BundleObligationKind,
    BundleObligationMetadata, BundleProducer, BundleProofContext, BundleSourceSpan,
    BundleSummaryFact, BundleTarget, BundleTmirObligationSource, BundleTmirSourceSpan,
    VerifyBundleOptions, VerifyBundleRequest, TRUST_FORMULA_CLAIM_SCHEMA_VERSION,
};

/// Stable schema tag for the first direct Trust/tMIR adapter input.
pub const TRUST_TMIR_ADAPTER_SCHEMA_VERSION: &str = "trust-wp.trust-tmir-adapter.v1";

const TRUST_TMIR_PRODUCER_NAME: &str = "trust-tmir";

/// Direct compiler bundle emitted by Trust/tMIR before trust-wp verification.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustTmirBundle {
    pub schema: String,
    pub bundle_id: String,
    pub producer: BundleProducer,
    pub target: BundleTarget,
    pub function: String,
    #[serde(default)]
    pub obligations: Vec<TrustTmirObligation>,
    #[serde(default)]
    pub options: VerifyBundleOptions,
}

impl TrustTmirBundle {
    /// Create a Trust/tMIR bundle for one function.
    #[must_use]
    pub fn new(
        bundle_id: impl Into<String>,
        crate_name: impl Into<String>,
        function: impl Into<String>,
    ) -> Self {
        Self {
            schema: TRUST_TMIR_ADAPTER_SCHEMA_VERSION.to_string(),
            bundle_id: bundle_id.into(),
            producer: BundleProducer::new(TRUST_TMIR_PRODUCER_NAME),
            target: BundleTarget::new(crate_name),
            function: function.into(),
            obligations: Vec::new(),
            options: VerifyBundleOptions::default(),
        }
    }

    /// Add one tMIR obligation.
    #[must_use]
    pub fn with_obligation(mut self, obligation: TrustTmirObligation) -> Self {
        self.obligations.push(obligation);
        self
    }

    /// Replace verification options.
    #[must_use]
    pub fn with_options(mut self, options: VerifyBundleOptions) -> Self {
        self.options = options;
        self
    }

    /// Convert this adapter bundle into trust-wp's native verification request.
    pub fn into_verify_bundle_request(self) -> Result<VerifyBundleRequest, TrustTmirAdapterError> {
        trust_tmir_to_verify_bundle(self)
    }

    /// Convert this adapter bundle after enforcing deterministic adapter work budgets.
    pub fn into_verify_bundle_request_with_budget(
        self,
        budget: &TrustTmirAdapterBudget,
    ) -> Result<VerifyBundleRequest, TrustTmirAdapterError> {
        trust_tmir_to_verify_bundle_with_budget(self, budget)
    }

    /// Count deterministic adapter work before handing the request to a verifier.
    pub fn adapter_metrics(&self) -> Result<TrustTmirAdapterMetrics, TrustTmirAdapterError> {
        trust_tmir_adapter_metrics(self)
    }

    /// Count adapter work and fail closed when any configured budget is exceeded.
    pub fn checked_adapter_metrics(
        &self,
        budget: &TrustTmirAdapterBudget,
    ) -> Result<TrustTmirAdapterMetrics, TrustTmirAdapterError> {
        self.adapter_metrics()?.checked_against(budget)
    }
}

/// Deterministic work limits for the direct Trust/tMIR adapter path.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustTmirAdapterBudget {
    pub max_obligations: usize,
    pub max_bindings: usize,
    pub max_expr_nodes: usize,
    pub max_expr_depth: usize,
    pub max_payload_bytes: usize,
    pub max_summary_facts: usize,
    pub max_source_locations: usize,
}

impl Default for TrustTmirAdapterBudget {
    fn default() -> Self {
        Self {
            max_obligations: 64,
            max_bindings: 256,
            max_expr_nodes: 4_096,
            max_expr_depth: 64,
            max_payload_bytes: 262_144,
            max_summary_facts: 256,
            max_source_locations: 64,
        }
    }
}

/// Deterministic work observed while preparing a direct Trust/tMIR request.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustTmirAdapterMetrics {
    pub obligations: usize,
    pub bindings: usize,
    pub expr_nodes: usize,
    pub max_expr_depth: usize,
    pub payload_bytes: usize,
    pub summary_facts: usize,
    pub source_locations: usize,
}

impl TrustTmirAdapterMetrics {
    /// Fail closed when the observed adapter work exceeds the configured budget.
    pub fn checked_against(
        self,
        budget: &TrustTmirAdapterBudget,
    ) -> Result<Self, TrustTmirAdapterError> {
        let mut diagnostics = Vec::new();

        push_budget_diagnostic(
            &mut diagnostics,
            "obligations",
            self.obligations,
            budget.max_obligations,
        );
        push_budget_diagnostic(
            &mut diagnostics,
            "bindings",
            self.bindings,
            budget.max_bindings,
        );
        push_budget_diagnostic(
            &mut diagnostics,
            "expr_nodes",
            self.expr_nodes,
            budget.max_expr_nodes,
        );
        push_budget_diagnostic(
            &mut diagnostics,
            "max_expr_depth",
            self.max_expr_depth,
            budget.max_expr_depth,
        );
        push_budget_diagnostic(
            &mut diagnostics,
            "payload_bytes",
            self.payload_bytes,
            budget.max_payload_bytes,
        );
        push_budget_diagnostic(
            &mut diagnostics,
            "summary_facts",
            self.summary_facts,
            budget.max_summary_facts,
        );
        push_budget_diagnostic(
            &mut diagnostics,
            "source_locations",
            self.source_locations,
            budget.max_source_locations,
        );

        if diagnostics.is_empty() {
            Ok(self)
        } else {
            Err(TrustTmirAdapterError::new(diagnostics))
        }
    }
}

/// One Trust/tMIR proof obligation before conversion to trust-wp's bundle API.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustTmirObligation {
    pub id: String,
    pub kind: BundleObligationKind,
    pub formula: TrustTmirFormula,
    #[serde(default)]
    pub location: Option<BundleSourceSpan>,
    #[serde(default)]
    pub metadata: BundleObligationMetadata,
    #[serde(default)]
    pub summary_facts: Vec<BundleSummaryFact>,
}

impl TrustTmirObligation {
    /// Create one Trust/tMIR obligation.
    #[must_use]
    pub fn new(
        id: impl Into<String>,
        kind: BundleObligationKind,
        formula: TrustTmirFormula,
    ) -> Self {
        Self {
            id: id.into(),
            kind,
            formula,
            location: None,
            metadata: BundleObligationMetadata::default(),
            summary_facts: Vec::new(),
        }
    }

    /// Attach a source location.
    #[must_use]
    pub fn with_location(mut self, location: BundleSourceSpan) -> Self {
        self.location = Some(location);
        self
    }

    /// Attach typed provenance and proof-context metadata.
    #[must_use]
    pub fn with_metadata(mut self, metadata: BundleObligationMetadata) -> Self {
        self.metadata = metadata;
        self
    }

    /// Attach typed native-origin metadata.
    #[must_use]
    pub fn with_native_origin(mut self, origin: BundleNativeOrigin) -> Self {
        self.metadata.native_origin = Some(origin);
        self
    }

    /// Attach a typed tMIR source span.
    #[must_use]
    pub fn with_tmir_source_span(mut self, span: BundleTmirSourceSpan) -> Self {
        self.metadata.tmir_source_span = Some(span);
        self
    }

    /// Attach typed native verifier provenance.
    #[must_use]
    pub fn with_native_verifier(mut self, verifier: BundleNativeToolIdentity) -> Self {
        self.metadata.native_verifier = Some(verifier);
        self
    }

    /// Attach typed native solver/prover provenance.
    #[must_use]
    pub fn with_native_solver(mut self, solver: BundleNativeToolIdentity) -> Self {
        self.metadata.native_solvers.push(solver);
        self
    }

    /// Attach typed native solver/prover provenance.
    #[must_use]
    pub fn with_native_solvers(
        mut self,
        solvers: impl IntoIterator<Item = BundleNativeToolIdentity>,
    ) -> Self {
        self.metadata.native_solvers.extend(solvers);
        self
    }

    /// Attach typed tMIR obligation source/fact-reference metadata.
    #[must_use]
    pub fn with_tmir_obligation_source(mut self, source: BundleTmirObligationSource) -> Self {
        self.metadata.tmir_obligation_source = Some(source);
        self
    }

    /// Attach producer-supplied assumption/assertion context.
    #[must_use]
    pub fn with_proof_context(mut self, context: BundleProofContext) -> Self {
        self.metadata.proof_context = context;
        self
    }

    /// Attach one producer-supplied summary fact.
    #[must_use]
    pub fn with_summary_fact(mut self, fact: BundleSummaryFact) -> Self {
        self.summary_facts.push(fact);
        self
    }
}

/// Typed Trust formula payload accepted by the direct tMIR adapter.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustTmirFormula {
    #[serde(default)]
    pub variables: Vec<TrustTmirBinding>,
    #[serde(default)]
    pub result: Option<TrustTmirBinding>,
    pub body: TrustTmirExpr,
}

impl TrustTmirFormula {
    /// Create a formula with no declared variables or result binding.
    #[must_use]
    pub fn new(body: TrustTmirExpr) -> Self {
        Self {
            variables: Vec::new(),
            result: None,
            body,
        }
    }

    /// Declare one input variable.
    #[must_use]
    pub fn with_variable(mut self, name: impl Into<String>, sort: TrustTmirSort) -> Self {
        self.variables.push(TrustTmirBinding::new(name, sort));
        self
    }

    /// Declare the default `result` binding.
    #[must_use]
    pub fn with_result(mut self, sort: TrustTmirSort) -> Self {
        self.result = Some(TrustTmirBinding::new("result", sort));
        self
    }

    /// Declare a named result binding.
    #[must_use]
    pub fn with_named_result(mut self, name: impl Into<String>, sort: TrustTmirSort) -> Self {
        self.result = Some(TrustTmirBinding::new(name, sort));
        self
    }

    fn to_trust_formula_payload(&self) -> Result<String, Vec<BundleDiagnostic>> {
        let mut diagnostics = Vec::new();
        let mut object = serde_json::Map::new();
        object.insert(
            "schema".to_string(),
            json!(TRUST_FORMULA_CLAIM_SCHEMA_VERSION),
        );

        if !self.variables.is_empty() {
            object.insert(
                "variables".to_string(),
                Value::Array(
                    self.variables
                        .iter()
                        .map(|binding| binding.to_trust_formula_value(&mut diagnostics))
                        .collect(),
                ),
            );
        }

        if let Some(result) = &self.result {
            object.insert(
                "result".to_string(),
                result.to_trust_formula_value(&mut diagnostics),
            );
        }

        object.insert(
            "body".to_string(),
            self.body.to_trust_formula_value(&mut diagnostics),
        );

        if !diagnostics.is_empty() {
            return Err(diagnostics);
        }

        let payload = Value::Object(object).to_string();
        if let Err(err) = decode_trust_formula_v1_claim(&payload) {
            return Err(vec![BundleDiagnostic::invalid(
                "trust_tmir.formula",
                format!("adapter emitted invalid TrustFormulaV1 payload: {err}"),
            )]);
        }
        Ok(payload)
    }

    fn adapter_metrics(&self) -> Result<TrustTmirFormulaMetrics, Vec<BundleDiagnostic>> {
        let payload = self.to_trust_formula_payload()?;
        Ok(self.adapter_metrics_from_payload(payload.len()))
    }

    fn adapter_metrics_from_payload(&self, payload_bytes: usize) -> TrustTmirFormulaMetrics {
        TrustTmirFormulaMetrics {
            bindings: self.variables.len() + usize::from(self.result.is_some()),
            expr_nodes: self.body.node_count(),
            max_expr_depth: self.body.max_depth(),
            payload_bytes,
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct TrustTmirFormulaMetrics {
    bindings: usize,
    expr_nodes: usize,
    max_expr_depth: usize,
    payload_bytes: usize,
}

/// A Trust/tMIR variable or result binding.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustTmirBinding {
    pub name: String,
    pub sort: TrustTmirSort,
}

impl TrustTmirBinding {
    /// Create a Trust/tMIR binding.
    #[must_use]
    pub fn new(name: impl Into<String>, sort: TrustTmirSort) -> Self {
        Self {
            name: name.into(),
            sort,
        }
    }

    fn to_trust_formula_value(&self, diagnostics: &mut Vec<BundleDiagnostic>) -> Value {
        if let Some(sort) = self.sort.to_trust_formula_sort() {
            json!({ "name": self.name, "sort": sort })
        } else {
            diagnostics.push(BundleDiagnostic::unsupported(
                "trust_tmir.sort",
                format!(
                    "binding `{}` uses unsupported tMIR sort `{}`",
                    self.name,
                    self.sort.as_label()
                ),
            ));
            json!({ "name": self.name, "sort": self.sort.as_label() })
        }
    }
}

/// First-slice Trust/tMIR sorts admitted by the native replay adapter.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TrustTmirSort {
    Int,
    Bool,
    Seq,
    TypeParam(String),
    Ref(Box<TrustTmirSort>),
    MutRef(Box<TrustTmirSort>),
    Other(String),
}

impl TrustTmirSort {
    /// Opaque type-parameter sort such as `T`.
    #[must_use]
    pub fn type_param(name: impl Into<String>) -> Self {
        Self::TypeParam(name.into())
    }

    /// Shared reference sort.
    #[must_use]
    pub fn shared_ref(inner: Self) -> Self {
        Self::Ref(Box::new(inner))
    }

    /// Mutable reference sort.
    #[must_use]
    pub fn mut_ref(inner: Self) -> Self {
        Self::MutRef(Box::new(inner))
    }

    /// Shared slice reference sort. Native replay treats this as a fat pointer.
    #[must_use]
    pub fn shared_slice() -> Self {
        Self::shared_ref(Self::Seq)
    }

    fn to_trust_formula_sort(&self) -> Option<String> {
        match self {
            Self::Int => Some("int".to_string()),
            Self::Bool => Some("bool".to_string()),
            Self::Seq => Some("Seq".to_string()),
            Self::TypeParam(name) if is_tmir_type_param_name(name) => Some(name.clone()),
            Self::Ref(inner) => Some(format!("&{}", inner.as_type_annotation()?)),
            Self::MutRef(inner) => Some(format!("&mut {}", inner.as_type_annotation()?)),
            Self::TypeParam(_) | Self::Other(_) => None,
        }
    }

    fn as_type_annotation(&self) -> Option<Cow<'_, str>> {
        match self {
            Self::Int => Some(Cow::Borrowed("Int")),
            Self::Bool => Some(Cow::Borrowed("bool")),
            Self::Seq => Some(Cow::Borrowed("[T]")),
            Self::TypeParam(name) if is_tmir_type_param_name(name) => {
                Some(Cow::Borrowed(name.as_str()))
            }
            Self::Ref(inner) => Some(Cow::Owned(format!("&{}", inner.as_type_annotation()?))),
            Self::MutRef(inner) => {
                Some(Cow::Owned(format!("&mut {}", inner.as_type_annotation()?)))
            }
            Self::TypeParam(_) | Self::Other(_) => None,
        }
    }

    fn as_label(&self) -> Cow<'_, str> {
        match self {
            Self::Int => Cow::Borrowed("int"),
            Self::Bool => Cow::Borrowed("bool"),
            Self::Seq => Cow::Borrowed("seq"),
            Self::TypeParam(name) => Cow::Borrowed(name.as_str()),
            Self::Ref(inner) => Cow::Owned(format!("&{}", inner.as_label())),
            Self::MutRef(inner) => Cow::Owned(format!("&mut {}", inner.as_label())),
            Self::Other(sort) => Cow::Borrowed(sort.as_str()),
        }
    }
}

fn is_tmir_type_param_name(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(
        (chars.next(), chars.next()),
        (Some(ch), None) if ch.is_ascii_uppercase()
    )
}

/// Typed expression fragment accepted by the direct tMIR adapter.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "kind")]
pub enum TrustTmirExpr {
    Bool {
        value: bool,
    },
    Int {
        value: i64,
    },
    Var {
        name: String,
    },
    Result,
    Old {
        expr: Box<TrustTmirExpr>,
    },
    Let {
        name: String,
        sort: TrustTmirSort,
        value: Box<TrustTmirExpr>,
        body: Box<TrustTmirExpr>,
    },
    Forall {
        name: String,
        sort: TrustTmirSort,
        body: Box<TrustTmirExpr>,
    },
    Exists {
        name: String,
        sort: TrustTmirSort,
        body: Box<TrustTmirExpr>,
    },
    Unary {
        op: TrustTmirUnaryOp,
        expr: Box<TrustTmirExpr>,
    },
    Binary {
        op: TrustTmirBinOp,
        lhs: Box<TrustTmirExpr>,
        rhs: Box<TrustTmirExpr>,
    },
    Unsupported {
        reason: String,
    },
}

impl TrustTmirExpr {
    /// Boolean literal.
    #[must_use]
    pub const fn bool(value: bool) -> Self {
        Self::Bool { value }
    }

    /// Integer literal.
    #[must_use]
    pub const fn int(value: i64) -> Self {
        Self::Int { value }
    }

    /// Variable reference.
    #[must_use]
    pub fn var(name: impl Into<String>) -> Self {
        Self::Var { name: name.into() }
    }

    /// Result reference.
    #[must_use]
    pub const fn result() -> Self {
        Self::Result
    }

    /// Old-value reference.
    #[must_use]
    pub fn old(expr: Self) -> Self {
        Self::Old {
            expr: Box::new(expr),
        }
    }

    /// Scoped let binding.
    #[must_use]
    pub fn let_bind(name: impl Into<String>, sort: TrustTmirSort, value: Self, body: Self) -> Self {
        Self::Let {
            name: name.into(),
            sort,
            value: Box::new(value),
            body: Box::new(body),
        }
    }

    /// Universal quantifier over a typed tMIR binding.
    #[must_use]
    pub fn forall(name: impl Into<String>, sort: TrustTmirSort, body: Self) -> Self {
        Self::Forall {
            name: name.into(),
            sort,
            body: Box::new(body),
        }
    }

    /// Existential quantifier over a typed tMIR binding.
    #[must_use]
    pub fn exists(name: impl Into<String>, sort: TrustTmirSort, body: Self) -> Self {
        Self::Exists {
            name: name.into(),
            sort,
            body: Box::new(body),
        }
    }

    /// Unary operation.
    #[must_use]
    pub fn unary(op: TrustTmirUnaryOp, expr: Self) -> Self {
        Self::Unary {
            op,
            expr: Box::new(expr),
        }
    }

    /// Binary operation.
    #[must_use]
    pub fn binary(op: TrustTmirBinOp, lhs: Self, rhs: Self) -> Self {
        Self::Binary {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }

    /// Unsupported tMIR expression node placeholder.
    #[must_use]
    pub fn unsupported(reason: impl Into<String>) -> Self {
        Self::Unsupported {
            reason: reason.into(),
        }
    }

    fn to_trust_formula_value(&self, diagnostics: &mut Vec<BundleDiagnostic>) -> Value {
        match self {
            Self::Bool { value } => json!({ "bool": value }),
            Self::Int { value } => json!({ "int": value }),
            Self::Var { name } => json!({ "var": name }),
            Self::Result => json!({ "result": true }),
            Self::Old { expr } => json!({ "old": expr.to_trust_formula_value(diagnostics) }),
            Self::Let {
                name,
                sort,
                value,
                body,
            } => {
                if let Some(sort) = sort.to_trust_formula_sort() {
                    json!({
                        "op": "let",
                        "name": name,
                        "sort": sort,
                        "value": value.to_trust_formula_value(diagnostics),
                        "body": body.to_trust_formula_value(diagnostics),
                    })
                } else {
                    diagnostics.push(BundleDiagnostic::unsupported(
                        "trust_tmir.sort",
                        format!(
                            "let binding `{name}` uses unsupported tMIR sort `{}`",
                            sort.as_label()
                        ),
                    ));
                    json!({
                        "op": "let",
                        "name": name,
                        "sort": sort.as_label(),
                        "value": value.to_trust_formula_value(diagnostics),
                        "body": body.to_trust_formula_value(diagnostics),
                    })
                }
            }
            Self::Forall { name, sort, body } | Self::Exists { name, sort, body } => {
                let op = if matches!(self, Self::Forall { .. }) {
                    "forall"
                } else {
                    "exists"
                };
                if let Some(sort) = sort.to_trust_formula_sort() {
                    json!({
                        "op": op,
                        "name": name,
                        "sort": sort,
                        "body": body.to_trust_formula_value(diagnostics),
                    })
                } else {
                    diagnostics.push(BundleDiagnostic::unsupported(
                        "trust_tmir.sort",
                        format!(
                            "{op} binding `{name}` uses unsupported tMIR sort `{}`",
                            sort.as_label()
                        ),
                    ));
                    json!({
                        "op": op,
                        "name": name,
                        "sort": sort.as_label(),
                        "body": body.to_trust_formula_value(diagnostics),
                    })
                }
            }
            Self::Unary { op, expr } => json!({
                "op": op.as_trust_formula_op(),
                "expr": expr.to_trust_formula_value(diagnostics),
            }),
            Self::Binary { op, lhs, rhs } => json!({
                "op": op.as_trust_formula_op(),
                "lhs": lhs.to_trust_formula_value(diagnostics),
                "rhs": rhs.to_trust_formula_value(diagnostics),
            }),
            Self::Unsupported { reason } => {
                diagnostics.push(BundleDiagnostic::unsupported(
                    "trust_tmir.expr",
                    format!("unsupported tMIR expression node: {reason}"),
                ));
                json!({ "unsupported": reason })
            }
        }
    }

    fn node_count(&self) -> usize {
        match self {
            Self::Bool { .. }
            | Self::Int { .. }
            | Self::Var { .. }
            | Self::Result
            | Self::Unsupported { .. } => 1,
            Self::Old { expr } | Self::Unary { expr, .. } => 1 + expr.node_count(),
            Self::Let { value, body, .. } => 1 + value.node_count() + body.node_count(),
            Self::Forall { body, .. } | Self::Exists { body, .. } => 1 + body.node_count(),
            Self::Binary { lhs, rhs, .. } => 1 + lhs.node_count() + rhs.node_count(),
        }
    }

    fn max_depth(&self) -> usize {
        match self {
            Self::Bool { .. }
            | Self::Int { .. }
            | Self::Var { .. }
            | Self::Result
            | Self::Unsupported { .. } => 1,
            Self::Old { expr } | Self::Unary { expr, .. } => 1 + expr.max_depth(),
            Self::Let { value, body, .. } => 1 + value.max_depth().max(body.max_depth()),
            Self::Forall { body, .. } | Self::Exists { body, .. } => 1 + body.max_depth(),
            Self::Binary { lhs, rhs, .. } => 1 + lhs.max_depth().max(rhs.max_depth()),
        }
    }
}

/// Unary operators admitted by the first Trust/tMIR adapter slice.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TrustTmirUnaryOp {
    Not,
    Neg,
}

impl TrustTmirUnaryOp {
    const fn as_trust_formula_op(self) -> &'static str {
        match self {
            Self::Not => "not",
            Self::Neg => "neg",
        }
    }
}

/// Binary operators admitted by the first Trust/tMIR adapter slice.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TrustTmirBinOp {
    Add,
    Sub,
    Mul,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Implies,
}

impl TrustTmirBinOp {
    const fn as_trust_formula_op(self) -> &'static str {
        match self {
            Self::Add => "add",
            Self::Sub => "sub",
            Self::Mul => "mul",
            Self::Eq => "eq",
            Self::Ne => "ne",
            Self::Lt => "lt",
            Self::Le => "le",
            Self::Gt => "gt",
            Self::Ge => "ge",
            Self::And => "and",
            Self::Or => "or",
            Self::Implies => "implies",
        }
    }
}

/// tMIR proof-call precondition VC input.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustTmirProofCall {
    pub schema: String,
    pub bundle_id: String,
    pub producer: BundleProducer,
    pub target: BundleTarget,
    pub caller_function: String,
    pub callee_function: String,
    #[serde(default)]
    pub preconditions: Vec<TrustTmirFormula>,
    #[serde(default)]
    pub location: Option<BundleSourceSpan>,
    #[serde(default)]
    pub summary_facts: Vec<BundleSummaryFact>,
    #[serde(default)]
    pub options: VerifyBundleOptions,
}

impl TrustTmirProofCall {
    /// Create proof-call VC input for one call site.
    #[must_use]
    #[allow(clippy::similar_names)]
    pub fn new(
        bundle_id: impl Into<String>,
        crate_name: impl Into<String>,
        caller_function: impl Into<String>,
        callee_function: impl Into<String>,
    ) -> Self {
        Self {
            schema: TRUST_TMIR_ADAPTER_SCHEMA_VERSION.to_string(),
            bundle_id: bundle_id.into(),
            producer: BundleProducer::new(TRUST_TMIR_PRODUCER_NAME),
            target: BundleTarget::new(crate_name),
            caller_function: caller_function.into(),
            callee_function: callee_function.into(),
            preconditions: Vec::new(),
            location: None,
            summary_facts: Vec::new(),
            options: VerifyBundleOptions::default(),
        }
    }

    /// Add one callee precondition VC.
    #[must_use]
    pub fn with_precondition(mut self, formula: TrustTmirFormula) -> Self {
        self.preconditions.push(formula);
        self
    }

    /// Attach the proof-call source location to emitted VCs.
    #[must_use]
    pub fn with_location(mut self, location: BundleSourceSpan) -> Self {
        self.location = Some(location);
        self
    }

    /// Attach one producer-supplied summary fact to emitted VCs.
    #[must_use]
    pub fn with_summary_fact(mut self, fact: BundleSummaryFact) -> Self {
        self.summary_facts.push(fact);
        self
    }

    /// Replace verification options.
    #[must_use]
    pub fn with_options(mut self, options: VerifyBundleOptions) -> Self {
        self.options = options;
        self
    }
}

/// Error returned when Trust/tMIR adapter input cannot become a valid request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustTmirAdapterError {
    diagnostics: Vec<BundleDiagnostic>,
}

impl TrustTmirAdapterError {
    fn new(diagnostics: Vec<BundleDiagnostic>) -> Self {
        Self { diagnostics }
    }

    /// Structured fail-closed diagnostics.
    #[must_use]
    pub fn diagnostics(&self) -> &[BundleDiagnostic] {
        &self.diagnostics
    }

    /// Consume the error and return its diagnostics.
    #[must_use]
    pub fn into_diagnostics(self) -> Vec<BundleDiagnostic> {
        self.diagnostics
    }
}

impl fmt::Display for TrustTmirAdapterError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let codes = self
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        write!(formatter, "Trust/tMIR adapter rejected input: {codes}")
    }
}

impl Error for TrustTmirAdapterError {}

/// Convert a direct Trust/tMIR bundle into trust-wp's verification request.
pub fn trust_tmir_to_verify_bundle(
    bundle: TrustTmirBundle,
) -> Result<VerifyBundleRequest, TrustTmirAdapterError> {
    trust_tmir_to_verify_bundle_inner(bundle, None)
}

/// Convert a direct Trust/tMIR bundle after enforcing deterministic work budgets.
pub fn trust_tmir_to_verify_bundle_with_budget(
    bundle: TrustTmirBundle,
    budget: &TrustTmirAdapterBudget,
) -> Result<VerifyBundleRequest, TrustTmirAdapterError> {
    trust_tmir_to_verify_bundle_inner(bundle, Some(budget))
}

fn trust_tmir_to_verify_bundle_inner(
    bundle: TrustTmirBundle,
    budget: Option<&TrustTmirAdapterBudget>,
) -> Result<VerifyBundleRequest, TrustTmirAdapterError> {
    let TrustTmirBundle {
        schema,
        bundle_id,
        producer,
        target,
        function,
        obligations,
        options,
    } = bundle;

    let mut diagnostics = validate_adapter_schema(&schema);
    let mut metrics = TrustTmirAdapterMetrics {
        obligations: obligations.len(),
        ..TrustTmirAdapterMetrics::default()
    };
    let mut request = VerifyBundleRequest::new(bundle_id, producer, target).with_options(options);

    for obligation in obligations {
        let TrustTmirObligation {
            id,
            kind,
            formula,
            location,
            metadata,
            summary_facts,
        } = obligation;

        let payload = match formula.to_trust_formula_payload() {
            Ok(payload) => payload,
            Err(formula_diagnostics) => {
                diagnostics.extend(with_obligation_context(&id, formula_diagnostics));
                continue;
            }
        };
        let formula_metrics = formula.adapter_metrics_from_payload(payload.len());
        metrics.bindings += formula_metrics.bindings;
        metrics.expr_nodes += formula_metrics.expr_nodes;
        metrics.max_expr_depth = metrics.max_expr_depth.max(formula_metrics.max_expr_depth);
        metrics.payload_bytes += formula_metrics.payload_bytes;
        metrics.summary_facts += summary_facts.len();
        metrics.source_locations += usize::from(location.is_some());

        let mut bundle_obligation = BundleObligation::new(
            id,
            kind,
            function.clone(),
            BundleClaim::new(BundleClaimFormat::TrustFormulaV1, payload),
        );
        bundle_obligation.location = location;
        bundle_obligation.metadata = metadata;
        bundle_obligation.summary_facts = summary_facts;
        request.obligations.push(bundle_obligation);
    }

    diagnostics.extend(request.validation_diagnostics());
    if diagnostics.is_empty() {
        if let Some(budget) = budget {
            if let Err(err) = metrics.checked_against(budget) {
                diagnostics.extend(err.into_diagnostics());
            }
        }
    }
    if diagnostics.is_empty() {
        Ok(request)
    } else {
        Err(TrustTmirAdapterError::new(diagnostics))
    }
}

/// Compile tMIR proof-call preconditions into trust-wp verification obligations.
pub fn compile_trust_tmir_proof_call_vcs(
    proof_call: TrustTmirProofCall,
) -> Result<VerifyBundleRequest, TrustTmirAdapterError> {
    let TrustTmirProofCall {
        schema,
        bundle_id,
        producer,
        target,
        caller_function,
        callee_function,
        preconditions,
        location,
        summary_facts,
        options,
    } = proof_call;

    let mut diagnostics = validate_adapter_schema(&schema);
    if callee_function.trim().is_empty() {
        diagnostics.push(BundleDiagnostic::invalid(
            "trust_tmir.proof_call.callee_function",
            "proof-call callee function is empty",
        ));
    }
    if preconditions.is_empty() {
        diagnostics.push(BundleDiagnostic::invalid(
            "trust_tmir.proof_call.preconditions",
            "proof-call contains no callee precondition VCs",
        ));
    }
    if !diagnostics.is_empty() {
        return Err(TrustTmirAdapterError::new(diagnostics));
    }

    let mut bundle = TrustTmirBundle {
        schema,
        bundle_id,
        producer,
        target,
        function: caller_function,
        obligations: Vec::new(),
        options,
    };

    for (index, formula) in preconditions.into_iter().enumerate() {
        let mut obligation = TrustTmirObligation::new(
            format!("proof-call:{callee_function}:precondition:{index}"),
            BundleObligationKind::Precondition {
                callee: callee_function.clone(),
            },
            formula,
        );
        obligation.location.clone_from(&location);
        obligation.summary_facts.clone_from(&summary_facts);
        bundle.obligations.push(obligation);
    }

    trust_tmir_to_verify_bundle(bundle)
}

fn trust_tmir_adapter_metrics(
    bundle: &TrustTmirBundle,
) -> Result<TrustTmirAdapterMetrics, TrustTmirAdapterError> {
    let mut diagnostics = validate_adapter_schema(&bundle.schema);
    let mut metrics = TrustTmirAdapterMetrics {
        obligations: bundle.obligations.len(),
        ..TrustTmirAdapterMetrics::default()
    };

    for obligation in &bundle.obligations {
        metrics.summary_facts += obligation.summary_facts.len();
        metrics.source_locations += usize::from(obligation.location.is_some());

        match obligation.formula.adapter_metrics() {
            Ok(formula_metrics) => {
                metrics.bindings += formula_metrics.bindings;
                metrics.expr_nodes += formula_metrics.expr_nodes;
                metrics.max_expr_depth = metrics.max_expr_depth.max(formula_metrics.max_expr_depth);
                metrics.payload_bytes += formula_metrics.payload_bytes;
            }
            Err(formula_diagnostics) => {
                diagnostics.extend(with_obligation_context(&obligation.id, formula_diagnostics));
            }
        }
    }

    if diagnostics.is_empty() {
        Ok(metrics)
    } else {
        Err(TrustTmirAdapterError::new(diagnostics))
    }
}

fn validate_adapter_schema(schema: &str) -> Vec<BundleDiagnostic> {
    if schema == TRUST_TMIR_ADAPTER_SCHEMA_VERSION {
        Vec::new()
    } else {
        vec![BundleDiagnostic::invalid(
            "trust_tmir.schema",
            format!(
                "unsupported Trust/tMIR adapter schema `{schema}`; expected `{TRUST_TMIR_ADAPTER_SCHEMA_VERSION}`"
            ),
        )]
    }
}

fn push_budget_diagnostic(
    diagnostics: &mut Vec<BundleDiagnostic>,
    metric: &str,
    actual: usize,
    budget: usize,
) {
    if actual > budget {
        diagnostics.push(BundleDiagnostic::unsupported(
            "trust_tmir.performance_budget",
            format!("Trust/tMIR adapter metric `{metric}` is {actual}, exceeds budget {budget}"),
        ));
    }
}

fn with_obligation_context(
    obligation_id: &str,
    diagnostics: Vec<BundleDiagnostic>,
) -> Vec<BundleDiagnostic> {
    diagnostics
        .into_iter()
        .map(|diagnostic| BundleDiagnostic {
            severity: diagnostic.severity,
            code: diagnostic.code,
            message: format!(
                "obligation `{obligation_id}` failed Trust/tMIR adapter conversion: {}",
                diagnostic.message
            ),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify_bundle::{
        replay_native_pure_evidence, replay_verify_bundle_result_evidence,
        BundleDiagnosticSeverity, BundleDigest, BundleObligationStatus, BundleProofAtom,
        BundleProofAtomRole, BundleSummaryFactKind, BundleTmirCompilerFactKind,
        BundleTmirCompilerFactRef, BundleTmirObligationCause, EvidenceArtifactKind,
        NativeTrustWpBundleVerifier, ProofEvidenceFormat, VerifyBundleEngine, VerifyBundleStatus,
    };

    fn linear_formula() -> TrustTmirFormula {
        let x_nonnegative = TrustTmirExpr::binary(
            TrustTmirBinOp::Ge,
            TrustTmirExpr::var("x"),
            TrustTmirExpr::int(0),
        );
        let x_plus_one_positive = TrustTmirExpr::binary(
            TrustTmirBinOp::Gt,
            TrustTmirExpr::binary(
                TrustTmirBinOp::Add,
                TrustTmirExpr::var("x"),
                TrustTmirExpr::int(1),
            ),
            TrustTmirExpr::int(0),
        );

        TrustTmirFormula::new(TrustTmirExpr::binary(
            TrustTmirBinOp::Implies,
            x_nonnegative,
            x_plus_one_positive,
        ))
        .with_variable("x", TrustTmirSort::Int)
    }

    fn indexed_linear_formula(index: usize) -> TrustTmirFormula {
        let variable = format!("x_{index}");
        let x_nonnegative = TrustTmirExpr::binary(
            TrustTmirBinOp::Ge,
            TrustTmirExpr::var(variable.as_str()),
            TrustTmirExpr::int(0),
        );
        let x_plus_one_positive = TrustTmirExpr::binary(
            TrustTmirBinOp::Gt,
            TrustTmirExpr::binary(
                TrustTmirBinOp::Add,
                TrustTmirExpr::var(variable.as_str()),
                TrustTmirExpr::int(1),
            ),
            TrustTmirExpr::int(0),
        );

        TrustTmirFormula::new(TrustTmirExpr::binary(
            TrustTmirBinOp::Implies,
            x_nonnegative,
            x_plus_one_positive,
        ))
        .with_variable(variable, TrustTmirSort::Int)
    }

    fn representative_performance_bundle(obligations: usize) -> TrustTmirBundle {
        let mut bundle =
            TrustTmirBundle::new("trust-tmir-performance-gate", "demo", "demo::perf_gate")
                .with_options(VerifyBundleOptions {
                    require_proof_evidence: true,
                    timeout_ms: Some(1_000),
                });

        for index in 0..obligations {
            let line = 20 + u32::try_from(index).expect("fixture index fits in u32");
            let kind = match index % 3 {
                0 => BundleObligationKind::Precondition {
                    callee: format!("demo::callee_{index}"),
                },
                1 => BundleObligationKind::Postcondition,
                _ => BundleObligationKind::LoopInvariant,
            };
            bundle = bundle.with_obligation(
                TrustTmirObligation::new(
                    format!("tmir-perf-{index}"),
                    kind,
                    indexed_linear_formula(index),
                )
                .with_location(BundleSourceSpan::new(
                    format!("src/perf_fixture_{index}.rs"),
                    line,
                    9,
                )),
            );
        }

        bundle
    }

    fn summary_digest(id: &str) -> BundleDigest {
        BundleDigest::new("sha256", format!("trust-tmir-summary-{id}"))
    }

    fn pointer_disjoint_binding_fact(id: &str, left: &str, right: &str) -> BundleSummaryFact {
        BundleSummaryFact::new(
            id,
            "tMIR",
            "dep_crate",
            "dep_crate::native_pointer_summary",
            BundleSummaryFactKind::PointerProvenanceDisjointBinding {
                left: left.to_string(),
                right: right.to_string(),
            },
            summary_digest(id),
        )
    }

    fn fat_pointer_disjoint_binding_fact(id: &str, left: &str, right: &str) -> BundleSummaryFact {
        BundleSummaryFact::new(
            id,
            "tMIR",
            "dep_crate",
            "dep_crate::native_slice_summary",
            BundleSummaryFactKind::FatPointerMetadataDisjointBinding {
                left: left.to_string(),
                right: right.to_string(),
            },
            summary_digest(id),
        )
    }

    #[test]
    fn test_trust_tmir_adapter_builds_verified_bundle_with_replay_evidence() {
        let request =
            TrustTmirBundle::new("trust-tmir-bundle-1", "demo", "demo::verified_from_tmir")
                .with_obligation(
                    TrustTmirObligation::new(
                        "tmir-post-1",
                        BundleObligationKind::Postcondition,
                        linear_formula(),
                    )
                    .with_location(BundleSourceSpan::new("src/lib.rs", 12, 9)),
                )
                .into_verify_bundle_request()
                .unwrap();

        assert_eq!(request.producer.name, TRUST_TMIR_PRODUCER_NAME);
        assert_eq!(
            request.obligations[0].claim.format,
            BundleClaimFormat::TrustFormulaV1
        );
        assert!(request.obligations[0]
            .claim
            .payload
            .contains(TRUST_FORMULA_CLAIM_SCHEMA_VERSION));

        let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

        assert_eq!(result.status, VerifyBundleStatus::Verified);
        let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status
        else {
            panic!("expected verified Trust/tMIR obligation");
        };
        assert_eq!(
            evidence.format,
            ProofEvidenceFormat::TrustWpNativePureReplayV1
        );
        assert!(evidence.is_proof_grade());
        replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
    }

    #[test]
    fn test_trust_tmir_adapter_parity_with_native_verify_bundle_boundary() {
        let location = BundleSourceSpan::new("src/lib.rs", 20, 13);
        let options = VerifyBundleOptions {
            require_proof_evidence: true,
            timeout_ms: Some(250),
        };
        let formula = linear_formula();
        let adapter_request =
            TrustTmirBundle::new("trust-tmir-parity", "demo", "demo::verified_from_tmir")
                .with_options(options)
                .with_obligation(
                    TrustTmirObligation::new(
                        "tmir-parity-post",
                        BundleObligationKind::Postcondition,
                        formula.clone(),
                    )
                    .with_location(location.clone()),
                )
                .into_verify_bundle_request()
                .unwrap();
        let expected_payload = formula.to_trust_formula_payload().unwrap();
        let expected_request = VerifyBundleRequest::new(
            "trust-tmir-parity",
            BundleProducer::new(TRUST_TMIR_PRODUCER_NAME),
            BundleTarget::new("demo"),
        )
        .with_options(options)
        .with_obligation(
            BundleObligation::new(
                "tmir-parity-post",
                BundleObligationKind::Postcondition,
                "demo::verified_from_tmir",
                BundleClaim::new(BundleClaimFormat::TrustFormulaV1, expected_payload),
            )
            .with_location(location),
        );

        assert_eq!(adapter_request, expected_request);

        let adapter_result = NativeTrustWpBundleVerifier.verify_bundle(adapter_request.clone());
        let expected_result = NativeTrustWpBundleVerifier.verify_bundle(expected_request.clone());

        assert_eq!(adapter_result.status, VerifyBundleStatus::Verified);
        assert_eq!(expected_result.status, VerifyBundleStatus::Verified);
        assert_eq!(
            adapter_result.obligation_results[0].status,
            expected_result.obligation_results[0].status
        );
        let BundleObligationStatus::Verified { evidence } =
            &adapter_result.obligation_results[0].status
        else {
            panic!("expected verified Trust/tMIR parity obligation");
        };
        let artifact_kinds = evidence
            .artifacts
            .iter()
            .map(|artifact| artifact.kind.clone())
            .collect::<Vec<_>>();
        assert_eq!(
            artifact_kinds,
            vec![
                EvidenceArtifactKind::RequestDigest,
                EvidenceArtifactKind::NormalizedObligation,
                EvidenceArtifactKind::ReplayLog,
                EvidenceArtifactKind::SolverTranscript,
            ]
        );
        replay_native_pure_evidence(&adapter_request, &adapter_request.obligations[0], evidence)
            .unwrap();
    }

    #[test]
    fn test_trust_tmir_direct_verifier_performance_gate_representative_fixture() {
        const OBLIGATIONS: usize = 12;
        let budget = TrustTmirAdapterBudget {
            max_obligations: OBLIGATIONS,
            max_bindings: 24,
            max_expr_nodes: 128,
            max_expr_depth: 8,
            max_payload_bytes: 8_192,
            max_summary_facts: 0,
            max_source_locations: OBLIGATIONS,
        };
        let bundle = representative_performance_bundle(OBLIGATIONS);

        let metrics = bundle.checked_adapter_metrics(&budget).unwrap();

        assert_eq!(metrics.obligations, OBLIGATIONS);
        assert_eq!(metrics.bindings, OBLIGATIONS);
        assert_eq!(metrics.expr_nodes, 108);
        assert_eq!(metrics.max_expr_depth, 4);
        assert_eq!(metrics.summary_facts, 0);
        assert_eq!(metrics.source_locations, OBLIGATIONS);
        assert!(metrics.payload_bytes <= budget.max_payload_bytes);

        let request = trust_tmir_to_verify_bundle_with_budget(bundle, &budget).unwrap();
        let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

        assert_eq!(result.status, VerifyBundleStatus::Verified);
        assert_eq!(result.obligation_results.len(), OBLIGATIONS);

        let mut stable_evidence_wire_bytes = 0;
        for (obligation, obligation_result) in request
            .obligations
            .iter()
            .zip(result.obligation_results.iter())
        {
            let BundleObligationStatus::Verified { evidence } = &obligation_result.status else {
                panic!("expected verified Trust/tMIR performance obligation");
            };
            assert!(evidence.is_proof_grade());
            assert_eq!(evidence.artifacts.len(), 4);
            stable_evidence_wire_bytes += evidence.to_stable_wire().len();
            replay_native_pure_evidence(&request, obligation, evidence).unwrap();
        }
        assert!(
            stable_evidence_wire_bytes <= 64_000,
            "stable evidence wire grew to {stable_evidence_wire_bytes} bytes"
        );
    }

    #[test]
    fn test_trust_tmir_direct_verifier_performance_gate_rejects_metric_budget_regression() {
        let bundle = representative_performance_bundle(4);
        let metrics = bundle.adapter_metrics().unwrap();
        let err = trust_tmir_to_verify_bundle_with_budget(
            bundle,
            &TrustTmirAdapterBudget {
                max_expr_nodes: metrics.expr_nodes - 1,
                ..TrustTmirAdapterBudget::default()
            },
        )
        .unwrap_err();

        assert!(err.diagnostics().iter().any(|diagnostic| {
            diagnostic.severity == BundleDiagnosticSeverity::Unsupported
                && diagnostic.code == "trust_tmir.performance_budget"
                && diagnostic.message.contains("expr_nodes")
        }));
    }

    #[test]
    fn test_trust_tmir_adapter_accepts_result_and_old_bindings() {
        let formula = TrustTmirFormula::new(TrustTmirExpr::binary(
            TrustTmirBinOp::And,
            TrustTmirExpr::binary(
                TrustTmirBinOp::Eq,
                TrustTmirExpr::old(TrustTmirExpr::var("x")),
                TrustTmirExpr::old(TrustTmirExpr::var("x")),
            ),
            TrustTmirExpr::binary(
                TrustTmirBinOp::Eq,
                TrustTmirExpr::result(),
                TrustTmirExpr::result(),
            ),
        ))
        .with_variable("x", TrustTmirSort::Int)
        .with_result(TrustTmirSort::Int);

        let request = TrustTmirBundle::new("trust-tmir-old", "demo", "demo::old_value")
            .with_obligation(TrustTmirObligation::new(
                "tmir-old-post",
                BundleObligationKind::Postcondition,
                formula,
            ))
            .into_verify_bundle_request()
            .unwrap();

        assert!(request.obligations[0].claim.payload.contains("\"old\""));
        assert!(request.obligations[0]
            .claim
            .payload
            .contains("\"result\":true"));
        assert!(decode_trust_formula_v1_claim(&request.obligations[0].claim.payload).is_ok());
    }

    #[test]
    fn test_trust_tmir_adapter_emits_replayable_let_binding() {
        let formula = TrustTmirFormula::new(TrustTmirExpr::let_bind(
            "ret",
            TrustTmirSort::Int,
            TrustTmirExpr::result(),
            TrustTmirExpr::binary(
                TrustTmirBinOp::Implies,
                TrustTmirExpr::binary(
                    TrustTmirBinOp::Ge,
                    TrustTmirExpr::result(),
                    TrustTmirExpr::int(0),
                ),
                TrustTmirExpr::binary(
                    TrustTmirBinOp::Ge,
                    TrustTmirExpr::var("ret"),
                    TrustTmirExpr::int(0),
                ),
            ),
        ))
        .with_result(TrustTmirSort::Int);
        let request = TrustTmirBundle::new("trust-tmir-let", "demo", "demo::let_alias")
            .with_obligation(TrustTmirObligation::new(
                "tmir-let-post",
                BundleObligationKind::Postcondition,
                formula,
            ))
            .into_verify_bundle_request()
            .unwrap();

        assert!(request.obligations[0]
            .claim
            .payload
            .contains("\"op\":\"let\""));
        let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

        assert_eq!(result.status, VerifyBundleStatus::Verified);
        let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status
        else {
            panic!("expected verified Trust/tMIR let obligation");
        };
        assert!(evidence.is_proof_grade());
        replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();
    }

    #[test]
    fn test_trust_tmir_adapter_proves_pointer_disjoint_from_typed_binding_fact() {
        let ref_t = TrustTmirSort::shared_ref(TrustTmirSort::type_param("T"));
        let formula = TrustTmirFormula::new(TrustTmirExpr::forall(
            "p",
            ref_t.clone(),
            TrustTmirExpr::forall(
                "q",
                ref_t,
                TrustTmirExpr::binary(
                    TrustTmirBinOp::Ne,
                    TrustTmirExpr::var("p"),
                    TrustTmirExpr::var("q"),
                ),
            ),
        ));
        let request =
            TrustTmirBundle::new("trust-tmir-pointer-disjoint", "demo", "demo::ptr_disjoint")
                .with_obligation(
                    TrustTmirObligation::new(
                        "tmir-pointer-disjoint-post",
                        BundleObligationKind::Postcondition,
                        formula,
                    )
                    .with_summary_fact(pointer_disjoint_binding_fact(
                        "summary-ptr-p-q",
                        "p",
                        "q",
                    )),
                )
                .into_verify_bundle_request()
                .unwrap();

        assert!(request.obligations[0]
            .claim
            .payload
            .contains("\"op\":\"forall\""));
        assert!(request.obligations[0]
            .claim
            .payload
            .contains("\"sort\":\"&T\""));

        let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

        assert_eq!(result.status, VerifyBundleStatus::Verified);
        let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status
        else {
            panic!("expected verified pointer-disjoint Trust/tMIR obligation");
        };
        assert!(evidence.is_proof_grade());
        assert!(evidence
            .artifacts
            .iter()
            .any(|artifact| artifact.kind == EvidenceArtifactKind::SummaryEvidence));
        replay_verify_bundle_result_evidence(&request, &result).unwrap();
    }

    #[test]
    fn test_trust_tmir_adapter_proves_fat_pointer_disjoint_from_typed_binding_fact() {
        let formula = TrustTmirFormula::new(TrustTmirExpr::forall(
            "p",
            TrustTmirSort::shared_slice(),
            TrustTmirExpr::forall(
                "q",
                TrustTmirSort::shared_slice(),
                TrustTmirExpr::binary(
                    TrustTmirBinOp::Ne,
                    TrustTmirExpr::var("p"),
                    TrustTmirExpr::var("q"),
                ),
            ),
        ));
        let request = TrustTmirBundle::new(
            "trust-tmir-fat-pointer-disjoint",
            "demo",
            "demo::slice_disjoint",
        )
        .with_obligation(
            TrustTmirObligation::new(
                "tmir-fat-pointer-disjoint-post",
                BundleObligationKind::Postcondition,
                formula,
            )
            .with_summary_fact(fat_pointer_disjoint_binding_fact(
                "summary-slice-p-q",
                "p",
                "q",
            )),
        )
        .into_verify_bundle_request()
        .unwrap();

        assert!(request.obligations[0]
            .claim
            .payload
            .contains("\"sort\":\"&[T]\""));
        let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

        assert_eq!(result.status, VerifyBundleStatus::Verified);
        let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status
        else {
            panic!("expected verified fat-pointer-disjoint Trust/tMIR obligation");
        };
        replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();

        let mut tampered_request = request.clone();
        tampered_request.obligations[0].summary_facts[0].digest = summary_digest("tampered");
        let err = replay_native_pure_evidence(
            &tampered_request,
            &tampered_request.obligations[0],
            evidence,
        )
        .unwrap_err();

        assert_eq!(err.code, "proof_replay.mismatch");
        assert!(err.message.contains("summary-evidence"));
    }

    #[test]
    fn test_trust_tmir_adapter_preserves_typed_provenance_for_replay() {
        let request =
            TrustTmirBundle::new("trust-tmir-provenance", "demo", "demo::with_provenance")
                .with_obligation(
                    TrustTmirObligation::new(
                        "tmir-provenance-post",
                        BundleObligationKind::Postcondition,
                        linear_formula(),
                    )
                    .with_tmir_source_span(BundleTmirSourceSpan::new(8, 42, 5))
                    .with_native_verifier(
                        BundleNativeToolIdentity::new("trust-native")
                            .with_version("tmir-schema-v2")
                            .with_revision("compiler-rev"),
                    )
                    .with_native_solver(BundleNativeToolIdentity::new("trust-wp-native-replay"))
                    .with_tmir_obligation_source(
                        BundleTmirObligationSource::new(BundleTmirObligationCause::Postcondition)
                            .with_function_id(11)
                            .with_monomorphization_id(3)
                            .with_compiler_fact_refs([
                                BundleTmirCompilerFactRef::monomorphization(3),
                                BundleTmirCompilerFactRef::cast(9),
                            ]),
                    ),
                )
                .into_verify_bundle_request()
                .unwrap();

        let metadata = &request.obligations[0].metadata;
        assert_eq!(
            metadata.tmir_source_span,
            Some(BundleTmirSourceSpan::new(8, 42, 5))
        );
        assert_eq!(
            metadata
                .native_verifier
                .as_ref()
                .map(|verifier| verifier.name.as_str()),
            Some("trust-native")
        );
        assert_eq!(metadata.native_solvers.len(), 1);
        assert!(matches!(
            metadata
                .tmir_obligation_source
                .as_ref()
                .map(|source| &source.cause),
            Some(BundleTmirObligationCause::Postcondition)
        ));

        let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

        assert_eq!(result.status, VerifyBundleStatus::Verified);
        let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status
        else {
            panic!("expected verified Trust/tMIR provenance obligation");
        };
        replay_native_pure_evidence(&request, &request.obligations[0], evidence).unwrap();

        let mut tampered_request = request.clone();
        tampered_request.obligations[0].metadata.tmir_source_span =
            Some(BundleTmirSourceSpan::new(8, 43, 5));
        let err = replay_native_pure_evidence(
            &tampered_request,
            &tampered_request.obligations[0],
            evidence,
        )
        .unwrap_err();

        assert_eq!(err.code, "proof_replay.mismatch");
        assert!(err.message.contains("normalized-obligation"));
        assert!(err.message.contains("tMIR metadata"));
    }

    #[test]
    fn test_trust_tmir_adapter_preserves_bundle_metadata_object() {
        let proof_context = BundleProofContext::new(
            vec![BundleProofAtom::new(
                0,
                BundleProofAtomRole::Assumption,
                BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "x >= 0"),
            )],
            vec![BundleProofAtom::new(
                1,
                BundleProofAtomRole::Assertion,
                BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, "x + 1 > 0"),
            )],
        );
        let expected_context_digest = proof_context.canonical_digest();
        let metadata = BundleObligationMetadata {
            native_origin: None,
            tmir_source_span: Some(BundleTmirSourceSpan::new(9, 77, 13)),
            native_verifier: Some(BundleNativeToolIdentity::new("trust-native")),
            native_replay: None,
            native_solvers: vec![BundleNativeToolIdentity::new("trust-wp-native-replay")],
            tmir_obligation_source: Some(
                BundleTmirObligationSource::new(BundleTmirObligationCause::Postcondition)
                    .with_function_id(31),
            ),
            proof_context,
        };
        let request =
            TrustTmirBundle::new("trust-tmir-full-metadata", "demo", "demo::with_metadata")
                .with_obligation(
                    TrustTmirObligation::new(
                        "tmir-full-metadata-post",
                        BundleObligationKind::Postcondition,
                        linear_formula(),
                    )
                    .with_metadata(metadata.clone()),
                )
                .into_verify_bundle_request()
                .unwrap();

        assert_eq!(request.obligations[0].metadata, metadata);
        assert_eq!(
            request.obligations[0]
                .metadata
                .proof_context
                .canonical_digest(),
            expected_context_digest
        );

        let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

        assert_eq!(result.status, VerifyBundleStatus::Verified);
        assert!(result.is_verified());
        replay_verify_bundle_result_evidence(&request, &result).unwrap();
    }

    #[test]
    fn test_trust_tmir_adapter_rejects_malformed_typed_provenance() {
        let err = TrustTmirBundle::new("trust-tmir-bad-provenance", "demo", "demo::bad_provenance")
            .with_obligation(
                TrustTmirObligation::new(
                    "tmir-bad-provenance-post",
                    BundleObligationKind::Postcondition,
                    linear_formula(),
                )
                .with_native_verifier(BundleNativeToolIdentity::new(""))
                .with_tmir_obligation_source(
                    BundleTmirObligationSource::new(
                        BundleTmirObligationCause::Other(String::new()),
                    )
                    .with_compiler_fact_refs([
                        BundleTmirCompilerFactRef::monomorphization(7),
                        BundleTmirCompilerFactRef::monomorphization(7),
                        BundleTmirCompilerFactRef::cast(9).with_digest(BundleDigest::new("", "")),
                        BundleTmirCompilerFactRef {
                            kind: BundleTmirCompilerFactKind::Other(String::new()),
                            id: 8,
                            digest: None,
                        },
                    ]),
                ),
            )
            .into_verify_bundle_request()
            .unwrap_err();

        assert!(err
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "obligation.metadata.native_verifier.name"));
        assert!(err.diagnostics().iter().any(|diagnostic| {
            diagnostic.code == "obligation.metadata.tmir_obligation_source.cause"
        }));
        assert!(err.diagnostics().iter().any(|diagnostic| {
            diagnostic.code == "obligation.metadata.tmir_obligation_source.compiler_fact_refs.kind"
        }));
        assert!(err.diagnostics().iter().any(|diagnostic| {
            diagnostic.code
                == "obligation.metadata.tmir_obligation_source.compiler_fact_refs.digest"
        }));
        assert!(err.diagnostics().iter().any(|diagnostic| {
            diagnostic.code == "obligation.metadata.tmir_obligation_source.compiler_fact_refs"
        }));
    }

    #[test]
    fn test_trust_tmir_adapter_rejects_unsupported_expr_before_verification() {
        let err = TrustTmirBundle::new("trust-tmir-unsupported", "demo", "demo::unsupported_expr")
            .with_obligation(TrustTmirObligation::new(
                "tmir-aggregate",
                BundleObligationKind::Postcondition,
                TrustTmirFormula::new(TrustTmirExpr::unsupported(
                    "aggregate pattern projection is not in the v1 adapter fragment",
                )),
            ))
            .into_verify_bundle_request()
            .unwrap_err();

        assert!(err.diagnostics().iter().any(|diagnostic| {
            diagnostic.severity == BundleDiagnosticSeverity::Unsupported
                && diagnostic.code == "trust_tmir.expr"
                && diagnostic.message.contains("tmir-aggregate")
        }));
    }

    #[test]
    fn test_trust_tmir_adapter_rejects_unsupported_sort_before_verification() {
        let err = TrustTmirBundle::new("trust-tmir-sort", "demo", "demo::unsupported_sort")
            .with_obligation(TrustTmirObligation::new(
                "tmir-seq-sort",
                BundleObligationKind::Postcondition,
                TrustTmirFormula::new(TrustTmirExpr::binary(
                    TrustTmirBinOp::Eq,
                    TrustTmirExpr::var("xs"),
                    TrustTmirExpr::var("xs"),
                ))
                .with_variable("xs", TrustTmirSort::Other("seq<int>".to_string())),
            ))
            .into_verify_bundle_request()
            .unwrap_err();

        assert!(err.diagnostics().iter().any(|diagnostic| {
            diagnostic.severity == BundleDiagnosticSeverity::Unsupported
                && diagnostic.code == "trust_tmir.sort"
        }));
    }

    #[test]
    fn test_trust_tmir_proof_call_compiler_emits_precondition_vcs() {
        let request = compile_trust_tmir_proof_call_vcs(
            TrustTmirProofCall::new(
                "trust-tmir-proof-call",
                "demo",
                "demo::caller",
                "demo::callee_lemma",
            )
            .with_location(BundleSourceSpan::new("src/lib.rs", 30, 17))
            .with_precondition(linear_formula()),
        )
        .unwrap();

        assert_eq!(request.obligations.len(), 1);
        assert_eq!(request.obligations[0].function, "demo::caller");
        assert!(matches!(
            &request.obligations[0].kind,
            BundleObligationKind::Precondition { callee }
                if callee == "demo::callee_lemma"
        ));
        assert_eq!(
            request.obligations[0].claim.format,
            BundleClaimFormat::TrustFormulaV1
        );

        let result = NativeTrustWpBundleVerifier.verify_bundle(request);
        assert_eq!(result.status, VerifyBundleStatus::Verified);
    }

    #[test]
    fn test_trust_tmir_proof_call_compiler_rejects_empty_preconditions() {
        let err = compile_trust_tmir_proof_call_vcs(TrustTmirProofCall::new(
            "trust-tmir-proof-call-empty",
            "demo",
            "demo::caller",
            "demo::callee",
        ))
        .unwrap_err();

        assert!(err
            .diagnostics()
            .iter()
            .any(|diagnostic| { diagnostic.code == "trust_tmir.proof_call.preconditions" }));
    }
}
