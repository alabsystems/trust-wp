// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Body-aware weakest preconditions over the shared, typed TrustIR.
//!
//! This API is separate from formula-only replay: its evidence commits to the
//! original module, including the original contract, and replay derives the WP
//! again. The current total fragment is an acyclic Boolean/U8/U32/U64 CFG. No instruction
//! is erased, no proof annotation is assumed, and no caller-supplied body fact
//! participates. Fresh entry-local scalar cells use definite-initialization
//! obligations and store/load substitution. Its other rules are pure assignment and return,
//! simultaneous substitution for block arguments, and conjunction of guarded
//! successor WPs for conditional branches. Local scalar calls compose the actual
//! callee's WP with the caller continuation; no summary clause is a premise.

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    sync::Arc,
};

use trust_ir::{BlockId, Constant, FuncId, FuncTy, Function, Inst, Module, Ty, ValueId};
use trust_ir_contract::body_wp_identity::{native_body_wp_bundle_id, NATIVE_BODY_WP_SCHEMA};
use trust_wp_core::{
    formula::{BinOp, ExprSort, PureExpr, UnOp},
    verify_bundle::{
        native_claim_names, native_predicate_for_obligation, replay_verify_bundle_result_evidence,
    },
};

use crate::{
    trust_ir_native::{
        body_native_requests, body_native_requests_validated, TrustIrNativeBundleError,
    },
    verify_bundle, BundleClaim, BundleClaimFormat, BundleObligationStatus, ProofEvidenceFormat,
    VerifyBundleRequest, VerifyBundleResult,
};

/// Distinguishes a re-derived body WP from historical formula-only evidence.
pub const TRUST_IR_BODY_WP_SCHEMA: &str = NATIVE_BODY_WP_SCHEMA;
const MAX_BLOCKS: usize = 256;
const MAX_FORMULA_DEPTH: usize = 256;
const MAX_NODES: usize = 1024;
const MAX_FORMULA_BYTES: usize = 262_144;

#[derive(Debug, thiserror::Error)]
pub enum TrustIrBodyContractError {
    #[error(transparent)]
    Native(#[from] TrustIrNativeBundleError),
    #[error("body-aware WP refuses request: {0}")]
    Unsupported(String),
    #[error("body-aware WP evidence replay failed: {0}")]
    Replay(String),
}

mod translation;
pub use translation::{
    replay_trust_ir_body_translation_witnesses, NativeBodyWpProofPlan,
    NativeBodyWpTranslationCoverage, NativeBodyWpTranslationWitness,
};

type Result<T> = std::result::Result<T, TrustIrBodyContractError>;

fn refuse(reason: impl Into<String>) -> TrustIrBodyContractError {
    TrustIrBodyContractError::Unsupported(reason.into())
}

/// Derive and verify postcondition WPs for typed TrustWP requests.
///
/// Successful results are trusted derivations checked by native pure replay,
/// not Clean-kernel certification. Unsupported bodies return an error before
/// proof search. Call [`replay_trust_ir_body_contracts`] on the original bundle
/// before accepting any serialized result as evidence.
pub fn verify_trust_ir_body_contracts(
    bundle: &trust_ir::NativeVerificationBundle,
) -> Result<Vec<VerifyBundleResult>> {
    verify_body_requests(trust_ir_native_bundle_to_body_verify_requests(bundle)?)
}

/// Verify using admission of this exact immutable bundle. Body semantics and
/// WP-specific checks still run; output evidence still requires replay.
pub fn verify_trust_ir_body_contracts_validated(
    admitted: &trust_ir::ValidatedNativeBundle<'_>,
) -> Result<Vec<VerifyBundleResult>> {
    verify_body_requests(trust_ir_native_bundle_to_body_verify_requests_validated(
        admitted,
    )?)
}

fn verify_body_requests(requests: Vec<VerifyBundleRequest>) -> Result<Vec<VerifyBundleResult>> {
    requests
        .into_iter()
        .map(|request| {
            let result = verify_bundle(request);
            require_native_body_evidence(&result)?;
            Ok(result)
        })
        .collect()
}

fn require_native_body_evidence(result: &VerifyBundleResult) -> Result<()> {
    for leaf in &result.obligation_results {
        if let BundleObligationStatus::Verified { evidence } = &leaf.status {
            if evidence.format != ProofEvidenceFormat::TrustWpNativePureReplayV1 {
                return Err(TrustIrBodyContractError::Replay(format!(
                    "body evidence requires native pure replay leaves, got `{}`",
                    evidence.format.as_str(),
                )));
            }
        }
    }
    Ok(())
}

/// Re-derive WPs from the original body and claims, then check all artifacts.
pub fn replay_trust_ir_body_contracts(
    bundle: &trust_ir::NativeVerificationBundle,
    results: &[VerifyBundleResult],
) -> Result<()> {
    let requests = trust_ir_native_bundle_to_body_verify_requests(bundle)?;
    replay_body_requests(&requests, results)
}

/// Independently re-derive and replay output evidence, reusing only the
/// canonical admission of the same immutable bundle. This does not reuse the
/// solver's verdict or a previous output-certificate check.
pub fn replay_trust_ir_body_contracts_validated(
    admitted: &trust_ir::ValidatedNativeBundle<'_>,
    results: &[VerifyBundleResult],
) -> Result<()> {
    let requests = trust_ir_native_bundle_to_body_verify_requests_validated(admitted)?;
    replay_body_requests(&requests, results)
}

fn replay_body_requests(
    requests: &[VerifyBundleRequest],
    results: &[VerifyBundleResult],
) -> Result<()> {
    if requests.len() != results.len() {
        return Err(TrustIrBodyContractError::Replay(
            "request/result count mismatch".into(),
        ));
    }
    for (request, result) in requests.iter().zip(results) {
        require_native_body_evidence(result)?;
        replay_verify_bundle_result_evidence(request, result)
            .map_err(|err| TrustIrBodyContractError::Replay(err.to_string()))?;
    }
    Ok(())
}

/// Validate native body contracts and derive their canonical typed WP requests.
///
/// This is the same derivation used by verification and body-aware replay.
/// Returned requests describe proof questions, not accepted proofs; consumers
/// must replay evidence against the original native bundle before accepting it.
pub fn trust_ir_native_bundle_to_body_verify_requests(
    bundle: &trust_ir::NativeVerificationBundle,
) -> Result<Vec<VerifyBundleRequest>> {
    validate_body_module(bundle)?;
    let requests = body_native_requests(bundle)?;
    derive_body_requests(bundle, requests, None)
}

/// Derive the identical typed proof questions from an admitted bundle, while
/// retaining the shared module semantic check and all WP-specific refusals.
pub fn trust_ir_native_bundle_to_body_verify_requests_validated(
    admitted: &trust_ir::ValidatedNativeBundle<'_>,
) -> Result<Vec<VerifyBundleRequest>> {
    let bundle = admitted.bundle();
    validate_body_module(bundle)?;
    let requests = body_native_requests_validated(admitted)?;
    derive_body_requests(bundle, requests, None)
}

fn validate_body_module(bundle: &trust_ir::NativeVerificationBundle) -> Result<()> {
    // Bundle provenance validation does not establish that its instructions
    // are legal TrustIR. Use the shared semantic validator before any WP rule.
    // In particular scalar Boolean negation is a Select, not UnOp::Not.
    let semantic_errors = trust_ir_build::validate_module(&bundle.module);
    if !semantic_errors.is_empty() {
        return Err(refuse(format!(
            "invalid TrustIR program: {semantic_errors:?}"
        )));
    }
    if bundle.module.proof_obligations.iter().any(|obligation| {
        obligation
            .formula
            .as_ref()
            .is_some_and(|formula| formula.payload.len() > MAX_FORMULA_BYTES)
    }) {
        return Err(refuse("contract exceeds payload budget"));
    }
    Ok(())
}

/// Capture the exact original contracts, body traversal and emitted typed
/// proof questions. These diagnostic witnesses carry no proof authority.
pub fn trust_ir_native_bundle_to_body_translation_witnesses(
    bundle: &trust_ir::NativeVerificationBundle,
) -> Result<Vec<NativeBodyWpTranslationWitness>> {
    validate_body_module(bundle)?;
    let mut witnesses = Vec::new();
    derive_body_requests(bundle, body_native_requests(bundle)?, Some(&mut witnesses))?;
    Ok(witnesses)
}

fn derive_body_requests(
    bundle: &trust_ir::NativeVerificationBundle,
    mut requests: Vec<VerifyBundleRequest>,
    mut witnesses: Option<&mut Vec<NativeBodyWpTranslationWitness>>,
) -> Result<Vec<VerifyBundleRequest>> {
    // Bind the complete admitted input, including source and input artifact
    // identities. The canonical owner supplies the framed SHA-256 digest;
    // this is request identity, not fresh-source or artifact proof authority.
    // Output evidence stays separate and must never be appended to this input
    // before replay, which would change the question being checked.
    let input_identity = bundle.stable_digest();
    let native = bundle.requests.iter().filter_map(|request| match request {
        trust_ir::NativeVerificationRequest::TrustWp(request) => Some(request),
        _ => None,
    });
    for (request, native) in requests.iter_mut().zip(native) {
        if native.mode != trust_ir::TrustWpVerificationMode::WeakestPrecondition {
            return Err(refuse("only WeakestPrecondition mode has body semantics"));
        }
        if !native.provenance.replay_context().atoms.is_empty() {
            return Err(refuse(
                "external replay assumptions/assertions are not body semantics",
            ));
        }
        let function = bundle
            .module
            .function_by_id(native.function)
            .ok_or_else(|| refuse("missing function"))?;
        let mut body = ScalarBody::validate(&bundle.module, function, String::new())?;
        body.capture_plan = witnesses.is_some();
        request.bundle_id = native_body_wp_bundle_id(
            &bundle.module.name,
            native.id.index(),
            &input_identity.bytes,
        );
        let mut plan = None;
        for (output, id) in request.obligations.iter_mut().zip(&native.obligations) {
            plan = derive_body_obligation(&body, native, output, *id)?;
        }
        if let Some(witnesses) = witnesses.as_deref_mut() {
            witnesses.push(NativeBodyWpTranslationWitness::new(
                bundle,
                native,
                function,
                request.clone(),
                body.entry
                    .params
                    .iter()
                    .map(|(id, _)| (*id, body.value_name(*id)))
                    .collect(),
                plan.ok_or_else(|| refuse("translation has no original postcondition"))?,
            )?);
        }
    }
    Ok(requests)
}

fn derive_body_obligation(
    body: &ScalarBody<'_>,
    native: &trust_ir::TrustWpNativeRequest,
    output: &mut crate::BundleObligation,
    id: trust_ir::ProofId,
) -> Result<Option<NativeBodyWpProofPlan>> {
    let original = body
        .module
        .proof_obligations
        .iter()
        .find(|obligation| obligation.id == id)
        .ok_or_else(|| refuse("missing original obligation"))?;
    if original.kind != trust_ir::ObligationKind::Postcondition
        || original.function != Some(native.function)
    {
        return Err(refuse(
            "only function-owned postconditions have body-WP semantics",
        ));
    }
    if !output.metadata.proof_context.assumptions.is_empty()
        || !output.metadata.proof_context.assertions.is_empty()
        || !output.summary_facts.is_empty()
    {
        return Err(refuse(
            "assumptions and summary facts are outside the scalar body fragment",
        ));
    }
    let formula = original
        .formula
        .as_ref()
        .ok_or_else(|| refuse("missing contract"))?;
    let postcondition = bound_postcondition(body, formula, output)?;
    let wp = body.wp(
        body.entry.id,
        &postcondition,
        &mut BTreeSet::new(),
        &mut 4096,
        &mut BTreeSet::from([native.function]),
    )?;
    if !wp.required_cells.is_empty() {
        return Err(refuse("load may read an uninitialized local scalar cell"));
    }
    let parameters: BTreeSet<_> = body
        .entry
        .params
        .iter()
        .map(|(id, _)| body.value_name(*id))
        .collect();
    if wp
        .predicate
        .free_vars()
        .iter()
        .any(|name| !parameters.contains(name))
    {
        return Err(refuse("derived WP retains an unbound local value"));
    }
    let plan = wp.plan;
    let payload = wp.predicate.to_string();
    if payload.len() > MAX_FORMULA_BYTES {
        return Err(refuse("derived WP exceeds the formula budget"));
    }
    output.claim = scalar_claim(&if body
        .entry
        .params
        .iter()
        .any(|(_, ty)| matches!(ty, Ty::U8 | Ty::U32 | Ty::U64))
    {
        binary(body.input_domain(), BinOp::Implies, wp.predicate)
    } else {
        wp.predicate
    })?;
    Ok(plan)
}

fn bound_postcondition(
    body: &ScalarBody<'_>,
    formula: &trust_ir::ProofFormula,
    output: &crate::BundleObligation,
) -> Result<PureExpr> {
    let names =
        native_claim_names(&output.claim).ok_or_else(|| refuse("unreadable claim names"))?;
    let mut substitutions = HashMap::new();
    for (name, binding) in &formula.bindings {
        let sort = match binding.sort {
            trust_ir::proof::ClauseSort::Bool => ScalarSort::Boolean,
            trust_ir::proof::ClauseSort::BitVec(8) => ScalarSort::Unsigned8,
            trust_ir::proof::ClauseSort::BitVec(32) => ScalarSort::Unsigned32,
            trust_ir::proof::ClauseSort::BitVec(64) => ScalarSort::Unsigned64,
            _ => return Err(refuse("contract binding is outside the scalar fragment")),
        };
        let value = match binding.place {
            trust_ir::proof::ClausePlace::Param { index } => body
                .entry
                .params
                .get(index as usize)
                .filter(|(_, ty)| ScalarSort::from_ty(ty) == Some(sort))
                .map(|(id, _)| body.value(*id))
                .ok_or_else(|| refuse("missing parameter binding"))?,
            trust_ir::proof::ClausePlace::ResultSlot { index: 0 } if sort == body.result_sort => {
                result_expr(sort, &body.namespace)
            }
            _ => return Err(refuse("contract place is outside Param/ResultSlot(0)")),
        };
        substitutions.insert(name.clone(), value);
    }
    if names.len() != substitutions.len()
        || names
            .iter()
            .any(|name| !substitutions.contains_key(&name.name))
    {
        return Err(refuse(
            "contract free names must have exact, complete place bindings",
        ));
    }
    let predicate = native_predicate_for_obligation(output)
        .map_err(|err| refuse(format!("contract decode: {err:?}")))?
        .predicate;
    let postcondition = predicate.substitute(&substitutions);
    if scalar_formula_sort(&postcondition, 0)? != ExprSort::Bool {
        return Err(refuse("postcondition must be Boolean"));
    }
    Ok(postcondition)
}

fn value_expr(id: ValueId, sort: ScalarSort, namespace: &str) -> PureExpr {
    PureExpr::Var(
        format!("__trust_wp_body_{namespace}v{}", id.index()),
        Some(sort.expr_sort()),
    )
}

fn result_expr(sort: ScalarSort, namespace: &str) -> PureExpr {
    PureExpr::Var(
        format!("__trust_wp_body_{namespace}result"),
        Some(sort.expr_sort()),
    )
}

fn binary(left: PureExpr, op: BinOp, right: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(left), op, Arc::new(right))
}

/// Preserve Boolean sorts across the existing structured proof-claim boundary.
/// PureExpr's Display intentionally omits variable sorts and is not a codec.
pub fn boolean_claim(predicate: &PureExpr) -> Result<BundleClaim> {
    check_boolean_formula(predicate, 0)?;
    scalar_claim(predicate)
}

/// Encode a typed scalar expression through the native body's shared claim
/// serializer. Question admission and evidence replay retain their own checks.
pub fn scalar_claim(predicate: &PureExpr) -> Result<BundleClaim> {
    fn encode(expr: &PureExpr) -> Result<serde_json::Value> {
        use serde_json::json;
        Ok(match expr {
            PureExpr::Bool(value) => json!({"bool":value}),
            PureExpr::Int(value) => json!({"int":value}),
            PureExpr::Var(name, Some(ExprSort::Bool | ExprSort::Int)) => json!({"var":name}),
            PureExpr::UnOp(UnOp::Not, inner) => json!({"op":"not", "expr":encode(inner)?}),
            PureExpr::BinOp(left, op, right) => {
                let op = match op {
                    BinOp::And => "and",
                    BinOp::Or => "or",
                    BinOp::Implies => "implies",
                    BinOp::Eq => "eq",
                    BinOp::Ne => "ne",
                    BinOp::Lt => "lt",
                    BinOp::Le => "le",
                    BinOp::Gt => "gt",
                    BinOp::Ge => "ge",
                    BinOp::Add if expr.free_vars().is_empty() => "add",
                    BinOp::Sub if expr.free_vars().is_empty() => "sub",
                    BinOp::Mul if expr.free_vars().is_empty() => "mul",
                    _ => return Err(refuse("operator outside scalar claim fragment")),
                };
                json!({"op":op,"lhs":encode(left)?,"rhs":encode(right)?})
            }
            PureExpr::Ite(condition, left, right) => {
                if scalar_formula_sort(expr, 0)? != ExprSort::Bool {
                    return Err(refuse("only Boolean selection has a claim codec"));
                }
                let condition = encode(condition)?;
                json!({"op":"or","lhs":{"op":"and","lhs":condition,"rhs":encode(left)?},"rhs":{"op":"and","lhs":{"op":"not","expr":condition},"rhs":encode(right)?}})
            }
            _ => return Err(refuse("untyped or unsupported scalar claim")),
        })
    }
    fn names(expr: &PureExpr, out: &mut BTreeMap<String, ExprSort>) -> Result<()> {
        match expr {
            PureExpr::Var(name, Some(sort @ (ExprSort::Bool | ExprSort::Int))) => {
                if out
                    .insert(name.clone(), sort.clone())
                    .is_some_and(|old| old != *sort)
                {
                    return Err(refuse("conflicting variable sorts"));
                }
            }
            PureExpr::UnOp(_, inner) => names(inner, out)?,
            PureExpr::BinOp(left, _, right) => {
                names(left, out)?;
                names(right, out)?;
            }
            PureExpr::Ite(c, l, r) => {
                names(c, out)?;
                names(l, out)?;
                names(r, out)?;
            }
            PureExpr::Bool(_) | PureExpr::Int(_) => {}
            _ => return Err(refuse("untyped or unsupported claim name")),
        }
        Ok(())
    }
    if scalar_formula_sort(predicate, 0)? != ExprSort::Bool {
        return Err(refuse("claim must be Boolean"));
    }
    let mut variables = BTreeMap::new();
    names(predicate, &mut variables)?;
    let variables: Vec<_> = variables.into_iter().map(|(name, sort)| {
        serde_json::json!({"name":name,"sort":if sort == ExprSort::Bool {"bool"} else {"int"}})
    }).collect();
    let payload = serde_json::json!({"schema":crate::TRUST_FORMULA_CLAIM_SCHEMA_VERSION,"variables":variables,"body":encode(predicate)?}).to_string();
    if payload.len() > MAX_FORMULA_BYTES {
        return Err(refuse("typed claim exceeds payload budget"));
    }
    Ok(BundleClaim::new(BundleClaimFormat::TrustFormulaV1, payload))
}

/// Decode the canonical cross-repo Formula type, never a guessed JSON AST.
/// This typed conversion deliberately owns only its Boolean fragment.
pub(crate) fn decode_shared_boolean_formula(payload: &str) -> Result<PureExpr> {
    if payload.len() > MAX_FORMULA_BYTES {
        return Err(refuse("contract exceeds payload budget"));
    }
    let formula: trust_ir_contract::Formula = serde_json::from_str(payload)
        .map_err(|error| refuse(format!("shared Formula decode: {error}")))?;
    shared_boolean_formula(&formula, 0)
}

fn shared_boolean_formula(formula: &trust_ir_contract::Formula, depth: usize) -> Result<PureExpr> {
    use trust_ir_contract::{Formula, Sort};
    if depth > MAX_FORMULA_DEPTH {
        return Err(refuse("shared Formula exceeds depth budget"));
    }
    let recurse = |formula| shared_boolean_formula(formula, depth + 1);
    Ok(match formula {
        Formula::Bool(value) => PureExpr::Bool(*value),
        Formula::Var(name, Sort::Bool) => PureExpr::Var(name.clone(), Some(ExprSort::Bool)),
        Formula::SymVar(name, Sort::Bool) => {
            PureExpr::Var(name.as_str().into(), Some(ExprSort::Bool))
        }
        Formula::Not(inner) => PureExpr::UnOp(UnOp::Not, Arc::new(recurse(inner)?)),
        Formula::And(values) | Formula::Or(values) => {
            if values.len() > 64 {
                return Err(refuse("Boolean connective exceeds arity budget"));
            }
            let (identity, operation) = if matches!(formula, Formula::And(_)) {
                (true, BinOp::And)
            } else {
                (false, BinOp::Or)
            };
            let mut result = PureExpr::Bool(identity);
            for value in values {
                result = binary(result, operation, recurse(value)?);
            }
            result
        }
        Formula::Implies(left, right) => binary(recurse(left)?, BinOp::Implies, recurse(right)?),
        Formula::Eq(left, right) => binary(recurse(left)?, BinOp::Eq, recurse(right)?),
        Formula::Ite(condition, left, right) => PureExpr::Ite(
            Arc::new(recurse(condition)?),
            Arc::new(recurse(left)?),
            Arc::new(recurse(right)?),
        ),
        _ => {
            return Err(refuse(
                "shared Formula node or sort is outside the Boolean fragment",
            ));
        }
    })
}

fn check_boolean_formula(expr: &PureExpr, depth: usize) -> Result<()> {
    if depth > MAX_FORMULA_DEPTH {
        return Err(refuse("contract expression exceeds depth budget"));
    }
    match expr {
        PureExpr::Bool(_) | PureExpr::Var(_, None | Some(ExprSort::Bool)) => Ok(()),
        PureExpr::UnOp(UnOp::Not, inner) => check_boolean_formula(inner, depth + 1),
        PureExpr::BinOp(
            left,
            BinOp::And | BinOp::Or | BinOp::Implies | BinOp::Eq | BinOp::Ne,
            right,
        ) => {
            check_boolean_formula(left, depth + 1)?;
            check_boolean_formula(right, depth + 1)
        }
        PureExpr::Ite(condition, left, right) => {
            check_boolean_formula(condition, depth + 1)?;
            check_boolean_formula(left, depth + 1)?;
            check_boolean_formula(right, depth + 1)
        }
        _ => Err(refuse(
            "contract expression is outside the Boolean fragment",
        )),
    }
}

fn scalar_formula_sort(expr: &PureExpr, depth: usize) -> Result<ExprSort> {
    if depth > MAX_FORMULA_DEPTH {
        return Err(refuse("contract expression exceeds depth budget"));
    }
    let sort = |value| scalar_formula_sort(value, depth + 1);
    Ok(match expr {
        PureExpr::Bool(_) => ExprSort::Bool,
        PureExpr::Int(_) => ExprSort::Int,
        PureExpr::Var(_, Some(value @ (ExprSort::Bool | ExprSort::Int))) => value.clone(),
        PureExpr::UnOp(UnOp::Not, inner) if sort(inner)? == ExprSort::Bool => ExprSort::Bool,
        PureExpr::BinOp(left, op, right) => {
            let l = sort(left)?;
            let r = sort(right)?;
            match op {
                BinOp::And | BinOp::Or | BinOp::Implies if l == ExprSort::Bool && r == l => {
                    ExprSort::Bool
                }
                BinOp::Add | BinOp::Sub | BinOp::Mul
                    if l == ExprSort::Int && r == l && expr.free_vars().is_empty() =>
                {
                    ExprSort::Int
                }
                BinOp::Eq | BinOp::Ne if l == r => ExprSort::Bool,
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge if l == ExprSort::Int && r == l => {
                    ExprSort::Bool
                }
                _ => return Err(refuse("ill-sorted or unsupported scalar operator")),
            }
        }
        PureExpr::Ite(c, l, r)
            if sort(c)? == ExprSort::Bool
                && sort(l)? == ExprSort::Bool
                && sort(r)? == ExprSort::Bool =>
        {
            ExprSort::Bool
        }
        _ => return Err(refuse("untyped or unsupported scalar expression")),
    })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ScalarSort {
    Boolean,
    Unsigned8,
    Unsigned32,
    Unsigned64,
}

impl ScalarSort {
    fn from_ty(ty: &Ty) -> Option<Self> {
        match ty {
            Ty::Bool => Some(Self::Boolean),
            Ty::U8 => Some(Self::Unsigned8),
            Ty::U32 => Some(Self::Unsigned32),
            Ty::U64 => Some(Self::Unsigned64),
            _ => None,
        }
    }
    fn expr_sort(self) -> ExprSort {
        match self {
            Self::Boolean => ExprSort::Bool,
            Self::Unsigned8 | Self::Unsigned32 | Self::Unsigned64 => ExprSort::Int,
        }
    }

    fn unsigned_bits(self) -> Option<u32> {
        match self {
            Self::Boolean => None,
            Self::Unsigned8 => Some(8),
            Self::Unsigned32 => Some(32),
            Self::Unsigned64 => Some(64),
        }
    }

    fn unsigned_max(self) -> Option<PureExpr> {
        self.unsigned_bits()
            .map(trust_wp_core::formula::int_bounds::unsigned_max_expr)
    }
}

struct ScalarBody<'a> {
    // Diagnostic collection is fixed for this derivation; callee bodies keep
    // the default off because their translation remains explicitly unproved.
    capture_plan: bool,
    module: &'a Module,
    namespace: String,
    entry: &'a trust_ir::Block,
    blocks: BTreeMap<BlockId, &'a trust_ir::Block>,
    definitions: BTreeMap<ValueId, ValueKind>,
    result_sort: ScalarSort,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ValueKind {
    Scalar(ScalarSort),
    Cell(ScalarSort),
}

struct BodyWp {
    predicate: PureExpr,
    plan: Option<NativeBodyWpProofPlan>,
    // A dead load still requires initialized bytes.
    required_cells: BTreeSet<ValueId>,
}

fn cell_expr(id: ValueId, sort: ScalarSort, namespace: &str) -> PureExpr {
    PureExpr::Var(
        format!("__trust_wp_{namespace}cell{}", id.index()),
        Some(sort.expr_sort()),
    )
}

type ScalarOperand = (ValueId, Option<ValueKind>);
type InstructionTypes = (Vec<ScalarOperand>, Option<ValueKind>, bool);

fn instruction_types(
    module: &Module,
    inst: &Inst,
    result_sort: ScalarSort,
    has_unsigned: bool,
) -> Result<InstructionTypes> {
    let scalar = |ty| ScalarSort::from_ty(ty).ok_or_else(|| refuse("unsupported scalar type"));
    let (uses, result, terminator) = match inst {
        Inst::Call { callee, args } => {
            let function = module
                .function_by_id(*callee)
                .ok_or_else(|| refuse("missing local callee"))?;
            let signature = scalar_signature(module, function)?;
            if signature.params.len() != args.len() {
                return Err(refuse("scalar call argument arity mismatch"));
            }
            (
                args.iter()
                    .zip(&signature.params)
                    .map(|(id, ty)| Ok((*id, Some(ValueKind::Scalar(scalar(ty)?)))))
                    .collect::<Result<Vec<_>>>()?,
                Some(ValueKind::Scalar(scalar(&signature.returns[0])?)),
                false,
            )
        }
        Inst::Alloca { .. } | Inst::Load { .. } | Inst::Store { .. } => local_cell_types(inst)?,
        Inst::Assume { cond } if has_unsigned => (
            vec![(*cond, Some(ValueKind::Scalar(ScalarSort::Boolean)))],
            None,
            false,
        ),
        Inst::Br { args, .. } => (args.iter().map(|id| (*id, None)).collect(), None, true),
        Inst::Return { values } if values.len() == 1 => (
            vec![(values[0], Some(ValueKind::Scalar(result_sort)))],
            None,
            true,
        ),
        Inst::CondBr {
            cond,
            then_args,
            else_args,
            ..
        } => {
            let mut uses = vec![(*cond, Some(ValueKind::Scalar(ScalarSort::Boolean)))];
            uses.extend(then_args.iter().chain(else_args).map(|id| (*id, None)));
            (uses, None, true)
        }
        Inst::Const { ty, .. } => {
            instruction_expression(inst, "")?;
            (vec![], Some(ValueKind::Scalar(scalar(ty)?)), false)
        }
        Inst::Copy { ty, operand } => {
            instruction_expression(inst, "")?;
            let kind = ValueKind::Scalar(scalar(ty)?);
            (vec![(*operand, Some(kind))], Some(kind), false)
        }
        Inst::ICmp { ty, lhs, rhs, .. } => {
            instruction_expression(inst, "")?;
            let kind = ValueKind::Scalar(scalar(ty)?);
            (
                vec![(*lhs, Some(kind)), (*rhs, Some(kind))],
                Some(ValueKind::Scalar(ScalarSort::Boolean)),
                false,
            )
        }
        Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => {
            let kind = ValueKind::Scalar(scalar(ty)?);
            (
                vec![
                    (*cond, Some(ValueKind::Scalar(ScalarSort::Boolean))),
                    (*then_val, Some(kind)),
                    (*else_val, Some(kind)),
                ],
                Some(kind),
                false,
            )
        }
        _ => {
            return Err(refuse(format!(
                "instruction outside scalar WP fragment: {inst:?}"
            )));
        }
    };
    Ok((uses, result, terminator))
}

fn local_cell_types(inst: &Inst) -> Result<InstructionTypes> {
    let scalar = |ty| ScalarSort::from_ty(ty).ok_or_else(|| refuse("unsupported scalar type"));
    Ok(match inst {
        Inst::Alloca {
            ty,
            count: None,
            align: None,
        } => (vec![], Some(ValueKind::Cell(scalar(ty)?)), false),
        Inst::Load {
            ty,
            ptr,
            volatile: false,
            align: None,
        } => {
            let sort = scalar(ty)?;
            (
                vec![(*ptr, Some(ValueKind::Cell(sort)))],
                Some(ValueKind::Scalar(sort)),
                false,
            )
        }
        Inst::Store {
            ty,
            ptr,
            value,
            volatile: false,
            align: None,
        } => {
            let sort = scalar(ty)?;
            (
                vec![
                    (*ptr, Some(ValueKind::Cell(sort))),
                    (*value, Some(ValueKind::Scalar(sort))),
                ],
                None,
                false,
            )
        }
        _ => return Err(refuse("unsupported local scalar cell instruction")),
    })
}

fn scalar_signature<'a>(module: &'a Module, function: &Function) -> Result<&'a FuncTy> {
    let signature = module
        .func_types
        .get(function.ty.index() as usize)
        .ok_or_else(|| refuse("missing function signature"))?;
    if signature.abi.is_some()
        || signature.is_vararg
        || signature
            .params
            .iter()
            .any(|ty| ScalarSort::from_ty(ty).is_none())
        || signature.returns.len() != 1
        || ScalarSort::from_ty(&signature.returns[0]).is_none()
    {
        return Err(refuse(
            "requires unplaced Boolean/U8/U32/U64 parameters and one scalar result",
        ));
    }
    Ok(signature)
}

fn validate_body_annotations(function: &Function, params: &[Ty]) -> Result<()> {
    // Pure is a producer claim, not an operational premise. The complete
    // instruction/CFG validation below independently excludes escaping
    // memory effects and every instruction outside this fragment. A local
    // call separately derives the actual callee body, including its checks.
    // Keep its original bytes in the bundle identity; never erase it or
    // infer any property from it. All other annotations remain refused.
    let annotation_only = function.proofs.is_empty()
        || function.proofs.as_slice() == [trust_ir::ProofAnnotation::Pure];
    // D-284: an unproved postcondition is a conclusion still owed, never
    // a premise. Preserve its bytes in the input identity and derive the
    // requested goal only from instructions. Preconditions, termination,
    // effects and claimed summary authority remain outside this fragment.
    let conclusion_only = function.summary.as_ref().is_none_or(|summary| {
        let trust_ir::FunctionSummary {
            requires,
            ensures,
            params: summary_params,
            proved,
            decreases,
            backed_by,
            effects,
        } = summary;
        !*proved
            && backed_by.is_none()
            && requires.is_empty()
            && decreases.is_empty()
            && effects.is_none()
            && ensures.len() <= MAX_NODES
            && ensures
                .iter()
                .all(|formula| formula.payload.len() <= MAX_FORMULA_BYTES)
            && summary_params.len() == params.len()
            && summary_params.iter().all(|name| !name.is_empty())
            && summary_params.iter().collect::<BTreeSet<_>>().len() == summary_params.len()
    });
    if !annotation_only
        || !function.attrs.is_empty()
        || !conclusion_only
        || function.blocks.is_empty()
        || function.blocks.len() > MAX_BLOCKS
        || function
            .blocks
            .iter()
            .map(|block| block.body.len())
            .sum::<usize>()
            > MAX_NODES
    {
        return Err(refuse(
            "body is absent, carries assumptions, or exceeds resource limits",
        ));
    }
    Ok(())
}

fn validate_reachable_blocks(
    function: &Function,
    blocks: &BTreeMap<BlockId, &trust_ir::Block>,
) -> Result<()> {
    let mut reachable = BTreeSet::new();
    let mut pending = vec![function.entry];
    while let Some(id) = pending.pop() {
        if !reachable.insert(id) {
            continue;
        }
        let block = blocks
            .get(&id)
            .ok_or_else(|| refuse("missing branch target"))?;
        match &block.body.last().ok_or_else(|| refuse("empty block"))?.inst {
            Inst::Br { target, .. } => pending.push(*target),
            Inst::CondBr {
                then_target,
                else_target,
                ..
            } => {
                pending.push(*then_target);
                pending.push(*else_target);
            }
            _ => {}
        }
    }
    if reachable.len() != blocks.len() {
        return Err(refuse(
            "unreachable blocks are outside the scalar body fragment",
        ));
    }
    Ok(())
}

fn validate_scalar_layout(module: &Module, has_cells: bool) -> Result<()> {
    if has_cells && (!module.globals.is_empty() || !module.imports.is_empty()) {
        return Err(refuse(
            "global or imported memory state is outside the local-cell fragment",
        ));
    }
    if !module.target_has_canonical_scalar_layout()
        || !matches!(module.pointer_bits(), 32 | 64)
        || module
            .target_info
            .as_ref()
            .is_some_and(|target| target.endianness != trust_ir::Endianness::Little)
        || (has_cells && module.pointer_bits() != 64)
    {
        return Err(refuse(
            "body target is outside the checked scalar memory layout",
        ));
    }
    Ok(())
}

impl<'a> ScalarBody<'a> {
    fn validate(module: &'a Module, function: &'a Function, namespace: String) -> Result<Self> {
        let signature = scalar_signature(module, function)?;
        let params = &signature.params;
        let result = &signature.returns[0];
        validate_body_annotations(function, params)?;
        let result_sort =
            ScalarSort::from_ty(result).ok_or_else(|| refuse("unsupported result type"))?;
        let has_unsigned = params
            .iter()
            .any(|ty| matches!(ty, Ty::U8 | Ty::U32 | Ty::U64))
            || matches!(result, Ty::U8 | Ty::U32 | Ty::U64);
        let mut blocks = BTreeMap::new();
        let mut definitions = BTreeMap::new();
        let mut has_cells = false;
        for block in &function.blocks {
            if blocks.insert(block.id, block).is_some() {
                return Err(refuse("duplicate block"));
            }
            for (id, ty) in &block.params {
                let sort =
                    ScalarSort::from_ty(ty).ok_or_else(|| refuse("unsupported block parameter"))?;
                if definitions.insert(*id, ValueKind::Scalar(sort)).is_some() {
                    return Err(refuse(
                        "block parameter is unsupported or has duplicate SSA identity",
                    ));
                }
            }
            for (index, node) in block.body.iter().enumerate() {
                if !node.proofs.is_empty() || node.proof_context.is_some() {
                    return Err(refuse("instruction proof annotations are not premises"));
                }
                let (_, result, terminator) =
                    instruction_types(module, &node.inst, result_sort, has_unsigned)?;
                if matches!(result, Some(ValueKind::Cell(_))) {
                    if block.id != function.entry {
                        return Err(refuse("Scalar cells must be allocated in the entry block"));
                    }
                    has_cells = true;
                }
                if let Some(kind) = result {
                    if node.results.len() != 1
                        || definitions.insert(node.results[0], kind).is_some()
                    {
                        return Err(refuse(
                            "value-producing instruction needs one unique SSA result",
                        ));
                    }
                } else if !node.results.is_empty() || (terminator && index + 1 != block.body.len())
                {
                    return Err(refuse(
                        "terminator must end the block and yield no SSA result",
                    ));
                }
            }
            if !matches!(
                block.body.last().map(|node| &node.inst),
                Some(Inst::Br { .. } | Inst::CondBr { .. } | Inst::Return { .. })
            ) {
                return Err(refuse("block has no supported terminator"));
            }
        }
        let entry = blocks
            .get(&function.entry)
            .copied()
            .ok_or_else(|| refuse("missing entry block"))?;
        if entry.params.iter().map(|(_, ty)| ty).ne(params.iter()) {
            return Err(refuse("entry parameters do not match signature"));
        }
        // The shared semantic validator has already checked SSA ordering and
        // dominance. Reuse that answer for cross-block values; check the exact
        // scalar/cell roles here, including every branch argument and return.
        for block in blocks.values() {
            for node in &block.body {
                for (id, kind) in
                    instruction_types(module, &node.inst, result_sort, has_unsigned)?.0
                {
                    if !matches!(definitions.get(&id), Some(actual) if kind.map_or(matches!(actual, ValueKind::Scalar(_)), |kind| *actual == kind))
                    {
                        return Err(refuse(
                            "operand is undefined or has the wrong scalar/cell type",
                        ));
                    }
                }
            }
        }
        validate_reachable_blocks(function, &blocks)?;
        validate_scalar_layout(module, has_cells)?;
        Ok(Self {
            capture_plan: false,
            module,
            namespace,
            entry,
            blocks,
            definitions,
            result_sort,
        })
    }

    fn value(&self, id: ValueId) -> PureExpr {
        match self.definitions[&id] {
            ValueKind::Scalar(sort) => value_expr(id, sort, &self.namespace),
            ValueKind::Cell(_) => unreachable!("validated scalar use"),
        }
    }

    fn value_name(&self, id: ValueId) -> String {
        format!("__trust_wp_body_{}v{}", self.namespace, id.index())
    }

    fn input_domain(&self) -> PureExpr {
        self.entry
            .params
            .iter()
            .filter_map(|(id, ty)| Some((*id, ScalarSort::from_ty(ty)?.unsigned_max()?)))
            .fold(PureExpr::Bool(true), |domain, (id, maximum)| {
                binary(
                    domain,
                    BinOp::And,
                    binary(
                        binary(PureExpr::Int(0), BinOp::Le, self.value(id)),
                        BinOp::And,
                        binary(self.value(id), BinOp::Le, maximum),
                    ),
                )
            })
    }

    fn edge(
        &self,
        target: BlockId,
        args: &[ValueId],
        post: &PureExpr,
        active: &mut BTreeSet<BlockId>,
        remaining: &mut usize,
        active_calls: &mut BTreeSet<FuncId>,
    ) -> Result<BodyWp> {
        let block = self
            .blocks
            .get(&target)
            .ok_or_else(|| refuse("missing branch target"))?;
        if block.params.len() != args.len() {
            return Err(refuse("branch argument arity mismatch"));
        }
        let substitutions = block
            .params
            .iter()
            .zip(args)
            .map(|((id, _), argument)| (self.value_name(*id), self.value(*argument)))
            .collect();
        let mut wp = self.wp(target, post, active, remaining, active_calls)?;
        wp.predicate = wp.predicate.substitute(&substitutions);
        Ok(wp)
    }

    fn wp(
        &self,
        id: BlockId,
        post: &PureExpr,
        active: &mut BTreeSet<BlockId>,
        remaining: &mut usize,
        active_calls: &mut BTreeSet<FuncId>,
    ) -> Result<BodyWp> {
        *remaining = remaining
            .checked_sub(1)
            .ok_or_else(|| refuse("CFG expansion exceeds work budget"))?;
        if !active.insert(id) {
            return Err(refuse(
                "loops require inductive invariants outside this fragment",
            ));
        }
        let block = self
            .blocks
            .get(&id)
            .ok_or_else(|| refuse("missing block"))?;
        let mut nodes = block.body.iter().enumerate().rev();
        let (position, node) = nodes.next().ok_or_else(|| refuse("empty block"))?;
        let plan = |successors: Vec<Option<NativeBodyWpProofPlan>>| {
            self.capture_plan.then(|| NativeBodyWpProofPlan {
                block: id,
                position,
                instruction: node.clone(),
                successors: successors.into_iter().flatten().collect(),
            })
        };
        let mut wp = match &node.inst {
            Inst::Return { values } if values.len() == 1 => BodyWp {
                predicate: post.substitute(&HashMap::from([(
                    format!("__trust_wp_body_{}result", self.namespace),
                    self.value(values[0]),
                )])),
                required_cells: BTreeSet::new(),
                plan: plan(Vec::new()),
            },
            Inst::Br { target, args } => {
                let mut child = self.edge(*target, args, post, active, remaining, active_calls)?;
                child.plan = plan(vec![child.plan]);
                child
            }
            Inst::CondBr {
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            } => {
                let then_wp = self.edge(
                    *then_target,
                    then_args,
                    post,
                    active,
                    remaining,
                    active_calls,
                )?;
                let else_wp = self.edge(
                    *else_target,
                    else_args,
                    post,
                    active,
                    remaining,
                    active_calls,
                )?;
                let mut required_cells = then_wp.required_cells;
                required_cells.extend(else_wp.required_cells);
                BodyWp {
                    predicate: binary(
                        binary(self.value(*cond), BinOp::Implies, then_wp.predicate),
                        BinOp::And,
                        binary(
                            PureExpr::UnOp(UnOp::Not, Arc::new(self.value(*cond))),
                            BinOp::Implies,
                            else_wp.predicate,
                        ),
                    ),
                    required_cells,
                    plan: plan(vec![then_wp.plan, else_wp.plan]),
                }
            }
            _ => return Err(refuse("requires one scalar return value")),
        };
        for (position, node) in nodes {
            if let Some(child) = wp.plan {
                wp.plan = Some(NativeBodyWpProofPlan {
                    block: id,
                    position,
                    instruction: node.clone(),
                    successors: vec![child],
                });
            }
            // Fresh allocation, initialized load, store and disjoint-cell
            // substitution. Pointers are never symbolic values:
            // validation admits only direct, nonescaping allocation identities.
            wp = self.step_wp(node, wp, remaining, active_calls)?;
            if wp.predicate.to_string().len() > MAX_FORMULA_BYTES {
                return Err(refuse("derived WP exceeds the formula budget"));
            }
        }
        if wp.predicate.to_string().len() > MAX_FORMULA_BYTES {
            return Err(refuse("derived WP exceeds the formula budget"));
        }
        active.remove(&id);
        Ok(wp)
    }

    fn step_wp(
        &self,
        node: &trust_ir::InstrNode,
        mut wp: BodyWp,
        remaining: &mut usize,
        active_calls: &mut BTreeSet<FuncId>,
    ) -> Result<BodyWp> {
        let substitution = match &node.inst {
            Inst::Select {
                ty: Ty::U8 | Ty::U32 | Ty::U64,
                cond,
                then_val,
                else_val,
            } => {
                // Select reads already computed SSA values. Split only the
                // continuation; earlier loads/calls must still be traversed,
                // even when their value is in an unselected arm. Keep the
                // local-cell initialization obligations unchanged.
                let name = self.value_name(node.results[0]);
                let then_wp = wp
                    .predicate
                    .substitute(&HashMap::from([(name.clone(), self.value(*then_val))]));
                let else_wp = wp
                    .predicate
                    .substitute(&HashMap::from([(name, self.value(*else_val))]));
                let condition = self.value(*cond);
                wp.predicate = binary(
                    binary(condition.clone(), BinOp::Implies, then_wp),
                    BinOp::And,
                    binary(
                        PureExpr::UnOp(UnOp::Not, Arc::new(condition)),
                        BinOp::Implies,
                        else_wp,
                    ),
                );
                None
            }
            Inst::Call { callee, args } => {
                wp.predicate = self.call_wp(
                    *callee,
                    args,
                    node.results[0],
                    &wp.predicate,
                    remaining,
                    active_calls,
                )?;
                None
            }
            Inst::Alloca { .. } => {
                let cell = node.results[0];
                if wp.required_cells.contains(&cell) {
                    return Err(refuse("load may read an uninitialized local scalar cell"));
                }
                None
            }
            Inst::Load { ptr, .. } => {
                wp.required_cells.insert(*ptr);
                Some((
                    self.value_name(node.results[0]),
                    cell_expr(
                        *ptr,
                        match self.definitions[ptr] {
                            ValueKind::Cell(sort) => sort,
                            ValueKind::Scalar(_) => unreachable!("validated cell"),
                        },
                        &self.namespace,
                    ),
                ))
            }
            Inst::Store { ptr, value, .. } => {
                wp.required_cells.remove(ptr);
                Some((
                    format!("__trust_wp_{}cell{}", self.namespace, ptr.index()),
                    self.value(*value),
                ))
            }
            Inst::Assume { cond } => {
                // Stronger than the partial-correctness assumption rule:
                // prove the condition instead of gaining it as a premise.
                wp.predicate = binary(self.value(*cond), BinOp::And, wp.predicate);
                None
            }
            _ => {
                let (_, expression) = instruction_expression(&node.inst, &self.namespace)?;
                Some((
                    self.value_name(node.results[0]),
                    expression.ok_or_else(|| refuse("unexpected terminator"))?,
                ))
            }
        };
        if let Some((name, expression)) = substitution {
            wp.predicate = wp
                .predicate
                .substitute(&HashMap::from([(name, expression)]));
        }
        Ok(wp)
    }

    fn call_wp(
        &self,
        callee: FuncId,
        args: &[ValueId],
        result: ValueId,
        post: &PureExpr,
        remaining: &mut usize,
        active_calls: &mut BTreeSet<FuncId>,
    ) -> Result<PureExpr> {
        // Expand instructions, never an authored or purportedly proved
        // summary. The caller and callee keep disjoint SSA/result/cell names;
        // recursion is refused even when a call's result is unused.
        if active_calls.len() >= 32 || !active_calls.insert(callee) {
            return Err(refuse("recursive or excessively deep scalar call graph"));
        }
        let function = self
            .module
            .function_by_id(callee)
            .ok_or_else(|| refuse("missing local callee"))?;
        let body = Self::validate(
            self.module,
            function,
            format!("callee_f{}_", callee.index()),
        )?;
        let continuation = post.substitute(&HashMap::from([(
            self.value_name(result),
            result_expr(body.result_sort, &body.namespace),
        )]));
        let wp = body.wp(
            function.entry,
            &continuation,
            &mut BTreeSet::new(),
            remaining,
            active_calls,
        )?;
        active_calls.remove(&callee);
        if !wp.required_cells.is_empty() {
            return Err(refuse(
                "callee load may read an uninitialized local scalar cell",
            ));
        }
        let substitutions: HashMap<_, _> = body
            .entry
            .params
            .iter()
            .zip(args)
            .map(|((formal, _), actual)| (body.value_name(*formal), self.value(*actual)))
            .collect();
        let predicate = wp.predicate.substitute(&substitutions);
        // No local identity or result placeholder can escape composition.
        // The only remaining reads are the caller's continuation and actuals.
        let mut allowed: BTreeSet<_> = post.free_vars().into_iter().collect();
        allowed.remove(&self.value_name(result));
        for argument in args {
            allowed.insert(self.value_name(*argument));
        }
        if predicate
            .free_vars()
            .iter()
            .any(|name| !allowed.contains(name))
        {
            return Err(refuse("composed callee WP retains an unbound local value"));
        }
        Ok(predicate)
    }
}

fn instruction_expression(
    inst: &Inst,
    namespace: &str,
) -> Result<(Vec<ValueId>, Option<PureExpr>)> {
    Ok(match inst {
        Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(value),
        } => (vec![], Some(PureExpr::Bool(*value))),
        Inst::Const {
            ty,
            value: Constant::Int(value),
        } if matches!(ty, Ty::U8 | Ty::U32 | Ty::U64) => {
            let bits = ScalarSort::from_ty(ty)
                .and_then(ScalarSort::unsigned_bits)
                .ok_or_else(|| refuse("unsupported unsigned constant"))?;
            let value =
                u64::try_from(*value).map_err(|_| refuse("unsigned constant is out of range"))?;
            if bits < 64 && value >= (1_u64 << bits) {
                return Err(refuse("unsigned constant is out of range"));
            }
            (
                vec![],
                Some(trust_wp_core::formula::int_bounds::unsigned_literal_expr(
                    value,
                )),
            )
        }
        Inst::Copy { ty, operand } => {
            let sort = ScalarSort::from_ty(ty).ok_or_else(|| refuse("unsupported copy type"))?;
            (vec![*operand], Some(value_expr(*operand, sort, namespace)))
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            let sort =
                ScalarSort::from_ty(ty).ok_or_else(|| refuse("unsupported comparison type"))?;
            let op = match (sort, op) {
                (_, trust_ir::ICmpOp::Eq) => BinOp::Eq,
                (_, trust_ir::ICmpOp::Ne) => BinOp::Ne,
                (
                    ScalarSort::Unsigned8 | ScalarSort::Unsigned32 | ScalarSort::Unsigned64,
                    trust_ir::ICmpOp::Ult,
                ) => BinOp::Lt,
                (
                    ScalarSort::Unsigned8 | ScalarSort::Unsigned32 | ScalarSort::Unsigned64,
                    trust_ir::ICmpOp::Ule,
                ) => BinOp::Le,
                (
                    ScalarSort::Unsigned8 | ScalarSort::Unsigned32 | ScalarSort::Unsigned64,
                    trust_ir::ICmpOp::Ugt,
                ) => BinOp::Gt,
                (
                    ScalarSort::Unsigned8 | ScalarSort::Unsigned32 | ScalarSort::Unsigned64,
                    trust_ir::ICmpOp::Uge,
                ) => BinOp::Ge,
                _ => return Err(refuse("comparison outside unsigned/Boolean fragment")),
            };
            (
                vec![*lhs, *rhs],
                Some(binary(
                    value_expr(*lhs, sort, namespace),
                    op,
                    value_expr(*rhs, sort, namespace),
                )),
            )
        }
        Inst::Select {
            ty: Ty::Bool,
            cond,
            then_val,
            else_val,
        } => (
            vec![*cond, *then_val, *else_val],
            Some(PureExpr::Ite(
                Arc::new(value_expr(*cond, ScalarSort::Boolean, namespace)),
                Arc::new(value_expr(*then_val, ScalarSort::Boolean, namespace)),
                Arc::new(value_expr(*else_val, ScalarSort::Boolean, namespace)),
            )),
        ),
        _ => {
            return Err(refuse(format!(
                "instruction outside scalar WP expression fragment: {inst:?}"
            )));
        }
    })
}
