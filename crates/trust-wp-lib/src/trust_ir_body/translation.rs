//! Diagnostic translation data, regenerated from the original native input.
//! Neither an equal witness nor a mechanized-fragment label is proof authority.

use serde::{Deserialize, Serialize};
use trust_ir::{
    BlockId, FuncId, Function, Inst, InstrNode, NativeRequestId, NativeVerificationBundle,
    NativeVerificationRequest, ProofDigest, ProofFormula, ProofId, TrustWpNativeRequest, Ty,
    ValueId,
};

use super::{Result, TrustIrBodyContractError, VerifyBundleRequest};

/// A finite traversal of the actual typed instructions. Successors are in the
/// original branch order; each node retains its exact block and position.
/// A semantic checker must also match each node at the actual program counter.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct NativeBodyWpProofPlan {
    pub block: BlockId,
    pub position: usize,
    pub instruction: InstrNode,
    pub successors: Vec<NativeBodyWpProofPlan>,
}

/// Supported scalar proof-plan fragments over the existing SemR instructions.
/// Other native-WP capabilities remain available and explicitly untranslated.
/// This is a body census, not acceptance of contract reification or a proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum NativeBodyWpTranslationCoverage {
    BooleanAssignmentCfg,
    UnsignedAssignmentCfg,
    Untranslated { reasons: Vec<String> },
}

/// Exact original inputs and emitted question, without a proof or verdict.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct NativeBodyWpTranslationWitness {
    pub native_bundle_digest: ProofDigest,
    pub module_digest: ProofDigest,
    pub native_request_digest: ProofDigest,
    pub request: NativeRequestId,
    pub function: FuncId,
    pub function_body_digest: ProofDigest,
    pub contracts: Vec<(ProofId, ProofFormula)>,
    pub derived_request: VerifyBundleRequest,
    /// Entry values and their emitted names, from the existing WP binder.
    pub parameters: Vec<(ValueId, String)>,
    pub plan: NativeBodyWpProofPlan,
    pub coverage: NativeBodyWpTranslationCoverage,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub public_question: Option<NativeBodyWpEntryWitness>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct NativeBodyWpEntryWitness {
    pub digest: String,
    pub uses_declared_entry: bool,
    pub contracts: Vec<(FuncId, ProofId, ProofFormula)>,
}

impl NativeBodyWpTranslationWitness {
    pub(super) fn new(
        bundle: &NativeVerificationBundle,
        native: &TrustWpNativeRequest,
        function: &Function,
        derived_request: VerifyBundleRequest,
        parameters: Vec<(ValueId, String)>,
        plan: NativeBodyWpProofPlan,
    ) -> Result<Self> {
        let contracts = native
            .obligations
            .iter()
            .map(|id| {
                let formula = bundle
                    .module
                    .proof_obligations
                    .iter()
                    .find(|row| row.id == *id)
                    .and_then(|row| row.formula.clone())
                    .ok_or_else(|| super::refuse("missing original translation contract"))?;
                Ok((*id, formula))
            })
            .collect::<Result<Vec<_>>>()?;
        let mut reasons = Vec::new();
        let signature = &bundle.module.func_types[function.ty.index() as usize];
        if signature
            .params
            .iter()
            .chain(&signature.returns)
            .any(|ty| !matches!(ty, Ty::Bool | Ty::U8 | Ty::U32 | Ty::U64))
        {
            reasons.push("unsupported scalar signature".into());
        }
        let mut unsigned = signature
            .params
            .iter()
            .chain(&signature.returns)
            .any(|ty| matches!(ty, Ty::U8 | Ty::U32 | Ty::U64));
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            unsigned |= matches!(
                node.inst,
                Inst::Const {
                    ty: Ty::U8 | Ty::U32 | Ty::U64,
                    ..
                } | Inst::Copy {
                    ty: Ty::U8 | Ty::U32 | Ty::U64,
                    ..
                } | Inst::Select {
                    ty: Ty::U8 | Ty::U32 | Ty::U64,
                    ..
                } | Inst::ICmp {
                    ty: Ty::U8 | Ty::U32 | Ty::U64,
                    ..
                }
            );
            if !matches!(
                node.inst,
                Inst::Const {
                    ty: Ty::Bool | Ty::U8 | Ty::U32 | Ty::U64,
                    ..
                } | Inst::Copy {
                    ty: Ty::Bool | Ty::U8 | Ty::U32 | Ty::U64,
                    ..
                } | Inst::Select {
                    ty: Ty::Bool | Ty::U8 | Ty::U32 | Ty::U64,
                    ..
                } | Inst::ICmp {
                    op: trust_ir::ICmpOp::Eq,
                    ty: Ty::U8 | Ty::U32 | Ty::U64,
                    ..
                } | Inst::Br { .. }
                    | Inst::CondBr { .. }
                    | Inst::Return { .. }
            ) {
                let reason = format!("untranslated instruction: {:?}", node.inst.shape());
                if !reasons.contains(&reason) {
                    reasons.push(reason);
                }
            }
        }
        Ok(Self {
            native_bundle_digest: bundle.stable_digest(),
            module_digest: bundle.module.stable_digest(),
            native_request_digest: NativeVerificationRequest::TrustWp(native.clone())
                .stable_digest(),
            request: native.id,
            function: function.id,
            function_body_digest: bundle
                .module
                .function_body_digest(function.id)
                .map_err(super::refuse)?,
            contracts,
            derived_request,
            parameters,
            plan,
            coverage: if reasons.is_empty() && unsigned {
                NativeBodyWpTranslationCoverage::UnsignedAssignmentCfg
            } else if reasons.is_empty() {
                NativeBodyWpTranslationCoverage::BooleanAssignmentCfg
            } else {
                NativeBodyWpTranslationCoverage::Untranslated { reasons }
            },
            public_question: None,
        })
    }
}

/// Regenerate all data using the same body derivation as verification/replay.
/// This checks correspondence only; it never accepts a translation theorem or
/// solver result, and an untranslated witness does not reduce engine coverage.
pub fn replay_trust_ir_body_translation_witnesses(
    bundle: &NativeVerificationBundle,
    witnesses: &[NativeBodyWpTranslationWitness],
) -> Result<()> {
    let expected = super::trust_ir_native_bundle_to_body_translation_witnesses(bundle)?;
    if expected != witnesses {
        return Err(TrustIrBodyContractError::Replay(
            "native body translation witness differs from the original input/derivation".into(),
        ));
    }
    Ok(())
}
