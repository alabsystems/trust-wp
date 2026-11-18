//! Explicit scheduling over the complete admitted input, through the shared
//! native conversion, body derivation and evidence replay owners.
use super::*;

/// The actual question and result from one canonical derivation/verification.
/// Private fields prevent replacement of only one side; this is producer data,
/// never a mathematical certificate or source/emission authority.
#[derive(Debug, Clone, PartialEq)]
pub struct NativeBodyWpVerification {
    witness: NativeBodyWpTranslationWitness,
    result: VerifyBundleResult,
    public_question_digest: Option<String>,
    uses_declared_entry: bool,
}

impl NativeBodyWpVerification {
    pub fn witness(&self) -> &NativeBodyWpTranslationWitness {
        &self.witness
    }
    pub fn result(&self) -> &VerifyBundleResult {
        &self.result
    }
    pub fn public_question_digest(&self) -> Option<&str> {
        self.public_question_digest.as_deref()
    }
    pub fn uses_declared_entry(&self) -> bool {
        self.uses_declared_entry
    }
    pub(super) fn with_public_question(
        mut self,
        digest: String,
        uses_declared_entry: bool,
    ) -> Self {
        self.public_question_digest = Some(digest);
        self.uses_declared_entry = uses_declared_entry;
        self
    }
}

/// Verify one original single-proof WP request without projecting the native
/// bundle. Unselected siblings stay in its input identity and structural
/// admission, but do not acquire selected WP mode/body compatibility duties.
pub fn verify_trust_ir_body_request_validated(
    admitted: &trust_ir::ValidatedNativeBundle<'_>,
    request_id: trust_ir::NativeRequestId,
) -> Result<NativeBodyWpVerification> {
    let (request, witness) = derive_selected(admitted, request_id, true)?;
    let witness = witness.ok_or_else(|| refuse("selected translation has no witness"))?;
    verify_derived_request(request, witness)
}

pub(super) fn verify_derived_request(
    request: VerifyBundleRequest,
    witness: NativeBodyWpTranslationWitness,
) -> Result<NativeBodyWpVerification> {
    let result = verify_bundle(request);
    require_native_body_evidence(&result)?;
    Ok(NativeBodyWpVerification {
        witness,
        result,
        public_question_digest: None,
        uses_declared_entry: false,
    })
}

/// Independently regenerate the selected question against the entire admitted
/// input, then replay its output evidence. Optional witness data must match the
/// complete canonical derivation; absence supplies no translation witness.
pub fn replay_trust_ir_body_request_validated(
    admitted: &trust_ir::ValidatedNativeBundle<'_>,
    request_id: trust_ir::NativeRequestId,
    result: &VerifyBundleResult,
    witness: Option<&NativeBodyWpTranslationWitness>,
) -> Result<()> {
    let (request, regenerated) = derive_selected(admitted, request_id, witness.is_some())?;
    if let Some(witness) = witness {
        if regenerated.as_ref() != Some(witness) {
            return Err(TrustIrBodyContractError::Replay(
                "selected translation differs from the complete original input/derivation".into(),
            ));
        }
    }
    replay_body_requests(std::slice::from_ref(&request), std::slice::from_ref(result))
}

fn derive_selected(
    admitted: &trust_ir::ValidatedNativeBundle<'_>,
    request_id: trust_ir::NativeRequestId,
    capture: bool,
) -> Result<(VerifyBundleRequest, Option<NativeBodyWpTranslationWitness>)> {
    derive_selected_with_domain(admitted, request_id, capture, None)
}

pub(super) fn derive_selected_with_domain(
    admitted: &trust_ir::ValidatedNativeBundle<'_>,
    request_id: trust_ir::NativeRequestId,
    capture: bool,
    entry_domain: Option<&EntryDomain>,
) -> Result<(VerifyBundleRequest, Option<NativeBodyWpTranslationWitness>)> {
    let bundle = admitted.bundle();
    let input_identity = bundle.stable_digest();
    validate_body_module_semantics(bundle)?;
    let selected = bundle
        .requests
        .iter()
        .find_map(|request| match request {
            trust_ir::NativeVerificationRequest::TrustWp(request) if request.id == request_id => {
                Some(request)
            }
            _ => None,
        })
        .ok_or(TrustIrNativeBundleError::SelectedRequestNotTrustWp {
            request_id: request_id.index(),
        })?;
    let [proof_id] = selected.obligations.as_slice() else {
        return Err(refuse(
            "selected body request must retain exactly one original proof",
        ));
    };
    let proof = bundle
        .module
        .proof_obligations
        .iter()
        .find(|proof| proof.id == *proof_id)
        .ok_or_else(|| refuse("selected body request has no original proof"))?;
    if proof
        .formula
        .as_ref()
        .is_some_and(|formula| formula.payload.len() > MAX_FORMULA_BYTES)
    {
        return Err(refuse("contract exceeds payload budget"));
    }
    let (native, mut request) = body_native_request_validated(admitted, request_id)?;
    let mut witnesses = Vec::new();
    derive_body_request(
        bundle,
        native,
        &mut request,
        input_identity,
        capture.then_some(&mut witnesses),
        entry_domain,
    )?;
    Ok((request, witnesses.pop()))
}
