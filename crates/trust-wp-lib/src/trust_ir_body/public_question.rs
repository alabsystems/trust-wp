//! Derive from the shared sealed original question, never local premise metadata.

use trust_verifier_api::native_public_question::{NativePublicProofScope, NativePublicQuestion};

use super::*;

/// Verify the selected original request in the shared question's explicit
/// derivation scope. This is native deductive producer data, not certification.
pub fn verify_native_public_question(
    question: &NativePublicQuestion<'_>,
    request_id: trust_ir::NativeRequestId,
) -> Result<NativeBodyWpVerification> {
    let domain = entry_domain(question, request_id)?;
    let admitted =
        trust_ir::ValidatedNativeBundle::new(question.native_bundle()).map_err(|errors| {
            TrustIrNativeBundleError::InvalidNativeBundle {
                errors: errors.into_iter().map(|error| error.to_string()).collect(),
            }
        })?;
    let (request, witness) = selected::derive_selected_with_domain(
        &admitted,
        request_id,
        true,
        (domain.conditioned || !domain.clauses.is_empty()).then_some(&domain),
    )?;
    Ok(selected::verify_derived_request(
        request,
        witness.ok_or_else(|| refuse("public question translation has no witness"))?,
    )?
    .with_public_question(domain.digest, domain.conditioned))
}

/// Independently regenerate program semantics, all consumed entry bindings and
/// the exact derivation scope before replaying any supplied result or witness.
pub fn replay_native_public_question(
    question: &NativePublicQuestion<'_>,
    request_id: trust_ir::NativeRequestId,
    result: &VerifyBundleResult,
    witness: Option<&NativeBodyWpTranslationWitness>,
    artifact_question_digest: &str,
) -> Result<()> {
    if artifact_question_digest != question.digest_sha256() {
        return Err(TrustIrBodyContractError::Replay(
            "artifact belongs to a different original public question".into(),
        ));
    }
    let domain = entry_domain(question, request_id)?;
    let admitted =
        trust_ir::ValidatedNativeBundle::new(question.native_bundle()).map_err(|errors| {
            TrustIrNativeBundleError::InvalidNativeBundle {
                errors: errors.into_iter().map(|error| error.to_string()).collect(),
            }
        })?;
    let (request, regenerated) = selected::derive_selected_with_domain(
        &admitted,
        request_id,
        witness.is_some(),
        (domain.conditioned || !domain.clauses.is_empty()).then_some(&domain),
    )?;
    if let Some(witness) = witness {
        if regenerated.as_ref() != Some(witness) {
            return Err(TrustIrBodyContractError::Replay(
                "public question identity, scope or original derivation differs".into(),
            ));
        }
    }
    replay_body_requests(std::slice::from_ref(&request), std::slice::from_ref(result))
}

fn entry_domain(
    question: &NativePublicQuestion<'_>,
    request_id: trust_ir::NativeRequestId,
) -> Result<EntryDomain> {
    let native = question.native_bundle();
    let request = native
        .requests
        .iter()
        .find_map(|request| match request {
            trust_ir::NativeVerificationRequest::TrustWp(request) if request.id == request_id => {
                Some(request)
            }
            _ => None,
        })
        .ok_or_else(|| refuse("public question does not select an original WP request"))?;
    if request.function != question.function() || request.obligations != [question.proof_id()] {
        return Err(refuse(
            "WP request differs from the original public question function/proof",
        ));
    }
    // Options, provenance, replay context and every sibling remain the exact
    // original values. Canonical conversion and semantic validation below
    // retain their normal admission/refusal duties for this selected request.
    let mut clauses = BTreeMap::new();
    for function in &native.module.functions {
        let originals: Vec<_> = question
            .entry_preconditions(function.id)
            .map(|entry| entry.proof().clone())
            .collect();
        if !originals.is_empty() {
            // The existing canonical semantic validator still checks the
            // complete module. The scalar binder runs when root/callee WP
            // actually consumes an entry, rather than narrowing unrelated
            // original functions to this engine's scalar fragment.
            clauses.insert(function.id, originals);
        }
    }
    Ok(EntryDomain {
        clauses,
        digest: question.digest_sha256().into(),
        request_id,
        conditioned: question.proof_scope() == NativePublicProofScope::DeclaredEntry,
    })
}
