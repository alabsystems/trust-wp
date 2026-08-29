// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::UnknownReason as AyUnknownReason;
use trust_wp_ay::UnknownReason;

#[test]
fn ay_self_check_rejection_stays_distinct_from_proof_trust() {
    let mapped = UnknownReason::from_ay_unknown_reason(&AyUnknownReason::SelfCheckRejected);

    assert_eq!(mapped, UnknownReason::SelfCheckRejected);
    assert_ne!(mapped, UnknownReason::ProofTrusted);
    assert_eq!(mapped.as_str(), "self-check-rejected");
}

#[test]
fn ay_proof_trust_stays_non_retryable_solver_message() {
    let reason = AyUnknownReason::ProofTrusted;
    let mapped = UnknownReason::from_ay_unknown_reason(&reason);

    assert_eq!(mapped, UnknownReason::SolverMessage(reason.to_string()));
    assert_ne!(mapped, UnknownReason::ProofTrusted);
}
