// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`UnknownReason`] parsing, conversion, and display methods,
//! and [`VerificationResult`] accessor methods.
//!
//! Coverage gap: 4 methods on UnknownReason (from_solver_reason,
//! from_solver_reason_ref, as_str, to_option_string) and Display impl
//! with 9 variants × 4 methods = 36 code paths, zero tests.
//! VerificationResult accessors (unknown_reason, unknown_reason_str)
//! also untested.

use ntest::timeout;

use crate::verify::{UnknownReason, VerificationResult};

// --- UnknownReason::from_solver_reason (owned String) ---

#[test]
#[timeout(30000)]
fn from_solver_reason_none_gives_unspecified() {
    assert_eq!(
        UnknownReason::from_solver_reason(None),
        UnknownReason::Unspecified
    );
}

#[test]
#[timeout(30000)]
fn from_solver_reason_timeout() {
    assert_eq!(
        UnknownReason::from_solver_reason(Some("timeout".to_string())),
        UnknownReason::Timeout
    );
}

#[test]
#[timeout(30000)]
fn from_solver_reason_incomplete() {
    assert_eq!(
        UnknownReason::from_solver_reason(Some("incomplete".to_string())),
        UnknownReason::Incomplete
    );
}

#[test]
#[timeout(30000)]
fn from_solver_reason_quantifiers() {
    assert_eq!(
        UnknownReason::from_solver_reason(Some("quantifiers".to_string())),
        UnknownReason::Quantifiers
    );
}

#[test]
#[timeout(30000)]
fn from_solver_reason_sat() {
    assert_eq!(
        UnknownReason::from_solver_reason(Some("sat".to_string())),
        UnknownReason::SatModel
    );
}

#[test]
#[timeout(30000)]
fn from_solver_reason_memout() {
    assert_eq!(
        UnknownReason::from_solver_reason(Some("memout".to_string())),
        UnknownReason::MemoryOut
    );
}

#[test]
#[timeout(30000)]
fn from_solver_reason_unknown_string_becomes_solver_message() {
    let reason = UnknownReason::from_solver_reason(Some("canceled".to_string()));
    assert_eq!(reason, UnknownReason::SolverMessage("canceled".to_string()));
}

// --- UnknownReason::from_solver_reason_ref (borrowed &str) ---

#[test]
#[timeout(30000)]
fn from_solver_reason_ref_none_gives_unspecified() {
    assert_eq!(
        UnknownReason::from_solver_reason_ref(None),
        UnknownReason::Unspecified
    );
}

#[test]
#[timeout(30000)]
fn from_solver_reason_ref_timeout() {
    assert_eq!(
        UnknownReason::from_solver_reason_ref(Some("timeout")),
        UnknownReason::Timeout
    );
}

#[test]
#[timeout(30000)]
fn from_solver_reason_ref_incomplete() {
    assert_eq!(
        UnknownReason::from_solver_reason_ref(Some("incomplete")),
        UnknownReason::Incomplete
    );
}

#[test]
#[timeout(30000)]
fn from_solver_reason_ref_quantifiers() {
    assert_eq!(
        UnknownReason::from_solver_reason_ref(Some("quantifiers")),
        UnknownReason::Quantifiers
    );
}

#[test]
#[timeout(30000)]
fn from_solver_reason_ref_sat() {
    assert_eq!(
        UnknownReason::from_solver_reason_ref(Some("sat")),
        UnknownReason::SatModel
    );
}

#[test]
#[timeout(30000)]
fn from_solver_reason_ref_memout() {
    assert_eq!(
        UnknownReason::from_solver_reason_ref(Some("memout")),
        UnknownReason::MemoryOut
    );
}

#[test]
#[timeout(30000)]
fn from_solver_reason_ref_unknown_becomes_solver_message() {
    let reason = UnknownReason::from_solver_reason_ref(Some("resource-limit"));
    assert_eq!(
        reason,
        UnknownReason::SolverMessage("resource-limit".to_string())
    );
}

// --- UnknownReason::as_str round-trip ---

#[test]
#[timeout(30000)]
fn as_str_timeout() {
    assert_eq!(UnknownReason::Timeout.as_str(), "timeout");
}

#[test]
#[timeout(30000)]
fn as_str_incomplete() {
    assert_eq!(UnknownReason::Incomplete.as_str(), "incomplete");
}

#[test]
#[timeout(30000)]
fn as_str_quantifiers() {
    assert_eq!(UnknownReason::Quantifiers.as_str(), "quantifiers");
}

#[test]
#[timeout(30000)]
fn as_str_sat_model() {
    assert_eq!(UnknownReason::SatModel.as_str(), "sat");
}

#[test]
#[timeout(30000)]
fn as_str_memout() {
    assert_eq!(UnknownReason::MemoryOut.as_str(), "memout");
}

#[test]
#[timeout(30000)]
fn as_str_demoted() {
    assert_eq!(
        UnknownReason::Demoted("sort_fallback".to_string()).as_str(),
        "sort_fallback"
    );
}

#[test]
#[timeout(30000)]
fn as_str_solver_panic() {
    assert_eq!(
        UnknownReason::SolverPanic("BUG: mk_eq".to_string()).as_str(),
        "BUG: mk_eq"
    );
}

#[test]
#[timeout(30000)]
fn as_str_solver_message() {
    assert_eq!(
        UnknownReason::SolverMessage("custom msg".to_string()).as_str(),
        "custom msg"
    );
}

#[test]
#[timeout(30000)]
fn as_str_unspecified() {
    assert_eq!(UnknownReason::Unspecified.as_str(), "unknown");
}

// --- UnknownReason::to_option_string ---

#[test]
#[timeout(30000)]
fn to_option_string_unspecified_is_none() {
    assert_eq!(UnknownReason::Unspecified.to_option_string(), None);
}

#[test]
#[timeout(30000)]
fn to_option_string_timeout_is_some() {
    assert_eq!(
        UnknownReason::Timeout.to_option_string(),
        Some("timeout".to_string())
    );
}

#[test]
#[timeout(30000)]
fn to_option_string_demoted_preserves_detail() {
    assert_eq!(
        UnknownReason::Demoted("detail".to_string()).to_option_string(),
        Some("detail".to_string())
    );
}

// --- Quantifier-specific variants (#2639) ---

#[test]
#[timeout(30000)]
fn as_str_quantifier_round_limit() {
    assert_eq!(
        UnknownReason::QuantifierRoundLimit.as_str(),
        "quantifier-round-limit"
    );
}

#[test]
#[timeout(30000)]
fn as_str_quantifier_deferred() {
    assert_eq!(
        UnknownReason::QuantifierDeferred.as_str(),
        "quantifier-deferred"
    );
}

#[test]
#[timeout(30000)]
fn as_str_quantifier_unhandled() {
    assert_eq!(
        UnknownReason::QuantifierUnhandled.as_str(),
        "quantifier-unhandled"
    );
}

#[test]
#[timeout(30000)]
fn as_str_quantifier_cegqi_incomplete() {
    assert_eq!(
        UnknownReason::QuantifierCegqiIncomplete.as_str(),
        "quantifier-cegqi-incomplete"
    );
}

#[test]
#[timeout(30000)]
fn as_str_quantifier_ematching_exists_incomplete() {
    assert_eq!(
        UnknownReason::QuantifierEmatchingExistsIncomplete.as_str(),
        "quantifier-ematching-exists-incomplete"
    );
}

#[test]
#[timeout(30000)]
fn is_quantifier_true_for_all_quantifier_variants() {
    assert!(UnknownReason::Quantifiers.is_quantifier());
    assert!(UnknownReason::QuantifierRoundLimit.is_quantifier());
    assert!(UnknownReason::QuantifierDeferred.is_quantifier());
    assert!(UnknownReason::QuantifierUnhandled.is_quantifier());
    assert!(UnknownReason::QuantifierCegqiIncomplete.is_quantifier());
    assert!(UnknownReason::QuantifierEmatchingExistsIncomplete.is_quantifier());
}

#[test]
#[timeout(30000)]
fn is_quantifier_false_for_non_quantifier_variants() {
    assert!(!UnknownReason::Timeout.is_quantifier());
    assert!(!UnknownReason::Incomplete.is_quantifier());
    assert!(!UnknownReason::MemoryOut.is_quantifier());
    assert!(!UnknownReason::Unspecified.is_quantifier());
}

#[test]
#[timeout(30000)]
fn is_timeout_true_for_timeout() {
    assert!(UnknownReason::Timeout.is_timeout());
}

#[test]
#[timeout(30000)]
fn is_timeout_false_for_others() {
    assert!(!UnknownReason::Incomplete.is_timeout());
    assert!(!UnknownReason::QuantifierRoundLimit.is_timeout());
    assert!(!UnknownReason::Unspecified.is_timeout());
}

// --- from_ay_unknown_reason direct mapping (#2639) ---

#[test]
#[timeout(30000)]
fn from_ay_unknown_reason_timeout() {
    use ay_dpll::UnknownReason as AYReason;
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&AYReason::Timeout),
        UnknownReason::Timeout
    );
}

#[test]
#[timeout(30000)]
fn from_ay_unknown_reason_quantifier_round_limit() {
    use ay_dpll::UnknownReason as AYReason;
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&AYReason::QuantifierRoundLimit),
        UnknownReason::QuantifierRoundLimit
    );
}

#[test]
#[timeout(30000)]
fn from_ay_unknown_reason_quantifier_deferred() {
    use ay_dpll::UnknownReason as AYReason;
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&AYReason::QuantifierDeferred),
        UnknownReason::QuantifierDeferred
    );
}

#[test]
#[timeout(30000)]
fn from_ay_unknown_reason_incomplete() {
    use ay_dpll::UnknownReason as AYReason;
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&AYReason::Incomplete),
        UnknownReason::Incomplete
    );
}

#[test]
#[timeout(30000)]
fn from_ay_unknown_reason_memory_limit() {
    use ay_dpll::UnknownReason as AYReason;
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&AYReason::MemoryLimit),
        UnknownReason::MemoryOut
    );
}

#[test]
#[timeout(30000)]
fn from_ay_unknown_reason_internal_error() {
    use ay_dpll::UnknownReason as AYReason;
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&AYReason::InternalError),
        UnknownReason::InternalError
    );
}

#[test]
#[timeout(30000)]
fn from_ay_unknown_reason_unknown_gives_unspecified() {
    use ay_dpll::UnknownReason as AYReason;
    assert_eq!(
        UnknownReason::from_ay_unknown_reason(&AYReason::Unknown),
        UnknownReason::Unspecified
    );
}

// --- Display impl ---

#[test]
#[timeout(30000)]
fn display_matches_as_str() {
    let variants: Vec<UnknownReason> = vec![
        UnknownReason::Timeout,
        UnknownReason::Incomplete,
        UnknownReason::Quantifiers,
        UnknownReason::QuantifierRoundLimit,
        UnknownReason::QuantifierDeferred,
        UnknownReason::QuantifierUnhandled,
        UnknownReason::QuantifierCegqiIncomplete,
        UnknownReason::QuantifierEmatchingExistsIncomplete,
        UnknownReason::SatModel,
        UnknownReason::MemoryOut,
        UnknownReason::Demoted("d".to_string()),
        UnknownReason::SolverPanic("p".to_string()),
        UnknownReason::SolverMessage("m".to_string()),
        UnknownReason::Unspecified,
    ];
    for v in &variants {
        assert_eq!(
            format!("{v}"),
            v.as_str(),
            "Display should match as_str for {v:?}"
        );
    }
}

// --- from_solver_reason / as_str round-trip for known keywords ---

#[test]
#[timeout(30000)]
fn round_trip_known_keywords() {
    for keyword in &["timeout", "incomplete", "quantifiers", "sat", "memout"] {
        let reason = UnknownReason::from_solver_reason(Some(keyword.to_string()));
        assert_eq!(reason.as_str(), *keyword, "round-trip failed for {keyword}");
    }
}

// --- VerificationResult accessor methods ---

#[test]
#[timeout(30000)]
fn verification_result_unknown_reason_returns_some() {
    let result = VerificationResult::Unknown(UnknownReason::Timeout);
    assert!(result.unknown_reason().is_some());
    assert_eq!(*result.unknown_reason().unwrap(), UnknownReason::Timeout);
}

#[test]
#[timeout(30000)]
fn verification_result_unknown_reason_returns_none_for_verified() {
    assert!(VerificationResult::Verified(None)
        .unknown_reason()
        .is_none());
}

#[test]
#[timeout(30000)]
fn verification_result_unknown_reason_returns_none_for_assumed() {
    let result = VerificationResult::Assumed("axiom".to_string());
    assert!(result.unknown_reason().is_none());
}

#[test]
#[timeout(30000)]
fn verification_result_unknown_reason_str_returns_str() {
    let result = VerificationResult::Unknown(UnknownReason::Incomplete);
    assert_eq!(result.unknown_reason_str(), Some("incomplete"));
}

#[test]
#[timeout(30000)]
fn verification_result_unknown_reason_str_none_for_verified() {
    assert_eq!(
        VerificationResult::Verified(None).unknown_reason_str(),
        None
    );
}

#[test]
#[timeout(30000)]
fn verification_result_unknown_from_solver_convenience() {
    let result = VerificationResult::unknown_from_solver(Some("timeout".to_string()));
    match result {
        VerificationResult::Unknown(reason) => {
            assert_eq!(reason, UnknownReason::Timeout);
        }
        other => panic!("expected Unknown, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn verification_result_unknown_from_solver_none() {
    let result = VerificationResult::unknown_from_solver(None);
    match result {
        VerificationResult::Unknown(reason) => {
            assert_eq!(reason, UnknownReason::Unspecified);
        }
        other => panic!("expected Unknown(Unspecified), got {other:?}"),
    }
}
