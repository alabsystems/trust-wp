// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// Tests for LoopVerificationResult helper methods (Part of #81)

/// Create a dummy counterexample for testing
pub(super) fn dummy_cex() -> Counterexample {
    Counterexample {
        values: vec![],
        violated_postcondition: None,
    }
}

/// Create a counterexample with a specific int marker value for identification
pub(super) fn cex_with_marker(marker: i64) -> Counterexample {
    Counterexample {
        values: vec![CounterexampleValue {
            name: "__marker".to_string(),
            value: CounterexampleType::Int(marker.into()),
            origin: None,
        }],
        violated_postcondition: None,
    }
}

#[test]
#[timeout(30000)]
fn test_loop_verification_result_all_verified_true() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        result.all_verified(),
        "all verified without variants should pass: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_loop_verification_result_all_verified_false_init() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Failed(dummy_cex()),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        !result.all_verified(),
        "failed initialization should cause all_verified=false: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_loop_verification_result_all_verified_false_preservation() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Unknown(UnknownReason::Unspecified),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        !result.all_verified(),
        "unknown preservation should cause all_verified=false: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_loop_verification_result_all_verified_false_postcondition() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Failed(dummy_cex()),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        !result.all_verified(),
        "failed postcondition should cause all_verified=false: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_loop_verification_result_overall_verified() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Verified(None),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        matches!(result.overall(), VerificationResult::Verified(_)),
        "all Verified fields should yield overall Verified, got {:?}",
        result.overall()
    );
}

#[test]
#[timeout(30000)]
fn test_loop_verification_result_overall_unknown() {
    let result = LoopVerificationResult {
        initialization: VerificationResult::Verified(None),
        preservation: VerificationResult::Unknown(UnknownReason::Unspecified),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        matches!(
            result.overall(),
            VerificationResult::Unknown(UnknownReason::Unspecified)
        ),
        "one Unknown preservation should yield overall Unknown, got {:?}",
        result.overall()
    );
}

#[test]
#[timeout(30000)]
fn test_loop_verification_result_overall_failed_priority() {
    // Failed takes priority over Unknown
    let result = LoopVerificationResult {
        initialization: VerificationResult::Unknown(UnknownReason::Unspecified),
        preservation: VerificationResult::Failed(dummy_cex()),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    assert!(
        matches!(result.overall(), VerificationResult::Failed(_)),
        "Failed should take priority over Unknown"
    );
}

#[test]
#[timeout(30000)]
fn test_loop_verification_result_overall_failed_first() {
    // First Failed is returned (initialization before preservation)
    // Use markers to identify which counterexample we get back
    let result = LoopVerificationResult {
        initialization: VerificationResult::Failed(cex_with_marker(1)),
        preservation: VerificationResult::Failed(cex_with_marker(2)),
        postcondition: VerificationResult::Verified(None),
        variant_nonneg: None,
        variant_decrease: None,
    };
    match result.overall() {
        VerificationResult::Failed(cex) => {
            // Should get init's counterexample (marker=1), not preservation's (marker=2)
            let marker = cex
                .int_assignments()
                .find(|(name, _)| *name == "__marker")
                .map(|(_, v)| v);
            assert_eq!(
                marker,
                Some(1),
                "overall() should return init's counterexample (marker=1), not preservation's"
            );
        }
        other => panic!("Expected Failed result, got {other:?}"),
    }
}

// Tests for Counterexample setter methods (Part of #82)

#[test]
#[timeout(30000)]
fn test_counterexample_set_origin() {
    // Create a counterexample with a value
    let mut cex = Counterexample {
        values: vec![CounterexampleValue {
            name: "x".to_string(),
            value: CounterexampleType::Int(42.into()),
            origin: None,
        }],
        violated_postcondition: None,
    };

    // Set origin
    let origin = VarOrigin::Parameter {
        name: "x".to_string(),
        span: None,
    };
    cex.set_origin("x", origin.clone());

    // Verify origin was set
    match &cex.values[0].origin {
        Some(VarOrigin::Parameter { name, .. }) => {
            assert_eq!(name, "x", "origin parameter name should be 'x'");
        }
        other => panic!("Expected Parameter origin for 'x', got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn test_counterexample_set_origin_overwrite() {
    // Create a counterexample with a value that has an origin
    let mut cex = Counterexample {
        values: vec![CounterexampleValue {
            name: "x".to_string(),
            value: CounterexampleType::Int(42.into()),
            origin: Some(VarOrigin::Parameter {
                name: "x".to_string(),
                span: None,
            }),
        }],
        violated_postcondition: None,
    };

    // Overwrite with a different origin
    let new_origin = VarOrigin::Precondition {
        contract_idx: 0,
        span: None,
    };
    cex.set_origin("x", new_origin);

    // Verify origin was overwritten
    match &cex.values[0].origin {
        Some(VarOrigin::Precondition { contract_idx, .. }) => {
            assert_eq!(*contract_idx, 0, "overwritten contract_idx should be 0");
        }
        other => panic!("Expected Precondition origin, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn test_counterexample_set_origin_nonexistent_var() {
    // Set origin for a variable that doesn't exist in values
    let mut cex = Counterexample {
        values: vec![CounterexampleValue {
            name: "x".to_string(),
            value: CounterexampleType::Int(42.into()),
            origin: None,
        }],
        violated_postcondition: None,
    };

    // Try to set origin for nonexistent "y"
    let origin = VarOrigin::Parameter {
        name: "y".to_string(),
        span: None,
    };
    cex.set_origin("y", origin);

    // Original "x" should still have no origin
    assert!(
        cex.values[0].origin.is_none(),
        "setting origin for nonexistent 'y' should not affect 'x', got: {:?}",
        cex.values[0].origin
    );
}

#[test]
#[timeout(30000)]
fn test_counterexample_set_violated_postcondition() {
    let mut cex = dummy_cex();

    let info = PostconditionInfo {
        clause_idx: 0,
        contract_text: "result > x".to_string(),
        span: None,
    };
    cex.set_violated_postcondition(info);

    let post = cex
        .violated_postcondition
        .expect("violated_postcondition should be set after set_violated_postcondition()");
    assert_eq!(
        post.clause_idx, 0,
        "violated postcondition clause_idx should be 0"
    );
    assert_eq!(
        post.contract_text, "result > x",
        "violated postcondition text should match"
    );
}

// NOTE: test_counterexample_violated_postcondition_in_display omitted
// Counterexample does not implement Display trait.
// The violated_postcondition field is used by callers (e.g., error reporters)
// directly rather than through Display.
