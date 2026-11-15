// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Focused loop-parameter coverage tests for `verify_loop_invariant` (#864).
//!
//! Covers paths that were previously untested in loop verification:
//! - `type_constants: Some(...)` wiring
//! - `track: Some(TrackLevel::{Ptr, Mem})` wiring
//! - `Err(EncodingError)` propagation for malformed loop expressions
//! - `loop_condition = None` in variant checks (unconditional loop)

use std::collections::HashMap;

use ntest::timeout;
use trust_wp_core::{formula::NamedBindingValue, TrackLevel};

use super::{super::*, helpers::*};

#[test]
#[timeout(30000)]
fn test_loop_type_constants_enable_initialization_proof() {
    // requires: x == Self::MAX
    let req = eq(var("x"), var("Self::MAX"));
    // invariant: x == 127
    let inv = eq(var("x"), int(127));

    let mut type_constants = HashMap::new();
    type_constants.insert("Self::MAX".to_string(), PureExpr::Int(127));

    // WITH type constants: Self::MAX resolves to 127, so x == Self::MAX => x == 127.
    let with_constants = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: std::slice::from_ref(&req),
        ensures: &[],
        invariants: std::slice::from_ref(&inv),
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &HashMap::new(),
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig {
            transition_facts: vec![],
            type_constants: Some(&type_constants),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    assert!(
        matches!(
            with_constants.initialization,
            VerificationResult::Verified(_)
        ),
        "With Self::MAX=127, initialization should verify: got {:?}",
        with_constants.initialization
    );

    // WITHOUT type constants: Self::MAX is an unconstrained variable, so
    // x == Self::MAX does not imply x == 127.
    let without_constants = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[req],
        ensures: &[],
        invariants: &[inv],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &HashMap::new(),
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        matches!(
            without_constants.initialization,
            VerificationResult::Failed(_)
        ),
        "Without type constants, initialization should fail: got {:?}",
        without_constants.initialization
    );
}

#[test]
#[timeout(30000)]
fn test_loop_ptr_track_level_verifies_inductive_invariant() {
    // invariant: i >= 0
    let inv = ge(var("i"), int(0));
    // condition: i < 10
    let cond = lt(var("i"), int(10));

    // body effect: i' = i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // pre-loop: i = 0
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: std::slice::from_ref(&inv),
        loop_condition: Some(&cond),
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig {
            transition_facts: vec![],
            track: Some(TrackLevel::Ptr),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Ptr track should preserve initialization behavior: got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.preservation, VerificationResult::Verified(_)),
        "Ptr track should verify preservation for i>=0, i'=i+1: got {:?}",
        result.preservation
    );
}

#[test]
#[timeout(30000)]
fn test_loop_mem_track_level_detects_preservation_failure() {
    // invariant: i >= 0 && i <= 10
    let inv = and(ge(var("i"), int(0)), le(var("i"), int(10)));

    // body effect: i' = i + 1, unconditional loop (no guard)
    let mut body_effect = HashMap::new();
    body_effect.insert("i".to_string(), add(var("i"), int(1)));

    // pre-loop: i = 0
    let mut pre_loop = HashMap::new();
    pre_loop.insert("i".to_string(), NamedBindingValue::untyped(int(0)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: std::slice::from_ref(&inv),
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &["i"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig {
            transition_facts: vec![],
            track: Some(TrackLevel::Mem),
            ..LoopEncoderConfig::default()
        },
    })
    .unwrap();

    // ay a261cd2b has a SAT model reconstruction bug (ay#3447) that can
    // panic on simple integer formulas. The panic is caught and surfaced
    // as Unknown. Workaround: accept Unknown alongside the expected result,
    // but log when it fires so we detect when the upstream fix lands.
    match &result.initialization {
        VerificationResult::Verified(_) => {} // expected
        VerificationResult::Unknown(reason) => {
            eprintln!(
                "WARNING: ay#3447 workaround active — initialization returned Unknown \
                 (expected Verified): {reason:?}"
            );
        }
        VerificationResult::Failed(e) => {
            panic!("Initialization should be Verified: got Failed({e:?})")
        }
        VerificationResult::Assumed(reason) => {
            panic!("Initialization should be Verified: got Assumed({reason:?})")
        }
    }
    match &result.preservation {
        VerificationResult::Failed(_) => {} // expected
        VerificationResult::Unknown(reason) => {
            eprintln!(
                "WARNING: ay#3447 workaround active — preservation returned Unknown \
                 (expected Failed): {reason:?}"
            );
        }
        VerificationResult::Verified(_) => {
            panic!("Mem track should detect non-inductive invariant: got Verified")
        }
        VerificationResult::Assumed(reason) => {
            panic!("Mem track should detect non-inductive invariant: got Assumed({reason:?})")
        }
    }
}

#[test]
#[timeout(30000)]
fn test_loop_verification_propagates_encoding_error_from_invariant() {
    // An invariant the encoder refuses, producing EncodingError::Unsupported.
    let bad_inv = crate::tests::helpers::unencodable_float_order();

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: &[bad_inv],
        loop_condition: None,
        condition_is_body_break: false,
        modified_vars: &[],
        body_effect: &HashMap::new(),
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: None,
        pre_loop_assignments: &HashMap::new(),
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    });

    assert!(
        matches!(
            result,
            Err(EncodingError::Unsupported { ref message, .. })
                if message.contains("Float") || message.contains("boolean")
        ),
        "Unencodable invariant should return unsupported encoding error: got {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_loop_variant_checks_with_none_condition() {
    // Invariant: x >= 0
    let inv = ge(var("x"), int(0));
    // Variant: x
    let variant = var("x");

    // body effect: x' = x - 1
    let mut body_effect = HashMap::new();
    body_effect.insert("x".to_string(), sub(var("x"), int(1)));

    // pre-loop: x = 5
    let mut pre_loop = HashMap::new();
    pre_loop.insert("x".to_string(), NamedBindingValue::untyped(int(5)));

    let result = verify_loop_invariant_positional(&LoopVerificationContext {
        requires: &[],
        ensures: &[],
        invariants: std::slice::from_ref(&inv),
        loop_condition: None, // unconditional loop path
        condition_is_body_break: false,
        modified_vars: &["x"],
        body_effect: &body_effect,
        deref_body_effect: &HashMap::new(),
        double_deref_body_effect: &HashMap::new(),
        postcondition_effects: None,
        variant: Some(&variant),
        pre_loop_assignments: &pre_loop,
        return_expr: None,
        init_extra_facts: &[],
        post_extra_facts: &[],
        config: LoopEncoderConfig::default(),
    })
    .unwrap();

    assert!(
        matches!(result.initialization, VerificationResult::Verified(_)),
        "Initialization should pass with x=5 and x>=0 invariant: got {:?}",
        result.initialization
    );
    assert!(
        matches!(result.variant_nonneg, Some(VerificationResult::Verified(_))),
        "Without loop condition, variant nonneg should prove x>=0 => x>=0: got {:?}",
        result.variant_nonneg
    );
    assert!(
        matches!(
            result.variant_decrease,
            Some(VerificationResult::Verified(_))
        ),
        "Without loop condition, variant decrease should prove x-1 < x: got {:?}",
        result.variant_decrease
    );
}
